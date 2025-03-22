use eyre::{eyre, Result};
use spdr_isa::{opcodes::{OpCode, CmpFlag}, program::Program, registers::{EQ, FIRST_FREE_REGISTER, LOOP, REG_COUNT}};
use crate::{errors::{ASMError, ErrorPrinter}, interner::{intern, lookup}, patch::Patch, src_file::SourceFile, symbol_table::{SymbolTable, Ty, VarDecl}, tokenizer::{Lexer, Span, Token, TokenKind}};
use std::{
  collections::HashMap, fmt::Debug, fs::read_to_string, io::{self, Write,}, path::Path
};


#[derive(Debug, Clone, Default, PartialEq,)]
enum CompilerPhase {
  #[default]
  FunctionCompilation,
  BinaryCompilation,
}

// TODO: Assembler should have different creation methods i.e. `load_from_str` and `load_from_file` new should just create a assembler instance also give it the option to not use a writer...
// Use the builder pattern for the assembler.
#[derive(Debug, Clone,)]
pub struct Assembler {
  phase:CompilerPhase,
  tokens:Vec<Token,>,
  cursor:usize,
  /// The [`Token`] the assembler is currently reading.
  current_instruction:Token,
  /// The Symbol Table for the current scope.
  table:SymbolTable,
  function_patches:HashMap<u32,Patch>,
  /// The first availible register the assembler can assign.
  open:u8,
  /// The body of the binary's "`main`" function.
  main:Program,
  source:SourceFile,
}
impl Assembler {
  // This is basically just used for tests
  #[cfg(test)]
  /// Create a new empty assembler without a file.
  pub fn new<W:Write>(src:&str, mut w:W) -> Self {
    let source = SourceFile::new_from_str(src);
    let tokens = Lexer::new(&source,).tokenize(&mut w);

    Self {
      phase:CompilerPhase::default(),
      current_instruction:tokens[0],
      tokens,
      cursor:0,
      table:SymbolTable::new(),
      function_patches:HashMap::new(),
      main:Program::new(),
      open:FIRST_FREE_REGISTER as u8,
      source
    }
  }

  #[cfg(test)]
  /// Returns a reference to the [`Assembler`]'s [`SymbolTable`].
  pub fn table(&self) -> &SymbolTable{
    &self.table
  }

  /// Returns the next [`Token`] in the `src`.
  fn next_token(&mut self,) -> Option<Token> {
    let token =  if self.cursor < self.tokens.len(){
      self.current_instruction = self.tokens[self.cursor];
      Some(self.tokens[self.cursor])
    }
    else{
      None
    };
    self.cursor += 1;
    token
  }

  fn peek(&self)-> Option<Token>{
    if self.cursor < self.tokens.len(){
      Some(self.tokens[self.cursor])
    }
    else{
      None
    }
  }

  /// Consume the next `n` [`Token`]s in the `src`.
  fn eat_tokens(&mut self, n:usize,) {
    for _ in 0..n {
      self.next_token();
    }
  }

  /// Reserves a register for use.
  fn reserve_reg(&mut self,) -> u8 {
    let reg = self.open;
    self.open += 1;
    reg
  }

  /// Adds an identifier to the [`Assembler`]'s Symbol Table as a
  /// [`Ty::Register`].
  fn add_as_reg(&mut self, ident:Token,) -> u8 {
    let ident = match ident {
      Token {
        kind: TokenKind::Identifier(ident,),
        ..
      } => ident,
      other => panic!("Tried to make a non identifier {}{} into a variable", other.kind, other.span.start),
    };

    // If the table already has the var it cannot be redeclared.
    match self.table.lookup(&ident){
      Some(decl) => match decl.ty {
        Ty::Register(reg) => reg,
        ty=> panic!("{} is already declared as a {}", lookup(ident), ty)
      },
      None => {
        let reg = self.reserve_reg();
        assert!(reg <= REG_COUNT as u8, "New register allocation strategy needed");

        self
          .table
          .add_symbol(ident, VarDecl::new(Ty::Register(reg,),),);
        reg
      },
    }
  }

  /// Read a `*.hd` file from the given path.
  pub fn read_header<P:AsRef<Path>,>(&mut self, src:P,) {
    // Load the header file and split them by lines
    let header = read_to_string(src,).unwrap();

    // Split the header into lines so each index corresponds to a function sig
    // TODO: Figure out if the header file should be tokenized
    for (idx, line,) in header.lines().enumerate() {
      // No need to parse the full signature just store the name as a key and the
      // idx of the func
    
      // Get the name of the function
      // Find the begining of the signature (which is the end of the name)
      let end = line.find("(",).unwrap();
      let name = line[2..end].trim();

      let sym = intern(name,);
      // Store the function in the symbol table
      self
        .table
        .add_symbol(sym, VarDecl::new(Ty::ExternalFunction(idx as u8,),),);
    }
  }

  /// Converts the `name` of a [`TokenKind::Identifier`] into a register
  /// address. Takes the current instruction and identifier location as
  /// arguments for error purposes.
  fn ident_to_reg(&self, name:u32, span:Span,) -> u8 {
    // Convert a variable declaration into a register
    // Error if the variable has not been declared
    let decl = match self.table.lookup(&name,) {
      Some(decl,) => decl,
      None => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::UndeclaredIdentifier{ ident: &lookup(name), span }),
    };

    match decl.ty {
      Ty::Register(idx,) => return idx as u8,
      other => {
        // TODO: This need to be an actual error
        panic!(
          "Invalid Target: {} only accepts registers as inputs. {other} is not a register.",
          self.current_instruction.kind
        )
      }
    }
  }

  /// Use when a function is `CALL`ed before it is defined. Creates a [`Patch`] for a [`TokenKind::Identifier`] 
  /// which records the [`Region`](defered_patch::Region) of a function pointer for later patching.
  fn create_function_pointer_patch(&mut self, name:&u32){
    // Patch in the function portion of the binary to overwrite with a concrete address.
    let addr_patch = self.function_patches.entry(*name).or_insert(Patch::new());

    // Reserve the region
    addr_patch.reserve_region(&mut self.main);
  }

  /// Return the next available address where a function can be stored.
  pub fn next_function_pointer(&self,) -> usize {
  // Add 4 to account for the displacement caused by the offset information at the
  // binary's beginning
  self.main.len() + 5
  }

  /// Give a concrete address to a function that was previously called without a definition. 
  fn fill_function_pointer_patch(&mut self, name:&u32, addr:usize){
    // Update the patch's PatchData
    self.function_patches.entry(*name).and_modify(|patch|patch.update_address(addr).unwrap());

    // Create an entry in the symbol table
    self.table.add_symbol(*name, VarDecl { ty:Ty::Function((addr as u32).to_le_bytes()) });
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Bool`] or
  /// [`TokenKind::Num`], return it as a `[u8;4]` array.
  fn next_token_as_immediate_array(&mut self,) -> [u8; 4] {
    match  self.next_token().unwrap() {
      Token {
        kind: TokenKind::Num(val,),
        ..
      } => val.to_le_bytes(),
      Token {
        kind: TokenKind::Bool(val,),
        ..
      } => (val as u32 as f32).to_le_bytes(),
      other => 
      ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::InvalidImmediateType{token:other}),
    }
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Register`] or a [`TokenKind::Identifier`], return
  /// it as a `u8`.
  fn next_token_as_register(&mut self,) -> u8 {
    match self.next_token().unwrap() {
      Token {
        kind: TokenKind::Register(idx,),
        ..
      } => idx,
      // If it's an identifier get the var decl, ensure it is a variable, then get the corresponding reg
      Token {
        kind: TokenKind::Identifier(name,),
        span,
        // Check the identifier is declared
      } => self.ident_to_reg(name, span,),
      // Anything other than an identigier should be an error
      other => panic!("{}", ASMError::NotRegisterOrIdent{token:other}),
    }
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Label`] or [`TokenKind::Num`] return it as a `u32`;
  fn next_token_as_jump_target(&mut self) -> [u8;4] {
    match self.next_token().unwrap(){
      Token { kind:TokenKind::Identifier(sym), span }  => {
        // Get the label the indentifier references
        let decl = self.table.lookup(&sym).unwrap();
        match decl.ty{
          Ty::Label(idx) => idx.to_le_bytes(),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::InvalidJumpTarget{ target:&other.to_string(), span }),
        }
      }
      // Rarely they use might use an actual number as the jump target (this should be discouraged)
      Token { kind:TokenKind::Num(num), .. } => (num as u32).to_le_bytes(),
      other => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::InvalidJumpTarget{ target:&other.kind.to_string(), span:other.span }),
    }
  }

  /// Compiles the .spdr file loaded into the assembler into a .spex executable
  /// file.
  pub fn compile(&mut self,) -> Program {
    // Compile only the functions and variables and store them at the beginning of the binary
    while let Some(token) = self.next_token() {
      match token.kind {
        TokenKind::Fn => self.compile_current_instruction(),
        _=> {},
      }
    }

    // Patch all the unassigned function addresses
    for (_, patch) in self.function_patches.iter(){
      patch.patch(&mut self.main);
    }
    
    // Get the len of the `lib` + 5 which is the offset of the `main`
    let offset = (self.main.len() as u32 + 5).to_le_bytes();
    self.main.push_front(vec![OpCode::Jmp.into(), offset[0], offset[1], offset[2], offset[3]]);

    // Reset the cursor so the tokens can be looped through again
    self.cursor = 0;
    // Switch the assembler phase
    self.phase = CompilerPhase::BinaryCompilation;

    // Compile `main` -- iterate over each instruction and interpret it as an opcode
    while let Some(instruction,) =  self.next_token() {
      // Compile while skipping function definitions
      match instruction.kind {
        // TODO: This here needs the functionality currently in eat_current_instruction
        TokenKind::Fn => 
        {
          // Eat the name
          self.eat_tokens(1,);
          // Eat the body
          self.eat_block();
        }
        // self.eat_current_instruction(),
        _ => self.compile_current_instruction(),
      }
    }
    
    self.main.push(OpCode::Hlt.into());

    return self.main.clone()
  }

  #[rustfmt::skip]
  /// Compile the next intruction in the program.
  fn compile_current_instruction(&mut self,) {
    let instruction = self.current_instruction;
    match instruction.kind {
      TokenKind::Load => {
        let reg = self.next_token_as_register();

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        self
          .main
          .extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Var => {
        // Add the next token to the symbol table assuming it is an ident
        let ident =  self.next_token().unwrap();
        let reg = self.add_as_reg(ident,);

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        self
          .main
          .extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Copy => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        self.main.extend_from_slice(&[OpCode::Copy.into(), dst, src,],)
      }
      TokenKind::Add 
      | TokenKind::Sub 
      | TokenKind::Mul 
      | TokenKind::Div 
      | TokenKind::Pow => self.compile_arithmetic_expr(),
      TokenKind::Not => {
        let dst = match  self.next_token().unwrap() {
          Token {
            kind: TokenKind::Register(reg,),
            ..
          } => reg,
          Token {
            kind: TokenKind::Identifier(name,),
            span,
          } => self.ident_to_reg(name, span,),
          _ => unreachable!("This needs to be a concrete error"),
        };

        match  self.next_token().unwrap() {
          Token {
            kind: TokenKind::Num(b,),
            ..
          } => {
            // If b is an immediate num perform the operation at compile time
            let b = b.to_le_bytes();
            self
              .main
              .extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Bool(b,),
            ..
          } => {
            // If b is an immediate bool perform the operation at compile time
            let b = (b as u32).to_le_bytes();
            self
              .main
              .extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Register(b,),
            ..
          } => {
            // If b is a register generate the not opcode
            self.main.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          Token {
            kind: TokenKind::Identifier(name,),
            span,
          } => {
            // If b is an identifier generate the not opcode
            let b = self.ident_to_reg(name, span,);
            self.main.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          _ => unreachable!(),
        }
      }
      TokenKind::Eq | TokenKind::Gt | TokenKind::Lt | TokenKind::Geq | TokenKind::Leq => {
        let op = self.current_instruction;
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_comparison(&op, &a, &b,);
      }
      TokenKind::Jmp => {
        let target = self.next_token_as_jump_target();
        self.main.extend_from_slice(&[OpCode::Jmp.into(), target[0], target[1], target[2], target[3],]);
      }
      TokenKind::Jz => {
        let check = self.next_token_as_register();
        let target = self.next_token_as_jump_target();
        self.main.extend_from_slice(&[OpCode::Jz.into(), check, target[0], target[1], target[2], target[3],]);
      }
      TokenKind::Jnz => {
        let check = self.next_token_as_register();
        let target = self.next_token_as_jump_target();
        self.main.extend_from_slice(&[OpCode::Jnz.into(), check, target[0], target[1], target[2], target[3],]);
      }
      TokenKind::Loop => self.compile_loop_expr(),
      TokenKind::While => self.compile_while_loop_expr(),
      TokenKind::For => self.compile_for_loop_expr(),
      TokenKind::If => self.compile_if_body_expr(),
      TokenKind::Else => {
        let next_operation = self.peek().unwrap();
        // If the "instruction" starts with a bracket, compile block should be called
        return match next_operation.kind {
          TokenKind::LCurlyBracket => self.compile_block(),
          // Doing nothing here will make it continue compiling the program which is what we want
          _ => {}
        };
      }
      TokenKind::Fn => {
        // Store the name in the symbol table        
        // Because of how interning works, "name" will be the order the identifier appeared in the source code. 
        // So an earlier defined function might have a later "name" if a function defined after it was called first
        match self.next_token().unwrap() {
          Token { kind:TokenKind::Identifier(name,) , span} => // Create a function declaration and store it in the symbol table
          match self.table.lookup(&name,) {
            // If the name is already in the table then 
            Some(_) => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::UnavailableFunctionName{name:&lookup(name), span}),
            None => {
              // Get the function address 
              let addr = self.next_function_pointer();
              // Store the address in the symbol table
              self.fill_function_pointer_patch(&name, addr);           
              // self.table.insert(name, VarDecl { ty: Ty::Function((ptr as f32).to_le_bytes()) });
              // Compile the function 
              self.compile_block();
            }
          },
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::MissingFnName{token:other}),
        };  
      
      }
      TokenKind::Call => {
        let (name, span) = match self.next_token().unwrap() {
          Token { kind: TokenKind::Identifier(name,), span } => (name, span),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,  ASMError::NoNameCall { token: other }),
        };

        // Place the Call opcode in the function
        self.main.push(OpCode::Call.into(),);

        match self.table.lookup(&name){
          // If the function already has a symbol table entry attempt to retrieve its pointer
          Some(VarDecl { ty: Ty::Function(ptr)}) => {
            self.main.extend_from_slice(ptr,)
          },
          // If the function does not have a symbol table entry *during function compilation* make a patch
          None if self.phase == CompilerPhase::FunctionCompilation => self.create_function_pointer_patch(&name),
          // If the function does not have a symbol table entry *during binary compilation* error 
          None => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::UndefinedFunction { name: &lookup(name), span }),
          // If the identifier does not reference a function throw an error
          Some(VarDecl { ty }) => ErrorPrinter::graceful_exit(io::stdout(), &self.source, ASMError::NotFunction(*ty)),
        }
      }
      TokenKind::SysCall => {
        let call_idx = match  self.next_token().unwrap() {
          // Confirm the token is an identifier
          Token {
            kind: TokenKind::Identifier(idx,),
            span,
            // Get the vardecl associated with the identifer
          } => match self.table.lookup(&idx,) {
            // Confirm the decl is an external function
            Some(decl,) => match decl.ty {
              Ty::ExternalFunction(idx,) => idx,
              _ => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::UnregistedSyscall{name:&lookup(idx), span}),
            },
            // If the decl identifer is not registered error
            None => panic!("{}",ASMError::UnregistedSyscall{name:&lookup(idx), span}),
          },
          // This should be must be followed by a syscall name not unregisted
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::NoNameCall{token: other}),
        };

        self
          .main
          .extend_from_slice(&[OpCode::SysCall.into(), call_idx,],);
      }
      TokenKind::Label(name,) => {
        // The label's address is the current len of the program
        self
          .table
          .add_symbol(name, VarDecl::new(Ty::Label(self.main.len() as u32,),),);
      }
      TokenKind::Noop => self.main.push(OpCode::Noop.into(),),
      TokenKind::Push => {
        let reg = self.next_token_as_register();
        self.main.extend_from_slice(&[OpCode::Push.into(), reg,],);
      }
      TokenKind::Pop => self.main.push(OpCode::Pop.into(),),
      TokenKind::PopR => {
        let reg = match  self.next_token().unwrap() {
          Token {
            kind: TokenKind::Register(dst,),
            ..
          } => dst,
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::NotRegisterOrIdent { token: other }),
        };
        self.main.extend_from_slice(&[OpCode::PopR.into(), reg,],);
      }
      TokenKind::Wmem | TokenKind::Rmem => {
        let op = match self.current_instruction.kind {
          TokenKind::Wmem => OpCode::WMem.into(),
          TokenKind::Rmem => OpCode::RMem.into(),
          _=> unreachable!()
        };
        
        // Get the register storing the destination
        let dst = self.next_token_as_register();
        // Get the register storing the pointer
        let src = self.next_token_as_register();
        // Get the value ::Callof the immediate offset
        let i_offset = self.next_token_as_immediate_array();
        // Get the register storing the register offset
        let r_offset = self.next_token_as_register();

        self.main.extend_from_slice(&[ op, dst, src, i_offset[0], i_offset[1], i_offset[2], i_offset[3], r_offset,],);
      }
      TokenKind::MemCpy => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        self
          .main
          .extend_from_slice(&[OpCode::MemCpy.into(), dst, src,],);
      }
      TokenKind::Alloc => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        self
          .main
          .extend_from_slice(&[OpCode::Alloc.into(), dst, src,],);
      }
      TokenKind::Dealloc => self.main.extend_from_slice(&[OpCode::Dealloc.into(),],),
      TokenKind::Ret => {
        // Number of items to pop from the stack when returning
        let pop_number = match self.next_token(){
            Some(Token { kind:TokenKind::Num(num), .. }) => num as u8,
            None => unreachable!("Must have a token"),
            // TODO: Make real error
            Some(Token { kind, span}) => panic!("{} {} is not a number, expected number after `Ret`.", kind, span.start),
        };
        self.main.extend_from_slice(&[ OpCode::Ret.into(), pop_number,],);
      }
      TokenKind::Eof => {}
      _ => panic!(
        "{}",
        ASMError::NotAnOpcode { token: self.current_instruction }
      ),
    }
  }

  /// Consume and discard the next block in the program.
  fn eat_block(&mut self,) {
    let next = self.next_token().unwrap();
    assert!(
      next.kind == TokenKind::LCurlyBracket,
      "Block must begin with {{ not {}",
      next.kind
    );

    // Create the block to be compiled
    while let Some(instruction,) =  self.next_token() {
      if instruction.kind == TokenKind::RCurlyBracket {
        // Does not need to eat the block because the compile function will call the
        // next token
        break;
      }      
    }
  }

  /// Compile the next block in the program.
  fn compile_block(&mut self,) {
    // TODO: I don't like having the curly bracket check being part of this. 
    // Ideally the assembler would start assembling a block whenever it encounters a curly brace.
    match self.next_token().unwrap(){
      Token { kind:TokenKind::LCurlyBracket, .. } => {},
      other => panic!("Block must begin with {{ not {} {}", other.kind, other.span.start)
    }

    // Enter a new scope 
    self.table.enter_scope();

    // Create the block to be compiled
    while let Some(_,) =  self.next_token() {
      if self.current_instruction.kind == TokenKind::RCurlyBracket {
        // Does not need to eat the bracket because the compile instruction will call the
        // next token
        break;
      }
      self.compile_current_instruction()
    }

    // Exit the scope
    self.table.exit_scope();
  }

  #[rustfmt::skip]
  /// Compile a comparison expression (EQ, GT, LT, GEQ, LEQ).
  pub(super) fn compile_comparison(&mut self, op:&Token, token_a:&Token, token_b:&Token,) {
    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediates perform the check during compilation
        let result = match op {
          Token {
            kind: TokenKind::Eq, ..
          } => ((a == b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Gt, ..
          } => ((a > b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Lt, ..
          } => ((a < b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Geq,
          ..
          } => ((a >= b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Leq,
          ..
          } => ((a <= b) as u32).to_le_bytes(),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{ token: *other }),
        };

        self.main.extend_from_slice(&[
          OpCode::Load.into(), EQ as u8,result[0], result[1], result[2], result[3],
        ],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate
        let b = b.to_le_bytes();
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        match op {
          Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
          Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
          Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
          Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
          Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        };
      }
      _ => unreachable!(),
    }
  }

  /// Compile a comparison expression (EQ, GT, LT, GEQ, LEQ). Return it as a
  /// program instead of modifying the currently compiled program in place.
  #[rustfmt::skip]
  pub(super) fn compile_comparison_return(&mut self, op:&Token, token_a:&Token, token_b:&Token,) -> Program {
    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediates perform the check during compilation
        let result = match op {
          Token {
            kind: TokenKind::Eq, ..
          } => ((a == b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Gt, ..
          } => ((a > b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Lt, ..
          } => ((a < b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Geq,
          ..
          } => ((a >= b) as u32).to_le_bytes(),
          Token {
            kind: TokenKind::Leq,
          ..
          } => ((a <= b) as u32).to_le_bytes(),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other}),
        };

        return Program::from(&[
          OpCode::Load.into(), EQ as u8, result[0], result[1], result[2], result[3],
        ],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate
        let b = b.to_le_bytes();    
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
          Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
          Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
          Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        match op {
          Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
          Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
          Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
          Token { kind:TokenKind::Geq, .. } =>Program::from(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
          Token { kind:TokenKind::Leq, .. } =>Program::from(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
          other => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidComparison{token:*other})
        }
      }
      (other_1, other_2,) => panic!("({} and {}) are invalid comparison arguments.", other_1, other_2),
    }
  }

  /// Compile an arithmetic operation (ADD, SUB, MUL, DIV, POW).
  pub (super) fn compile_arithmetic_expr(&mut self,){
    let op = self.current_instruction;
    // Get the destination
    let dst = match self.next_token().unwrap() {
      Token{kind:TokenKind::Register(reg,), ..} => reg,
      Token{kind:TokenKind::Identifier(name,), span} => self.ident_to_reg(name, span,),
      other => unreachable!("{}", ASMError::NotRegisterOrIdent{token:other},),
    };
    let arg1 =  self.next_token().unwrap();
    let arg2 =  self.next_token().unwrap();

    // Match the arguments to get the type of instruction to use
    let arg_type = match (arg1.kind, arg2.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => ArgTypes::II(a, b),
      (TokenKind::Num(a,), TokenKind::Register(b,),) => ArgTypes::IR(b, a.to_le_bytes()),
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => ArgTypes::IR(self.ident_to_reg(b, arg2.span,), a.to_le_bytes(),), 
      (TokenKind::Register(a,), TokenKind::Num(b,),) => ArgTypes::RI(a, b.to_le_bytes()),
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => ArgTypes::RI(self.ident_to_reg(a, arg1.span,), b.to_le_bytes()),
      (TokenKind::Register(a,), TokenKind::Register(b,),) => ArgTypes::RR(a, b),
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => ArgTypes::RR(self.ident_to_reg(a, arg1.span,), self.ident_to_reg(b, arg2.span,)),
      _ => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::InvalidMathArgs { operation: op, arg1, arg2})
    };

    // Match the operation to see which instruction to add
    match (op.kind, arg_type) {
      // Handle Addition
      (TokenKind::Add, ArgTypes::II(a, b)) => {
        let result = (a + b).to_le_bytes();
        self.main.extend_from_slice(&[OpCode::Load.into(), dst, result[0], result[1], result[2], result[3],],)
      }
      (TokenKind::Add, ArgTypes::RI(a, b) | ArgTypes::IR(a, b)) => self.main.extend_from_slice(&[OpCode::AddRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Add, ArgTypes::RR(a, b)) => self.main.extend_from_slice(&[OpCode::AddRR.into(), dst, a, b]),
      
      // Handle Subtraction
      (TokenKind::Sub, ArgTypes::II(a, b)) => {
        let result = (a - b).to_le_bytes();
        self.main.extend_from_slice(&[OpCode::Load.into(), dst, result[0], result[1], result[2], result[3],],)
      }
      (TokenKind::Sub, ArgTypes::RI(a, b)) => self.main.extend_from_slice(&[OpCode::SubRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Sub, ArgTypes::IR(a, b)) => self.main.extend_from_slice(&[OpCode::RvSubRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Sub, ArgTypes::RR(a, b)) => self.main.extend_from_slice(&[OpCode::SubRR.into(), dst, a, b]),
      
      // Handle Multiplication
      (TokenKind::Mul, ArgTypes::II(a, b)) => {
        let result = (a * b).to_le_bytes();
        self.main.extend_from_slice(&[OpCode::Load.into(), dst, result[0], result[1], result[2], result[3],],)
      }
      (TokenKind::Mul, ArgTypes::RI(a, b) | ArgTypes::IR(a, b)) => self.main.extend_from_slice(&[OpCode::MulRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Mul, ArgTypes::RR(a, b)) => self.main.extend_from_slice(&[OpCode::MulRR.into(), dst, a, b]),
      
      // Handle Division
      (TokenKind::Div, ArgTypes::II(a, b)) => {
        let result = (a / b).to_le_bytes();
        self.main.extend_from_slice(&[OpCode::Load.into(), dst, result[0], result[1], result[2], result[3],],)
      }
      (TokenKind::Div, ArgTypes::RI(a, b)) => self.main.extend_from_slice(&[OpCode::DivRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Div, ArgTypes::IR(a, b)) => self.main.extend_from_slice(&[OpCode::RvDivRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Div, ArgTypes::RR(a, b)) => self.main.extend_from_slice(&[OpCode::DivRR.into(), dst, a, b]),
      
      // Handle Exponentiation
      (TokenKind::Pow, ArgTypes::II(a, b)) => {
        let result = (a.powf(b)).to_le_bytes();
        self.main.extend_from_slice(&[OpCode::Load.into(), dst, result[0], result[1], result[2], result[3],],)
      }
      (TokenKind::Pow, ArgTypes::RI(a, b)) => self.main.extend_from_slice(&[OpCode::PowRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Pow, ArgTypes::IR(a, b)) => self.main.extend_from_slice(&[OpCode::RvPowRI.into(), dst, a, b[0], b[1], b[2], b[3]]),
      (TokenKind::Pow, ArgTypes::RR(a, b)) => self.main.extend_from_slice(&[OpCode::PowRR.into(), dst, a, b]),
      _=> unreachable!()
    }

  }

  /// Compiles the current comparison expression and returns the  [`Program`].
  pub(super) fn compile_cond_expr(&mut self,) -> Program {
    let op = self.next_token().unwrap();
    let token_a = self.next_token().unwrap();
    let token_b = self.next_token().unwrap();
    self.compile_comparison_return(&op, &token_a, &token_b,)
  }

  pub(super) fn compile_loop_expr(&mut self,) {
    // Set the return address
    let ret = self.main.len() as u32;
    
    // Compile the block contaning the LOOP's contents and add it to the
    // main main
    self.compile_block();

    // Add the Jmp to the `ret` address
    self.main.push(OpCode::Jmp.into());
    self.main.extend_from_slice(&ret.to_le_bytes());
  }

  pub(super) fn compile_while_loop_expr(&mut self){
    // Catch the statment here if it is a bool and optimize it out
    if let TokenKind::Bool(b,) = self.peek().unwrap().kind {
      self.next_token().unwrap();
      if b {
        self.compile_loop_expr();
      }
      else {
        self.eat_block();
      }
      return;
    }

    let cond = self.compile_cond_expr();

    // Use a defered patch here to jump to the check
    self.main.push(OpCode::Jmp.into(),);
    // Create a patch for the address of the condition check
    let mut patch = Patch::new();
    patch.reserve_region(&mut self.main);

    // Set the return point for the JNZ to be the begining of the loop block's logic
    let ret = (self.main.len() as u32).to_le_bytes();

    // Compile the block contaning the LOOP's contents and add it to the
    // main program
    self.compile_block();

    // Set the defered patch's target to the cond check
    // self.linker.update_jump_site(jump_site, self.main.len());
    patch.update_address(self.main.len()).unwrap();
    patch.patch(&mut self.main);

    // Check the condition
    self.main.extend_from_slice(cond.as_slice(),);

    // Jump to the `ret` address if the condition is true (not zero)
    self.main.extend_from_slice(&[OpCode::Jnz.into(), EQ as u8, ret[0], ret[1], ret[2], ret[3]],);
  }

  #[rustfmt::skip]
  pub(super) fn compile_for_loop_expr(&mut self,) {
    // Confirm the next token is an ident and eat it
    // This ident is discarded because the loop_variable uses the LOOP reg
    let ident = self.next_token().unwrap();
    match ident.unwrap_ident() {
      Some(_,) => {}
      None => ErrorPrinter::graceful_exit(io::stdout(), &self.source,ASMError::MissingLoopVar{token:ident.kind,span:ident.span,}),
    }

    // Ensure the syntax contains "in" as required
    let kwd = self.next_token().unwrap();
    assert_eq!(
      kwd.kind,
      TokenKind::In,
      "{}",
      ASMError::MissingKwd(TokenKind::For, TokenKind::In, kwd.kind),
    );

    // Parse the range
    let (start, end,) = match self.next_token().unwrap().unwrap_range() {
      Ok((start, end,),) => ((start as f32).to_le_bytes(), (end as f32).to_le_bytes(),),
      Err(err,) => panic!("{}", err),
    };

    // Set the counter equal to the range's start
    
    self.main.extend_from_slice(&[
      OpCode::Load.into(), LOOP as u8, start[0], start[1], start[2], start[3],
    ],);

    // Set the return address
    let ret = (self.main.len() as u32).to_le_bytes();

    // Compile the block
    self.compile_block();

    self.main.extend_from_slice(&[
      // Increment the counter by the value of 1f32 in le bytes = [0, 0, 128, 63,]
      OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
      // Compare the counter to the range's end and store in EQ
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, end[0], end[1], end[2], end[3],
      // JZ EQ to the begining of the loop
      OpCode::Jz.into(), EQ as u8, ret[0], ret[1], ret[2], ret[3],
    ],);
  }

  /// Compiles the block making up the body of an `if` expression.
  pub(super) fn compile_if_body_expr(&mut self,) {
    // Handle the case where the condition is an immediate value (boolean)
    if let TokenKind::Bool(b,) = self.peek().unwrap().kind {
      // Make the bool the current token
      self.next_token();
      if b {
        // If the cond is `true`, just compile the block that makes up its body
        self.compile_block();
        // Also devour any following else block
        if self.peek().unwrap().kind == TokenKind::Else {
          // Must explicitly get rid of the current token because it is the curly bracket
          self.next_token();
          self.eat_block();
        }
      }
      else {
        // If the cond is `false` just eat the if
        self.eat_block();
        // If there is an else block compile the code
        if self.peek().unwrap().kind == TokenKind::Else {
          // Must explicitly get rid of the current token because it is the curly bracket
          self.next_token();
          self.compile_current_instruction();
        }
      }
      return;
    }
    // Compile the condition
    let cond = self.compile_cond_expr();
    self.main.extend_from_slice(cond.as_slice(),);

    // Check the condition. Use a JZ to jump to the end of the IF expression
    // if it is false.
    // Use a defered patch in place of the end of the expression.
    self.main.extend_from_slice(&[OpCode::Jz.into(), EQ as u8,],);
    let mut patch = Patch::new();
    patch.reserve_region(&mut self.main);

    // Compile the block
    self.compile_block();

    // Update the deferred patch
    patch.update_address(self.main.len(),).unwrap();
    patch.patch(&mut self.main);
  }
}

/// Possible argument combinations for a binary operation.
pub enum ArgTypes{
  II(f32, f32),
  RI(u8, [u8;4], ),
  IR(u8, [u8;4], ),
  RR(u8, u8),
}


pub struct AssemblerBuilder<'b, P,>
where
  P: AsRef<Path,>,
{
  /// A file to load containing an assembly script.
  source_file:Option<P,>,
  /// A string containing assembly code.
  source_str:Option<String,>,
  /// A writer for the [`Assembler`] to use for displaying errors.
  writer:Option<&'b mut dyn Write>,
}

// TODO: Add tests for the builder;
impl<'b, P, > AssemblerBuilder<'b, P, >
where
  P: AsRef<Path,>,
{
  pub fn new() -> Self {
    AssemblerBuilder {
      source_file:None,
      source_str:None,
      writer:None,
    }
  }

  /// Add a file to assemble.
  pub fn add_src_file(&mut self, src:P,) -> Result<(),> {
    if self.source_str.is_none() {
      self.source_file = Some(src,);
      Ok((),)
    }
    else {
      Err(eyre!(
        "Cannot assemble a file when a string has already been provided."
      ),)
    }
  }

  /// Add an ASM string to assemble.
  pub fn add_src_str(&mut self, src:impl ToString,) -> Result<(),> {
    if self.source_file.is_none() {
      self.source_str = Some(src.to_string(),);
      Ok((),)
    }
    else {
      Err(eyre!(
        "Cannot assemble a string when a file has already been provided."
      ),)
    }
  }

  // Unused for the moment
  // In the future, I might use it to allow the user to output errors
  // into a file instead of the standard output
  #[allow(unused)]
  pub fn add_writer(&mut self, w:&'b mut impl Write,) {
    self.writer = Some(w,)
  }

  /// Create an [`Assembler`] with the provided settings. Consumes the builder.
  pub fn build(self,) -> Assembler {
    if self.source_file.is_none() && self.source_str.is_none(){
      panic!("Must provide either a source string or a source file!")
    }

    let src = match self.source_file {
      Some(path) => SourceFile::new_from_path(path),
      None => SourceFile::new_from_str(self.source_str.unwrap()),
    };

    // If no writer was provided use the standard output
    let tokens=Lexer::new(&src).tokenize(self.writer.unwrap_or(&mut io::stdout()));
    
    Assembler { 
      phase: CompilerPhase::FunctionCompilation, 
      current_instruction:tokens[0], 
      tokens, 
      cursor:0, 
      table: SymbolTable::new(), 
      function_patches: HashMap::new(), 
      open: FIRST_FREE_REGISTER as u8, 
      main: Program::new(), 
      source:src, 
    }
  }
}
