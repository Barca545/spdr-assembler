mod assembler_errors;
mod compilation_helpers;
mod patch;
mod error_printing;
mod interner;
mod tokenizer;
mod cli_integration;
mod test;

use assembler_errors::ASMError;
use patch::Patch;
use interner::{intern, lookup};
use spdr_isa::{
  opcodes::OpCode,
  program::Program,
  registers::{FIRST_FREE_REGISTER, REG_COUNT},
};
use std::{
  collections::HashMap, fmt::{Debug, Display}, fs::read_to_string, io::{self, Write}, path::PathBuf, usize
};
use tokenizer::{Lexer, Span, Token, TokenKind};

// Refactor:
// - I think there has to be something I can do when parsing a line instead of
//   unwrapping next. It would be better to handle the `Option`. Probably as
//   simple as returning an error if the unwrap fails that says expected X/Y/Z
//   tokens should recieve its own symbol table to prevent this
// - I think there has to be a better way of storing the src to print than
//   storing it in the compiler like that. maybe just intern the whole thing and
//   reference it that way
// - `compile_block_return` can be implemented way more efficiently
// - Currently all identifiers must be unique. I am not actually sure this
//   bothers me.


// TODO:
// - Jump instructions should accept labels as arguments
// - Add array compilation

// Compiler Rules
// - LOOP/WHILE/FOR must have their own lines
// - The beginning and end of blocks need their own lines
// - All variables are global. Names must be unique

fn main() { 
  let args = cli_integration::parse_arguments().unwrap();

  let src = read_to_string(args.path).unwrap();

  let mut compiler = Compiler::new(&src,io::stdout());

  if let Some(header,) = args.header {
    // TODO: This should be able to take a PathBuf
    compiler.read_header(header,);
  }

  let program = compiler.compile();

  let output_file = &format!("{}/{}.spex",args.output.to_str().unwrap(),args.name);

  // TODO: Program should be able to take a PathBuf
  program.save(output_file,).unwrap();
}

#[derive(Debug, Clone, Copy,)]
//JUMP AND JNZ will never take a Register as an arg.
enum Ty {
  /// Registers hold the index of their assigned register
  Register(u8,),
  /// Labels hold the index number the label references.
  Label(usize,),
  /// Functions hold the function's address as a `[u8;4]`;
  Function([u8;4]),
  /// Functions hold the index the VM where stores them in its collection of
  /// external functions.
  ExternalFunction(u8,),
}

impl Display for Ty {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    match self {
      Ty::Register(v,) => write!(f, "Reg({})", v),
      Ty::Label(v,) => write!(f, "Label({})", v),
      Ty::Function(ptr ) => write!(f, "Function(patch_index: {:?}", ptr,),
      Ty::ExternalFunction(idx,) => write!(f, "ExternalFunction({idx})"),
    }
  }
}

#[derive(Clone, Copy,)]
/// A Symbol Table entry. Contains information about identities in the source
/// code.
struct VarDecl {
  ty:Ty,
}

impl Display for VarDecl {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    write!(f, "VarDecl(ty: {})", self.ty)
  }
}

impl Debug for VarDecl {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    Display::fmt(&self, f,)
  }
}

impl VarDecl {
  fn new(ty:Ty,) -> Self {
    Self { ty, }
  }
}

#[derive(Debug, Clone, Default, PartialEq)]
enum CompilerPhase{
  #[default]
  FunctionCompilation,
  BinaryCompilation,
}

#[derive(Debug, Clone,)]
struct Compiler<'tcx,> {
  phase:CompilerPhase,
  tokens:Vec<Token,>,
  cursor:usize,
  /// The [`Token`] the compiler is currently reading.
  current_instruction:Token,
  /// The Symbol Table for the currently compiling program.
  table:HashMap<u32, VarDecl,>,
  function_patches:HashMap<u32,Patch>,
  open:u8,
  /// The body of the binary's "`main`" function.
  main:Program,

  _str:&'tcx str,
}
impl<'tcx,> Compiler<'tcx,> {
  /// Create a new empty compiler without a file.
  fn new<W:Write>(src:&'tcx str, mut w:W) -> Self {
    let tokens = Lexer::new(src,).tokenize(&mut w);
    let current_instruction = tokens[0];
    Self {
      phase:CompilerPhase::default(),
      tokens,
      cursor:0,
      current_instruction,
      table:HashMap::new(),
      function_patches:HashMap::new(),
      main:Program::new(),
      open:FIRST_FREE_REGISTER as u8,
      _str:src,
    }
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

  /// Adds an identifier to the [`Compiler`]'s Symbol Table as a
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
    match self.table.get(&ident){
      Some(decl) => match decl.ty {
        Ty::Register(reg) => reg,
        ty=> panic!("{} is already declared as a {}", lookup(ident), ty)
      },
      None => {
        let reg = self.reserve_reg();
        assert!(reg <= REG_COUNT as u8, "New register allocation strategy needed");

        self
          .table
          .insert(ident, VarDecl::new(Ty::Register(reg,),),);
        reg
      },
    }
  }

  /// Read a `*.hd` file from the given path.
  fn read_header(&mut self, src:PathBuf,) {
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
        .insert(sym, VarDecl::new(Ty::ExternalFunction(idx as u8,),),);
    }
  }

  /// Converts the `name` of a [`TokenKind::Identifier`] into a register
  /// address. Takes the current instruction and identifier location as
  /// arguments for error purposes.
  fn ident_to_reg(&self, name:u32, span:Span,) -> u8 {
    // Convert a variable declaration into a register
    // Error if the variable has not been declared
    let decl = match self.table.get(&name,) {
      Some(decl,) => decl,
      None => panic!("{}", ASMError::UndeclaredIdentifier{ ident: &lookup(name), span }),
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

  /// Give a concrete address to a function that was previously called without a definition. 
  fn fill_function_pointer_patch(&mut self, name:&u32, addr:usize){
    // Update the patch's PatchData
    self.function_patches.entry(*name).and_modify(|patch|patch.update_address(addr).unwrap());

    // Create an entry in the symbol table
    self.table.insert(*name, VarDecl { ty:Ty::Function((addr as u32).to_le_bytes()) });
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
      other => panic!("{}", ASMError::InvalidImmediateType{token:other}),
    }
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Register`], return
  /// it as a `u8`.
  fn next_token_as_register(&mut self,) -> u8 {
    match self.next_token().unwrap() {
      Token {
        kind: TokenKind::Register(idx,),
        ..
      } => idx,
      // If it's an idetifier get the var decl, ensure it is a variable, then get the corresponding reg
      Token {
        kind: TokenKind::Identifier(name,),
        span,
        // Check the identifier is declared
      } => self.ident_to_reg(name, span,),
      // Anything other than an identigier should be an error
      other => panic!("{}", ASMError::NotRegisterOrIdent{token:other}),
    }
  }

  /// Compiles the .spdr file loaded into the compiler into a .spex executable
  /// file.
  fn compile(&mut self,) -> Program {
    // Compile only the functions and variables and store them at the beginning of the binary
    while let Some(instruction) = self.next_token(){
      match instruction.kind{
        TokenKind::Fn => self.compile_current_instruction(),
        TokenKind::Var => {
          // Add the next token to the symbol table assuming it is an ident
          let ident =  self.next_token().unwrap();
          self.add_as_reg(ident,);
          // Consume the literal 
          self.eat_tokens(4,)
        }
        _=> self.eat_current_instruction(),
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
    // Switch the compiler phase
    self.phase = CompilerPhase::BinaryCompilation;

    // Compile `main` -- iterate over each instruction and interpret it as an opcode
    while let Some(instruction,) =  self.next_token() {
      // Compile while skipping function definitions
      match instruction.kind {
        TokenKind::Fn => self.eat_current_instruction(),
        _ => self.compile_current_instruction(),
      }
    }
    
    self.main.push(OpCode::Hlt.into());
    return self.main.clone()
  }

  /// Consume and discard the current intruction in the program.
  fn eat_current_instruction(&mut self,) {
    match self.current_instruction.kind {
      // Consume 0 tokens
      TokenKind::Eof | TokenKind::Noop | TokenKind::Pop | TokenKind::Dealloc => {}

      // Consume 1 token
      TokenKind::Call | TokenKind::SysCall | TokenKind::Push | TokenKind::PopR | TokenKind::Ret => {
        self.eat_tokens(1,)
      }
      // Consume 2 tokens
      TokenKind::Load
      | TokenKind::Var
      | TokenKind::Not
      | TokenKind::Eq
      | TokenKind::Gt
      | TokenKind::Lt
      | TokenKind::Geq
      | TokenKind::Leq
      | TokenKind::MemCpy
      | TokenKind::Copy
      | TokenKind::Alloc => self.eat_tokens(2,),
      // Consume 3 tokens
      TokenKind::Add | TokenKind::Sub | TokenKind::Mul | TokenKind::Div | TokenKind::Pow => {
        self.eat_tokens(3,)
      }
      // Consume 4 tokens
      TokenKind::Wmem | TokenKind::Rmem => self.eat_tokens(4,),

      // Special conditions for consuming
      TokenKind::Loop => self.eat_block(),
      TokenKind::While | TokenKind::If => {
        match self.next_token().unwrap().kind {
          TokenKind::Eq | TokenKind::Gt | TokenKind::Geq | TokenKind::Lt | TokenKind::Leq => {
            self.eat_tokens(2,)
          }
          TokenKind::Bool(_,) => {}
          other => panic!("{}", ASMError::NotEquality(other,)),
        }
        self.eat_block();
      }
      TokenKind::For => {
        self.eat_tokens(3,);
        self.eat_block()
      }
      TokenKind::Fn => {
        // Eat the name
        self.eat_tokens(1,);
        // Eat the body
        self.eat_block();
      }
      TokenKind::Else => {
        // If the "instruction" starts with a bracket, eat block should be called
        return match self.peek().unwrap().kind {
          TokenKind::LCurlyBracket => self.eat_block(),
          // Doing nothing here will make it continue compiling the program which is what we want
          _ => {}
        };
      }
      _ => panic!(
        "{}",
        ASMError::NotAnOpcode{ token: self.current_instruction }
         
        
      ),
    }
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
        let name = match  self.next_token().unwrap() {
          Token { kind:TokenKind::Identifier(name,) , .. } => name,
          other => panic!("{}", ASMError::MissingFnName{token:other}),
        };  
      
        // Create a function declaration and store it in the symbol table
        match self.table.get(&name,) {
          // If the name is already in the table then 
          Some(_) => panic!("{}", ASMError::UnavailableFunctionName(&lookup(name))),
          None => {
            // Get the function address 
            let addr = self.next_function_pointer();
            // Store the address in the symbol table
            self.fill_function_pointer_patch(&name, addr);           
            // self.table.insert(name, VarDecl { ty: Ty::Function((ptr as f32).to_le_bytes()) });
            // Compile the function 
            self.compile_block();
          }
        }
      }
      TokenKind::Call => {
        let (name, span) = match self.next_token().unwrap() {
          Token { kind: TokenKind::Identifier(name,), span } => (name, span),
          other => panic!("{}", ASMError::NoNameCall { token: other }),
        };

        // Place the Call opcode in the function
        self.main.push(OpCode::Call.into(),);

        match self.table.get(&name){
          // If the function already has a symbol table entry attempt to retrieve its pointer
          Some(VarDecl { ty: Ty::Function(ptr)}) => {
            self.main.extend_from_slice(ptr,)
          },
          // If the function does not have a symbol table entry *during function compilation* make a patch
          None if self.phase == CompilerPhase::FunctionCompilation => self.create_function_pointer_patch(&name),
          // If the function does not have a symbol table entry *during binary compilation* error
          None => panic!("{}", ASMError::UndefinedFunction { name: &lookup(name), span }),
          // If the identifier does not reference a function throw an error
          Some(VarDecl { ty })  => panic!("{}", ASMError::NotFunction(*ty)),
        }
      }
      TokenKind::SysCall => {
        let call_idx = match  self.next_token().unwrap() {
          // Confirm the token is an identifier
          Token {
            kind: TokenKind::Identifier(idx,),
            span,
            // Get the vardecl associated with the identifer
          } => match self.table.get(&idx,) {
            // Confirm the decl is an external function
            Some(decl,) => match decl.ty {
              Ty::ExternalFunction(idx,) => idx,
              _ => panic!("{}", ASMError::UnregistedSyscall{name:&lookup(idx), span}),
            },
            // If the decl identifer is not registered error
            None => panic!("{}",ASMError::UnregistedSyscall{name:&lookup(idx), span}),
          },
          // This should be must be followed by a syscall name not unregisted
          other => panic!("{}", ASMError::NoNameCall{token: other}),
        };

        self
          .main
          .extend_from_slice(&[OpCode::SysCall.into(), call_idx,],);
      }
      TokenKind::Label(name,) => {
        // The label's address is the current len of the program
        self
          .table
          .insert(name, VarDecl::new(Ty::Label(self.main.len(),),),);
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
          other => panic!("{}", ASMError::NotRegisterOrIdent { token: other }),
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
    let next =  self.next_token().unwrap();
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
      self.eat_current_instruction()
    }
  }

  /// Compile the next block in the program.
  fn compile_block(&mut self,) {
    let next = self.next_token().unwrap();
    assert!(
      next.kind == TokenKind::LCurlyBracket,
      "Block must begin with {{ not {}",
      next.kind
    );
    // Create the block to be compiled
    while let Some(_,) =  self.next_token() {
      if self.current_instruction.kind == TokenKind::RCurlyBracket {
        // Does not need to eat the bracket because the compile instruction will call the
        // next token
        break;
      }
      self.compile_current_instruction()
    }
  }
}