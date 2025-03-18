mod assembler_errors;
mod compilation_helpers;
mod patch;
mod error_printing;
mod interner;
mod tokenizer;
mod cli_integration;

use assembler_errors::ASMError;
use patch::Patch;
use interner::{intern, lookup};
use spdr_isa::{
  opcodes::OpCode,
  program::Program,
  registers::{FIRST_FREE_REGISTER, REG_COUNT},
};
use std::{
  collections::HashMap, fmt::{Debug, Display}, fs::read_to_string, io::{self, Write}, usize,
};
use tokenizer::{Lexer, Span, Token, TokenKind};

// Refactor:
// - I think there has to be something I can do when parsing a line instead of
//   unwrapping next. It would be better to handle the `Option`. Probably as
//   simple as returning an error if the unwrap fails that says expected X/Y/Z
//   tokens should recieve its own symbol table to prevent this
// - Eventually I should sub out usizes and choose some number that is platform
//   independent
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
    compiler.read_header(header.to_str().unwrap(),);
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
    // Get the currently open register and update the indicator to the next open
    // register
    let reg = self.reserve_reg();

    assert!(reg <= REG_COUNT as u8, "New register allocation strategy needed");

    match ident {
      Token {
        kind: TokenKind::Identifier(sym_idx,),
        ..
      } => {
        self
          .table
          .insert(sym_idx, VarDecl::new(Ty::Register(reg,),),);
      }
      _ => panic!("Tried to make a non identifier {} into a variable", ident.kind),
    }
    reg
  }

  /// Read a `*.hd` file from the given path.
  fn read_header(&mut self, src:&str,) {
    // Load the header file and split them by lines
    let header = read_to_string(src,).unwrap();

    // Split the header into lines so each index corresponds to a function sig
    for (idx, line,) in header.lines().enumerate() {
      // No need to parse the full signature just store the name as a key and the
      // idx of the func
      // TODO: Figure out if the header file should be tokenized

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
    // Compile only the functions and store them at the beginning of the binary
    while let Some(instruction) = self.next_token(){
      match instruction.kind{
        TokenKind::Fn => self.compile_current_instruction(),
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
    match self.current_instruction.kind {
      TokenKind::Load => {
        let reg = self.next_token_as_register();

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
      TokenKind::Var => {
        // Add the next token to the symbol table assuming it is an ident
        let ident =  self.next_token().unwrap();
        let reg = self.add_as_reg(ident,);

        // Eat the `=` sign
        if TokenKind::EqualSign !=  self.next_token().unwrap().kind {
          panic!("{}", ASMError::NoEquals(self.current_instruction.kind))
        }

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        self
          .main
          .extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Add => {
        let target =  self.next_token().unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_add_expr(&target, &a, &b,)
      }
      TokenKind::Sub => {
        let target =  self.next_token().unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_sub_expr(&target, &a, &b,)
      }
      TokenKind::Mul => {
        let target =  self.next_token().unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_mul_expr(&target, &a, &b,)
      }
      TokenKind::Div => {
        let target =  self.next_token().unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_div_expr(&target, &a, &b,)
      }
      TokenKind::Pow => {
        let target =  self.next_token().unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_pow_expr(&target, &a, &b,)
      }
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

#[cfg(test)]
mod test {
  use std::{any::Any, io};
  use crate::{interner::intern, Compiler, Ty, VarDecl};
  use spdr_isa::{
    opcodes::{CmpFlag, OpCode},
    program::Program,
    registers::{EQ, LOOP},
  };
  use spdr_vm::vm::VM;

  #[test]
  fn load_header() {
    let mut compiler = Compiler::new("",io::stdout());
    compiler.read_header("../spdr-assembler/src/test/test_header.hd",);

    let decl_1 = match compiler.table.get(&intern("foo",),).unwrap().ty {
      Ty::ExternalFunction(idx,) => idx,
      _ => panic!(),
    };
    assert_eq!(decl_1, 0);

    let decl_2 = match compiler.table.get(&intern("bar",),).unwrap().ty {
      Ty::ExternalFunction(idx,) => idx,
      _ => panic!(),
    };
    assert_eq!(decl_2, 1);
  }

  #[test]
  fn eat_instruction_works() {
    let src = include_str!("../src/test/full_compilation_test.spdr");
    let p = Compiler::new(src, io::stdout()).eat_compile();
    assert_eq!(p.as_slice(), []);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_load_cpy() {
    let p = Compiler::new("Load $14 1 Copy $15 $12",io::stdout()).compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
      OpCode::Load.into(), 14, 0, 0, 128, 63,
      OpCode::Copy.into(), 15, 12,
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_memcpy_rmem_wmem() {
    let p = Compiler::new("wmem $14 $15 1 $16 memcpy $55 $50 rmem $255 $40 1 $20",io::stdout()).compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
      OpCode::WMem.into(), 14, 15, 0, 0, 128, 63, 16,
      OpCode::MemCpy.into(), 55, 50,
      OpCode::RMem.into(), 255, 40, 0, 0, 128, 63, 20,
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_alloc_dealloc() {
    let p = Compiler::new("Alloc $14 $90 Dealloc", io::stdout()).compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
      OpCode::Alloc.into(), 14,   90,
      OpCode::Dealloc.into(),
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  fn compile_arith() {
    // ADDII
    let p = Compiler::new("ADD $14 15 10", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 14, 0, 0, 200, 65, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // ADDRI
    let p = Compiler::new("ADD $14 $15 10", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::AddRI.into(), 14, 15, 0, 0, 32, 65, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // ADDRR
    let p = Compiler::new("ADD $14 $14 $15", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::AddRR.into(), 14, 14, 15, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // SUBII
    let p = Compiler::new("SUB $14 10 30", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 14, 0, 0, 160, 193, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // SUBIR
    let p = Compiler::new("SUB $15 90 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::RvSubRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // SUBRI
    let p = Compiler::new("SUB $15 $14 90", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::SubRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // SUBRR
    let p = Compiler::new("SUB $15 $14 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::SubRR.into(), 15, 14, 14, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // MULII
    let p = Compiler::new("MUL $14 10 29.32", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 14, 154, 153, 146, 67, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // MULRI
    let p = Compiler::new("MUL $15 $14 10", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::MulRI.into(), 15, 14, 0, 0, 32, 65, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // MULRR
    let p = Compiler::new("MUL $15 $14 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::MulRR.into(), 15, 14, 14, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // DIVII
    let p = Compiler::new("DIV $14 32.54 653", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 14, 42, 28, 76, 61, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // DIVRI
    let p = Compiler::new("DIV $15 $14 90", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::DivRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // DIVIR
    let p = Compiler::new("DIV $15 90 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::RvDivRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // DIVRR
    let p = Compiler::new("DIV $15 $14 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::DivRR.into(), 15, 14, 14, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // POWII
    let p = Compiler::new("POW $14 76.253216 3.7", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 14, 127, 144, 12, 75, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // POWRI
    let p = Compiler::new("POW $15 $14 90", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::PowRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // POWIR
    let p = Compiler::new("POW $15 90 $14",io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::RvPowRI.into(), 15, 14, 0, 0, 180, 66, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // PowRR
    let p = Compiler::new("POW $15 $14 $14", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::PowRR.into(), 15, 14, 14, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_loop() {
    // Test plain loop compilation
    let mut c = Compiler::new("Loop {ADD $14 $30 1}", io::stdout());
    let p = c.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // Check the output is accurate
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
      OpCode::Jmp.into(), 5, 0, 0, 0, // Jump to 5
      OpCode::Hlt.into()
    ];
    assert_eq!(p.as_slice(), expected);

    // Test plain loop compilation with function at beginning
    let mut c = Compiler::new("Loop {ADD $14 $30 1} FN foo {SUB $16 $94 $233 RET 1}", io::stdout());
    let p = c.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // Check the output is accurate
    let expected = [
      OpCode::Jmp.into(), 11, 0, 0, 0, // `main` starts on 11
      OpCode::SubRR.into(), 16, 94, 233,
      OpCode::Ret.into(), 1,
      OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
      OpCode::Jmp.into(), 11, 0, 0, 0,  // Jump to 11
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_while_loop(){
    // Test while loop compilation when `true`
    let mut c = Compiler::new("while true {noop noop noop}",io::stdout());
    let p = c.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // Check the output is accurate
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Jmp.into(), 5, 0, 0, 0, 
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // Test While loop compilation when `false`
    let p = Compiler::new("while false {noop noop noop}", io::stdout()).compile();
   
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // Test While loop compilation with real condition
    let mut c = Compiler::new("while EQ $15 1 {noop noop noop}", io::stdout());
    let p = c.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Jmp.into(), 13, 0, 0, 0, // Jump to 13
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
      OpCode::Jnz.into(), EQ as u8, 10, 0, 0, 0, // Jump to 10
      OpCode::Hlt.into()
    ];
    assert_eq!(p.as_slice(), expected);

    // Test While loop compiles when binary contains function
    let mut c = Compiler::new("WHILE EQ $15 1 {ADD $15 $15 $54 } FN foo {NOOP NOOP}", io::stdout());
    let p = c.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    let expected = [
      OpCode::Jmp.into(), 7, 0, 0, 0, // `main` starts on 7
      // foo
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      // Main 
      OpCode::Jmp.into(), 16, 0, 0, 0,// Jump to 16
      OpCode::AddRR.into(), 15, 15, 54,
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
      OpCode::Jnz.into(), EQ as u8, 12, 0, 0, 0, // Jump to 12
      OpCode::Hlt.into()
    ];
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_for_loop(){
    // Test For loop compilation
    let mut c = Compiler::new("for i in 0..9 {noop noop noop}", io::stdout());
    let p = c.compile();   

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
      OpCode::Jz.into(), EQ as u8, 11, 0, 0, 0, // Jump to 11
      OpCode::Hlt.into(),
    ];

    assert_eq!(p.as_slice(), expected);

    // Test for loop compiles when binary has function
    let mut c = Compiler::new("FOR i IN 0..9 {NOOP NOOP NOOP} FN foo {NOOP NOOP}", io::stdout());
    let p = c.compile(); 

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p); 

    let expected = [
      OpCode::Jmp.into(), 7, 0, 0, 0, // `main` starts on 7
      // This is the function
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      // This is main
      OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
      OpCode::Jz.into(), EQ as u8, 13, 0, 0, 0, // Jump to 13
      OpCode::Hlt.into(),
    ];

    // Check the output is accurate when binary contains a function
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_if_else() {
    // Compile IF with boolean true check
    // Compile ELSE
    let p = Compiler::new("IF true {Noop Noop Noop Noop} else {Add $15 0 1} Mul $16 1 1", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Load.into(), 16, 0, 0, 128, 63, 
      OpCode::Hlt.into(),
    ];
    
    assert_eq!(p.as_slice(), expected);

    // Compile IF with boolean false check
    let p = Compiler::new("IF false {mul $54 0 1 } else {add $26 $17 1} add $46 0 1", io::stdout()).compile();
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      // Else Block
      OpCode::AddRI.into(), 26, 17, 0, 0, 128, 63,
      // Trailing expression
      OpCode::Load.into(), 46, 0, 0, 128, 63,
      OpCode::Hlt.into(),
    ];

    assert_eq!(p.as_slice(), expected);


    // Compile IF with runtime check
    // Compile ELSE IF
    let p = Compiler::new(
      "IF EQ $14 0 {Noop Noop Noop Noop} Else If GT $15 1 {add $26 0 1 Noop Noop Noop} Mul $14 $14 1 ",
      io::stdout())
    .compile();
    // If is failing likely because it is placing the jump location after the else

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
        // IF expression
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 0, 0,
        OpCode::Jz.into(), EQ as u8, 22, 0, 0, 0, // Jump to idx 22 if the comparison fails
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        // ELSE IF expression
        OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 128, 63,
        OpCode::Jz.into(), EQ as u8, 44, 0, 0, 0, // Jump to idx 44 if the comparison fails
        OpCode::Load.into(), 26, 0, 0, 128, 63,
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::MulRI.into(), 14, 14, 0, 0, 128, 63,
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_single_function_defined(){
    let mut c = Compiler::new("Sub $54 $34 $65 FN foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the program is correct
    let expected = [
      OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
      // Beginning of `lib`
      OpCode::AddRR.into(), 14, 14, 15,
      OpCode::Noop.into(),
      OpCode::MulRR.into(), 88, 87, 98,
      OpCode::Ret.into(), 0, 
      // Beginning of `main`
      OpCode::SubRR.into(), 54, 34, 65,
      OpCode::DivRR.into(), 65, 58, 30,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_call_when_single_function_defined_before_calling(){
    let mut c = Compiler::new("Sub $54 $34 $65 fn foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the program is correct
    let expected = [
      OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
      // Beginning of `lib`
      OpCode::AddRR.into(), 14, 14, 15,
      OpCode::Noop.into(),
      OpCode::MulRR.into(), 88, 87, 98,
      OpCode::Ret.into(), 0,
      // Beginning of `main`
      OpCode::SubRR.into(), 54, 34, 65,
      OpCode::DivRR.into(), 65, 58, 30,
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_single_function_defined_after_call(){
    let mut c = Compiler::new("CALL foo SUB $54 $34 $65 CALL foo FN foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    let expected = [
      OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
      // Beginning of `lib`
      OpCode::AddRR.into(), 14, 14, 15,
      OpCode::Noop.into(),
      OpCode::MulRR.into(), 88, 87, 98,
      OpCode::Ret.into(), 0, 
      // Beginning of `main`
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::SubRR.into(), 54, 34, 65,
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::DivRR.into(), 65, 58, 30,
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_single_function_contains_recursion(){
    let mut c = Compiler::new("CALL foo FN foo {ADD $14 $14 $15 CALL foo NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    let expected = [
      OpCode::Jmp.into(), 21, 0, 0, 0, // `main`'s address is 21
      // Beginning of `lib`
      OpCode::AddRR.into(), 14, 14, 15,
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::Noop.into(),
      OpCode::MulRR.into(), 88, 87, 98,
      OpCode::Ret.into(), 0,
      // Beginning of `main`
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::DivRR.into(), 65, 58, 30,
      OpCode::Call.into(), 5, 0, 0, 0, // Call 5
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);
    
    assert_eq!(p.as_slice(), expected);

  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_multiple_functions_defined(){
    let src = "FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2}";
    let mut c = Compiler::new(src, io::stdout());
    let p = c.compile();

    // Check the function pointer of `foo` is correct
    let foo_fn_idx = &intern("foo");
    assert_eq!(foo_fn_idx, &0);
    match c.table.get(foo_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the function pointer of `bar` is correct
    let bar_fn_idx = &intern("bar");
    assert_eq!(bar_fn_idx, &1);
    match c.table.get(bar_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    let expected = [
      OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
      OpCode::AddRR.into(), 14, 60, 37, // `foo` starts at 5
      OpCode::Ret.into(), 3,
      OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
      OpCode::Ret.into(), 2,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_call_when_multiple_functions_defined_before_calling(){
    let src = "FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar";
    let mut c = Compiler::new(src, io::stdout());
    let p = c.compile();
    
    // Check the function pointer of `foo` is correct
    let foo_fn_idx = &intern("foo");
    assert_eq!(foo_fn_idx, &0);
    match c.table.get(foo_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the function pointer of `bar` is correct
    let bar_fn_idx = &intern("bar");
    assert_eq!(bar_fn_idx, &1);
    match c.table.get(bar_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    let expected = [
      OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
      OpCode::AddRR.into(),  14, 60, 37, // `foo` starts at 5
      OpCode::Ret.into(), 3,
      OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
      OpCode::Ret.into(), 2,
      // Call foo
      OpCode::Call.into(), 5, 0, 0, 0,
      // Call bar
      OpCode::Call.into(), 11, 0, 0, 0,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_multiple_functions_defined_after_call(){
    let mut c = Compiler::new("CALL bar CALL foo FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar", io::stdout());
    let p = c.compile();

    // Check the function pointer of `foo` is correct
    let foo_fn_idx = &intern("foo");
    assert_eq!(foo_fn_idx, &1);
    match c.table.get(foo_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the function pointer of `bar` is correct
    let bar_fn_idx = &intern("bar");
    assert_eq!(bar_fn_idx, &0);
    match c.table.get(bar_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the binary is correct
    let expected = [
      OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
      OpCode::AddRR.into(), 14, 60, 37, // `foo` starts at 5
      OpCode::Ret.into(), 3,
      OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
      OpCode::Ret.into(), 2,
      // Call bar
      OpCode::Call.into(), 11, 0, 0, 0,
      // Call foo
      OpCode::Call.into(), 5, 0, 0, 0,
      // Call foo
      OpCode::Call.into(), 5, 0, 0, 0,
      // Call bar
      OpCode::Call.into(), 11, 0, 0, 0,
      OpCode::Hlt.into(),
    ];
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }
  
  #[test]
  #[rustfmt::skip]
  #[should_panic = "\x1b[93mUNAVAILABLE FUNCTION NAME:\x1b[0m The name foo is already in use."]
  fn function_errors_when_name_in_use() {
    // Test fuction name reuse fails
    let _ = Compiler::new("FN foo {ADD $14 $14 4} FN foo {NOOP NOOP}", io::stdout()).compile();
  }

  #[test]
  #[rustfmt::skip]
  #[should_panic = "\x1b[93mUNDEFINED FUNCTION:\x1b[0m Cannot use foo (idx:5, ln:1, col:6) without defining it."]
  fn function_errors_when_not_defined(){
    // Test fuction name reuse fails
    let _ = Compiler::new("CALL foo", io::stdout()).compile();
  }

  #[test]
  #[rustfmt::skip]
  fn compile_syscall() {   
    let mut compiler = Compiler::new("syscall foo", io::stdout());
    compiler
      .read_header("../spdr-assembler/src/test/test_header.hd",);

    let p = compiler.compile();

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::SysCall.into(), 0,
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_push_pop() {
    let p = Compiler::new("Push $1 Push $1 Pop PopR $16", io::stdout()).compile();

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Push.into(), 1, 
      OpCode::Push.into(), 1,
      OpCode::Pop.into(),
      OpCode::PopR.into(), 16,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_eq() {
    // EQII
    let p = Compiler::new("eq 2 2", io::stdout()).compile();

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
      OpCode::Hlt.into()
    ]; 

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // EQIR
    let p = Compiler::new("eq $14 1", io::stdout()).compile();
    
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 128, 63, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // EQRR
    let p = Compiler::new("eq $14 $15", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 15, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_geq(){
    // GEQII
    let p = Compiler::new("geq 4 2", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // GEQRI
    let p = Compiler::new("geq $14 1", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // GEQIR
    let p = Compiler::new("geq 1 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63,
      OpCode::Not.into(), EQ as u8, EQ as u8,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // GEQRR
    let p = Compiler::new("geq $15 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRR.into(), CmpFlag::Geq.into(), 15, 14, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_leq(){
    // LEQII
    let p = Compiler::new("leq 4 2", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // LEQRI
    let p = Compiler::new("leq $14 1", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // LEQIR
    let p = Compiler::new("leq 1 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63,
      OpCode::Not.into(), EQ as u8, EQ as u8,
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);

    // LEQRR
    let p = Compiler::new("leq $15 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRR.into(), CmpFlag::Leq.into(), 15, 14, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }
  
  #[test]
  #[rustfmt::skip]
  fn compile_gt(){
    // GTII
    let p = Compiler::new("gt 4 2", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
      OpCode::Hlt.into()
    ];
    
    assert_eq!(p.as_slice(), expected);

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // GTRI
    let p = Compiler::new("gt $14 1", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63, 
      OpCode::Hlt.into()
    ];
    assert_eq!(p.as_slice(), expected);

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // GTIR
    let p = Compiler::new("gt 1 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63,
      OpCode::Not.into(), EQ as u8, EQ as u8,
      OpCode::Hlt.into(),
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);

    // GTRR
    let p = Compiler::new("gt $15 $14", io::stdout()).compile();
    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRR.into(), CmpFlag::Gt.into(), 15, 14, 
      OpCode::Hlt.into()
    ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_lt(){
    // LTII
    let p = Compiler::new("LT 2 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
        OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, 
        OpCode::Hlt.into()
      ]
    );

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // LTRI
    let p = Compiler::new("LT $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );

      // Check printing the disassembled program does not cause the program to crash
      dbg!(&p);    

    // LTIR
    let p = Compiler::new("LT 1 $14 ", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63,
        OpCode::Not.into(), EQ as u8, EQ as u8,
        OpCode::Hlt.into(),
      ]
    );

      // Check printing the disassembled program does not cause the program to crash
      dbg!(&p);    

    // LTRR
    let p = Compiler::new("LT $15 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Lt.into(), 15, 14, 
        OpCode::Hlt.into()
      ]
    );

      // Check printing the disassembled program does not cause the program to crash
      dbg!(&p);    
  }

  #[test]
  #[rustfmt::skip]
  fn compile_all_commands() {
    let src = include_str!("../src/test/full_compilation_test.spdr");
    let p = Compiler::new(src, io::stdout()).compile();

    let expected = [
      OpCode::Jmp.into(), 14, 0, 0, 0, // Jump to 14
      // Fn
      OpCode::RvSubRI.into(), 13, 90, 0, 0, 112, 65,
      OpCode::Ret.into(), 3,
      // Basic instructions
      OpCode::Load.into(), 14, 0, 0, 128, 63,
      OpCode::Copy.into(), 14, 16,
      OpCode::Not.into(), 14, 15,
      // Arithmetic
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::MulRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::DivRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::PowRI.into(), 14, 13, 0, 0, 128, 63,
      // Comparisons
      OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 16,
      OpCode::CmpRR.into(), CmpFlag::Gt.into(), 14, 16,
      OpCode::CmpRR.into(), CmpFlag::Lt.into(), 14, 16,
      OpCode::CmpRR.into(), CmpFlag::Geq.into(), 14, 16,
      OpCode::CmpRR.into(), CmpFlag::Leq.into(), 14, 16,
      // Loop
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Jmp.into(), 81, 0, 0, 0, // Jump to 81
      // While loop
      OpCode::Jmp.into(), 115, 0, 0, 0, // Jump to 115
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::CmpRR.into(), CmpFlag::Leq.into(), 14, 16,
      OpCode::Jnz.into(), EQ as u8, 94, 0, 0, 0, // Jump to 94
      // For Loop
      OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
      OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::Noop.into(),
      OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 16, 65,
      OpCode::Jz.into(), EQ as u8, 131, 0, 0, 0, // Jump to 131
      // Memory manipulation
      OpCode::Push.into(), 15,
      OpCode::Pop.into(),
      OpCode::PopR.into(), 14,
      OpCode::WMem.into(), 14, 15, 0, 0, 32, 65, 10,
      OpCode::RMem.into(), 14, 15, 0, 0, 32, 65, 10,
      OpCode::MemCpy.into(), 16, 18,
      OpCode::Alloc.into(), 16, 18,
      OpCode::Dealloc.into(),
      // If
      OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 96, 65,
      OpCode::Jz.into(), EQ as u8, 212, 0, 0, 0, // Jump to 215
      OpCode::Call.into(), 5, 0, 0, 0, // Jump to 5
      // Else If
      OpCode::CmpRI.into(), CmpFlag::Lt.into(), 15, 0, 0, 96, 65,
      OpCode::Jz.into(), EQ as u8, 228, 0, 0, 0, // Jump to 228
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Hlt.into(),
    ];

      // Check printing the disassembled program does not cause the program to crash
      dbg!(&p);

    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  fn test_script_with_while_loop_compiles() {
    //Testing a while loop
    let src = include_str!("../src/test/test_script_while_loop.spdr");
    let mut w = io::stdout();
    let program = Compiler::new(src, &mut w).compile();

    let loop_var = 9.0f32.to_le_bytes();

    let expected = [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      OpCode::Load.into(), 15, 0, 0, 128, 63,
      OpCode::Jmp.into(), 30, 0, 0, 0, 
      OpCode::AddRI.into(), 94, 94, 0, 0, 128, 63,
      OpCode::AddRI.into(), 15, 15, 0, 0, 128, 63, 
      OpCode::CmpRI.into(), CmpFlag::Lt.into(), 15, loop_var[0], loop_var[1], loop_var[2], loop_var[3],
      OpCode::Jnz.into(), EQ as u8, 16, 0, 0, 0, // Jump to 16
      OpCode::Hlt.into(),
    ];
    assert_eq!(program.as_slice(), expected);
    
    // Check printing the disassembled program does not cause the program to crash
    dbg!(&program);

    let mut vm = VM::new();
    vm.upload(program);
    vm.run();

    assert_eq!(vm.reg()[15].as_f32(), 9.0);
  }

  #[test]
  fn test_script_compiles_with_function_calls(){
    // Testing a function called
    let src = include_str!("../src/test/test_script_function.spdr");
    let mut w = io::stdout();
    let program = Compiler::new(src, &mut w).compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&program);

    // Confirm function compiled properly
    let expected = [
      OpCode::Jmp.into(), 21, 0, 0, 0, // Main begins on 21
      OpCode::MulRR.into(), 6, 4, 5,  
      OpCode::AddRI.into(), 6, 6, 16, 88, 244, 65, // [16, 88, 244, 65,] = 30.543
      OpCode::Copy.into(), 4, 6,
      OpCode::Ret.into(), 0, 
      OpCode::Load.into(), 4, 205, 204, 172, 64, 
      OpCode::Load.into(), 5, 80, 141, 83, 65, 
      OpCode::Call.into(), 5, 0, 0, 0, 
      OpCode::Copy.into(), 15, 4,
      OpCode::Hlt.into(),
    ];

    assert_eq!(program.as_slice(), expected);

    // Foo is the equivalent of this function so test against each other 
    fn foo(a:f32, b:f32) -> f32 {
      let mut c = a * b;
      c += 30.543;
      c
    }

    let mut vm = VM::new();
    vm.upload(program);
    vm.run();
  
    assert_eq!(vm.reg()[4].as_f32(), foo(5.4, 13.222));
  }

  #[test]
  fn test_script_compiles_with_external_function(){
    // Test an external function call
    let src = include_str!("../src/test/test_external_script_function.spdr");
    let hed = "";
    let mut compiler = Compiler::new(src, io::stdout());
    // Upload the header file to the compiler
    compiler.read_header(hed);
    let program = compiler.compile();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&program);

    let expected = [];
    
    assert_eq!(program.as_slice(), expected);

    let mut vm = VM::new();
    fn foo(vm:&mut VM, _:&mut dyn Any){
      let a = vm.extern_read(vm.sp().as_u32() as usize).unwrap().as_f32();
      // Add one to read the next lowest entry in the stack because the stack grows downwards
      let b =  vm.extern_read(vm.sp().as_u32() as usize + 1).unwrap().as_f32();

      let c = a * b + 30.543;
      
      // Push c into the VM
      vm.extern_push(c);
    }

    vm.register_extern(foo);


    vm.upload(program);
  }

  #[test]
  fn load_and_run_assembled_script(){
    let program = Program::load("../spdr-assembler/src/test/basic_script_function.spex").unwrap();
    let mut vm = VM::new();

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&program);

    // Confirm function compiled properly
    let expected = [
      OpCode::Jmp.into(), 21, 0, 0, 0, // Main begins on 21
      OpCode::MulRR.into(), 6, 4, 5,  
      OpCode::AddRI.into(), 6, 6, 16, 88, 244, 65, // 30.543.to_le_bytes() = [16, 88, 244, 65,]
      OpCode::Copy.into(), 4, 6,
      OpCode::Ret.into(), 0, 
      OpCode::Load.into(), 4, 205, 204, 172, 64, 
      OpCode::Load.into(), 5, 80, 141, 83, 65, 
      OpCode::Call.into(), 5, 0, 0, 0, 
      OpCode::Copy.into(), 15, 4,
      OpCode::Hlt.into(),
    ];

    assert_eq!(program.as_slice(),expected);
    
    // Run the actual program
    vm.upload(program);
    vm.run();

    // Foo is the equivalent of this function so test against each other 
    fn foo(a:f32, b:f32) -> f32 {
      let mut c = a * b;
      c += 30.543;
      c
    }

    // Check program output
    assert_eq!(vm.reg()[4].as_f32(), foo(5.4, 13.222));
  } 

  // This always has to be at the end. 
  // Because it has foo and bar in different orders and one run of the program shares the same interner
  // it messes up the interned strings for every other test
  #[test]
  #[rustfmt::skip]
  fn compile_multiple_functions_when_one_calls_other_before_other_defined(){
    let mut c = Compiler::new("CALL bar CALL foo FN foo {CALL bar RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar", io::stdout());
    let p = c.compile();
    
    // Check the function pointer of `foo` is correct
    let foo_fn_idx = &intern("foo");
    assert_eq!(foo_fn_idx, &1);
    match c.table.get(foo_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0,]),
      _ => panic!("Should be a function pointer"),
    }

    // Check the function pointer of `bar` is correct
    let bar_fn_idx = &intern("bar");
    assert_eq!(bar_fn_idx, &0);
    match c.table.get(bar_fn_idx){
      Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [12, 0, 0, 0,]),
      _ => panic!("Should be a function pointer"),
    }

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

    // Check the binary is correct
    let expected = [
      OpCode::Jmp.into(),  18, 0, 0, 0, // `main` starts at 24
      // Call bar
      OpCode::Call.into(), 12, 0, 0, 0, // `foo` starts at 5
      OpCode::Ret.into(), 3,
      OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 12
      OpCode::Ret.into(), 2,
      // Call bar
      OpCode::Call.into(), 12, 0, 0, 0,
      // Call foo
      OpCode::Call.into(), 5, 0, 0, 0,
      // Call foo
      OpCode::Call.into(), 5, 0, 0, 0,
      // Call bar
      OpCode::Call.into(), 12, 0, 0, 0,
      OpCode::Hlt.into(),
    ];
    assert_eq!(p.as_slice(), expected);
  }


  impl<'tcx,> Compiler<'tcx,> {
    /// Method created to test `self.eat_current_instruction()` works.
    fn eat_compile(&mut self,) -> Program {
      // Iterate over each each and interpret it as an opcode
      while let Some(_,) = self.next_token() {
        // Match the instruction
        self.eat_current_instruction();
      }
      // Once all lines are compiled return the program
      return self.main.clone();
    }
  }
}
