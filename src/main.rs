mod assembler_errors;
mod compilation_helpers;
mod defered_patch;
mod error_printing;
mod interner;
mod tokenizer;

use assembler_errors::ASMError;
use defered_patch::Linker;
use interner::{intern, lookup};
use spdr_isa::{
  opcodes::OpCode,
  program::Program,
  registers::{FIRST_FREE_REGISTER, REG_COUNT},
};
use std::{
  collections::HashMap, env, fmt::{Debug, Display}, fs::read_to_string, io::{self, Write}, iter::Peekable, usize, vec::IntoIter
};
use tokenizer::{Lexer, Span, Token, TokenKind};

// Refactor:
// - I think there has to be something I can do when parsing a line instead of
//   unwrapping next. It would be better to handle the `Option`. Probably as
//   simple as returning an error if the unwrap fails that says expected X/Y/Z
//   tokens
// - Currently all variables are global. Each scope (block and function def)
//   should recieve its own symbol table to prevent this
// - Eventually I should sub out usizes and choose some number that is platform
//   independent
// - I think there has to be a better way of storing the src to print than
//   storing it in the compiler like that. maybe just intern the whole thing and
//   reference it that way
// - Does the iterator need to be peekable? Do I ever use peeking?
// - Need to add a halt before the fns are placed in the binary.
// - Need to store the fns and them stick them at the end, get their location
//   and patch
// - `compile_block_return` can be implemented way more efficiently
// - Currently All identifiers must be unique. I am not actually sure this
//   bothers me.

// TODO:
// - Jump instructions should accept labels as arguments
// - Add array compilation
// - Add note to opcodes that all immediates are 4bytes unless otherwise stated.
//   Then state otherwise.

// Compiler Rules
// - Names must be unique
// - LOOP/WHILE/FOR must have their own lines
// - The beginning and end of blocks need their own lines
// - All variables are global

fn main() {
  let args = env::args().collect::<Vec<String,>>();
  let path = args[1].trim();
  let src = read_to_string(path,).unwrap();
  let mut compiler = Compiler::new(&src,io::stdout());
  if let Some(header,) = args.get(3,) {
    compiler.read_header(header.trim(),);
  }

  let program = compiler.compile();

  // If an output is specifed place the file there. Otherwise place it in the
  // current directory
  if let Some(output,) = args.get(2,) {
    program.save(output.trim(),).unwrap();
  }
  else {
    // Get the name of the file
    // Update it to have the exe ending
    let output = &format!("{}.spex", src.split(['\\', '.',],).rev().nth(1,).unwrap());
    program.save(output,).unwrap();
  }
}

#[derive(Debug, Clone, Copy,)]
//JUMP AND JNZ will never take a Register as an arg.
enum Ty {
  /// Registers hold the index of their assigned register
  Register(usize,),
  /// Labels hold the index number the label references.
  Label(usize,),
  /// Functions hold the [`Patch`](defered_patch::Patch) index of a function's address and a `bool` indicating whether it has been definined yet.
  // Function(usize, bool),
  Function(usize),
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

#[derive(Debug, Clone,)]
struct Compiler<'tcx,> {
  tokens:Peekable<IntoIter<Token,>,>,
  /// The Symbol Table for the currently compiling program.
  table:HashMap<u32, VarDecl,>,
  open:u8,
  /// The locations to [`Patch`](defered_patch::Patch) into the
  /// program once compilation of the source is finished.
  linker:Linker,
  /// Stores the index of the next register available for register allocation.
  /// The portion of the binary where function definitions are stored. 
  lib:Program,
  /// The body of the binary's "`main`" function.
  main:Program,
  /// The [`Token`] the compiler is currently reading.
  current_instruction:Option<Token,>,
  _str:&'tcx str,
}
impl<'tcx,> Compiler<'tcx,> {
  /// Create a new empty compiler without a file.
  fn new<W:Write>(src:&'tcx str, mut w:W) -> Self {
    Self {
      tokens:Lexer::new(src,).tokenize(&mut w).into_iter().peekable(),
      table:HashMap::new(),
      linker:Linker::new(),
      lib:Program::new(),
      main:Program::new(),
      open:FIRST_FREE_REGISTER as u8,
      current_instruction:None,
      _str:src,
    }
  }

  /// Returns the [`TokenKind`] of the instruction currently being compiled.
  fn current_instruction_kind(&self,) -> TokenKind {
    self.current_instruction.unwrap().kind
  }

  /// Returns the next [`Token`] in the `src`.
  fn next_token(&mut self,) -> Option<Token> {
    self.current_instruction =  self.tokens.next();
    self.current_instruction
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
          .insert(sym_idx, VarDecl::new(Ty::Register(reg as usize,),),);
      }
      _ => panic!("Tried to make a non identifier {} into a variable", ident.kind),
    }
    reg
  }

  // /// Adds an identifier to the [`Compiler`]'s Symbol Table as a
  // /// [`Ty::Label`].
  // fn add_as_label(){}

  // /// Adds an identifier to the [`Compiler`]'s Symbol Table as a
  // /// [`Ty::Function`].
  // fn add_as_function(){}

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
          self.current_instruction.unwrap().kind
        )
      }
    }
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
    // Compile `main` -- iterate over each each and interpret it as an opcode
    while let Some(instruction,) =  self.next_token() {
      self.current_instruction = Some(instruction,);
      // Match the instruction
      self.compile_current_instruction();
    }

    // Get the len of the `lib` + 4 which is the offset of the `main`
    let offset = self.lib.len() + 5;

    // Patch the linker locations and the function definition into the binary
    self.linker.link(&mut self.main, &self.lib);

    // Create the output binary
    let mut out = Program::from(Vec::with_capacity(offset + self.main.len()));
    out.push(OpCode::Jmp.into());
    out.extend_from_slice(&(offset as f32).to_le_bytes());
    out.extend_from_slice(self.lib.as_slice());
    out.extend_from_slice(self.main.as_slice()); 
    // Append the halt command to the `main` binary
    out.push(OpCode::Hlt.into(),);

    // Once all lines are patched and linking has completed return the program
    return out;
  }

  /// Consume and discard the current intruction in the program.
  fn eat_current_instruction(&mut self,) {
    match self.current_instruction.unwrap().kind {
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
        return match self.tokens.peek().unwrap().kind {
          TokenKind::LCurlyBracket => self.eat_block(),
          // Doing nothing here will make it continue compiling the program which is what we want
          _ => {}
        };
      }
      _ => panic!(
        "{}",
        ASMError::NotAnOpcode{ token: self.current_instruction.unwrap() }
         
        
      ),
    }
  }

  #[rustfmt::skip]
  /// Compile the next intruction in the program.
  fn compile_current_instruction(&mut self,) {
    match self.current_instruction_kind() {
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
      TokenKind::Const | TokenKind::Var => {
        // Add the next token to the symbol table assuming it is an ident
        let ident =  self.next_token().unwrap();
        let reg = self.add_as_reg(ident,);

        // Eat the `=` sign
        if TokenKind::EqualSign !=  self.next_token().unwrap().kind {
          panic!("{}", ASMError::NoEquals(self.current_instruction_kind()))
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
        let op = self.current_instruction.unwrap();
        let a =  self.next_token().unwrap();
        let b =  self.next_token().unwrap();
        self.compile_comparison(&op, &a, &b,);
      }
      TokenKind::Loop => self.compile_loop_expr(),
      TokenKind::While => self.compile_while_loop_expr(),
      TokenKind::For => self.compile_for_loop_expr(),
      TokenKind::If => self.compile_if_body_expr(),
      TokenKind::Else => {
        let next_operation = *self.tokens.peek().unwrap();
        // If the "instruction" starts with a bracket, compile block should be called
        return match next_operation.kind {
          TokenKind::LCurlyBracket => self.compile_block(),
          // Doing nothing here will make it continue compiling the program which is what we want
          _ => {}
        };
      }
      TokenKind::Fn => {
        // Store the name in the symbol table
        let name = match  self.next_token().unwrap() {
          Token { kind:TokenKind::Identifier(name,) , .. } => name,
          other => panic!("{}", ASMError::MissingFnName{token:other}),
        };

        // Create a function declaration and store it in the symbol table
        match self.table.get(&name,) {
          // If there are function invocations but no use
          Some(&VarDecl { ty:Ty::Function(patch_idx) }) => {
            // The function pointer's address must be added to the linker before the body is compiled 
            // This is to ensure the declaration is accessible to any recursive calls in the body
            // Get the function pointer
            let ptr = self.next_function_pointer();
            // Try to update the patch's address
            if self.linker.update_function_pointer(patch_idx, ptr).is_err(){
              panic!("Function is already definied.\n{}", ASMError::UnavailableFunctionName(&lookup(name)))
            }
            // Compile the function body
            let body = self.compile_block_return();
            // Store the function in `lib` 
            self.store_function(body);
          }
          // If there is no declaration make a new one
          None => {
            // The function pointer's address must be added to the linker before the body is compiled 
            // This is to ensure the declaration is accessible to any recursive calls in the body
            // Get the function pointer
            let ptr = self.next_function_pointer();
            // Store the pointer in the linker 
            let patch_idx = self.linker.reserve();
            self.linker.update_function_pointer(patch_idx, ptr).unwrap();

            // Store the new declaration in the symbol table
            self.table.insert(name, VarDecl { ty: Ty::Function(patch_idx) });   
            
            // Compile the function body
            let body = self.compile_block_return();
            // Record the function in `lib` and get the pointer
            self.store_function(body);         
          }
          // Error if there is already a symbol table entry for the identifier
          _ => panic!("{}", ASMError::UnavailableFunctionName(&lookup(name))),
        }
      }
      TokenKind::Call => {
        let name = match self.next_token().unwrap() {
          Token { kind: TokenKind::Identifier(name,), .. } => name,
          other => panic!("{}", ASMError::NoNameCall { token: other }),
        };
        // Place the Call opcode in the function
        self.main.push(OpCode::Call.into(),);

        match self.table.get(&name){
          // If the function already has a symbol table entry attempt to retrieve its pointer
          Some(VarDecl { ty: Ty::Function(patch_idx)}) => {
            match self.get_function_pointer(patch_idx) {
              // Add the pointer to the program
              Some(ptr) => self.main.extend_from_slice(&ptr,),
              // Reserve a patch site for later linking
              None => self.linker.insert_patch_site(*patch_idx, &mut self.main),
            }
          },
          // If the function does not have a symbol table entry, create one
          None => {
            let patch_idx = self.linker.reserve();
            // Reserve a patch site for later linking            
            self.linker.insert_patch_site(patch_idx, &mut self.main);
            // Generate an empty function symbol table entry to fill when the function definition is encountered
            self.table.insert(name, VarDecl { ty: Ty::Function(patch_idx) });
          },
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
        let op = match self.current_instruction_kind() {
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
        let pop_number = self.next_token_as_immediate_array();
        self.main.extend_from_slice(&[ OpCode::Ret.into(), pop_number[0], pop_number[1], pop_number[2], pop_number[3],],);
      }
      TokenKind::Eof => {}
      _ => panic!(
        "{}",
        ASMError::NotAnOpcode { token: self.current_instruction.unwrap() }
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
      self.current_instruction = Some(instruction,);
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
      if self.current_instruction_kind() == TokenKind::RCurlyBracket {
        // Does not need to eat the block because the compile function will call the
        // next token
        break;
      }
      self.compile_current_instruction()
    }
  }

  /// Compile the next block in the program and return the restule as a
  /// [`Program`].
  fn compile_block_return(&mut self,) -> Program {
    // Store the real program 
    let original_program = self.main.clone();
    // Compile the block into a new program
    self.main = Program::new();
    // Compile the block
    self.compile_block();
    // Store the block's program
    let block = self.main.clone();
    // Place the real program back into the compiler
   self.main = original_program;
   block    
  }
}

#[cfg(test)]
mod test {
  use std::io;

use crate::{defered_patch::Region, interner::intern, Compiler, Ty, VarDecl};
  use spdr_isa::{
    opcodes::{CmpFlag, OpCode},
    program::Program,
    registers::{EQ, LOOP},
  };

  // TODO: (I believe right now it is currently just unreachable)

  #[test]
  fn load_header() {
    let mut compiler = Compiler::new("",io::stdout());
    compiler
      .read_header("C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\spdr-assembler\\src\\test_header.hd",);

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
  #[rustfmt::skip]
  fn compile_load_cpy() {
    let p = Compiler::new("Load $14 1 Copy $15 $12",io::stdout()).compile();

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::Load.into(), 14, 0, 0, 128, 63,
        OpCode::Copy.into(), 15, 12,
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_memcpy_rmem_wmem() {
    let p = Compiler::new("wmem $14 $15 1 $16 memcpy $55 $50 rmem $255 $40 1 $20",io::stdout()).compile();

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::WMem.into(), 14, 15, 0, 0, 128, 63, 16,
        OpCode::MemCpy.into(), 55, 50,
        OpCode::RMem.into(), 255, 40, 0, 0, 128, 63, 20,
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_alloc_dealloc() {
    let p = Compiler::new("Alloc $14 $90 Dealloc", io::stdout()).compile();

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::Alloc.into(), 14,   90,
        OpCode::Dealloc.into(),
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  fn compile_arith() {
    // ADDII
    let p = Compiler::new("ADD $14 15 10", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), 14, 0, 0, 200, 65, 
        OpCode::Hlt.into(),
      ]
    );

    // ADDRI
    let p = Compiler::new("ADD $14 $15 10", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::AddRI.into(), 14, 15, 0, 0, 32, 65, 
        OpCode::Hlt.into(),]
    );

    // ADDRR
    let p = Compiler::new("ADD $14 $14 $15", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::AddRR.into(), 14, 14, 15, 
        OpCode::Hlt.into(),
      ]
    );

    // SUBII
    let p = Compiler::new("SUB $14 10 30", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), 14, 0, 0, 160, 193, 
        OpCode::Hlt.into(),
      ]
    );

    // SUBIR
    let p = Compiler::new("SUB $15 90 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::RvSubRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // SUBRI
    let p = Compiler::new("SUB $15 $14 90", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::SubRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // SUBRR
    let p = Compiler::new("SUB $15 $14 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::SubRR.into(), 15, 14, 14, 
        OpCode::Hlt.into(),
      ]
    );

    // MULII
    let p = Compiler::new("MUL $14 10 29.32", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), 14, 154, 153, 146, 67, 
        OpCode::Hlt.into(),
      ]
    );

    // MULRI
    let p = Compiler::new("MUL $15 $14 10", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::MulRI.into(), 15, 14, 0, 0, 32, 65, 
        OpCode::Hlt.into(),
      ]
    );

    // MULRR
    let p = Compiler::new("MUL $15 $14 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::MulRR.into(), 15, 14, 14, 
        OpCode::Hlt.into(),
      ]
    );

    // DIVII
    let p = Compiler::new("DIV $14 32.54 653", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), 14, 42, 28, 76, 61, 
        OpCode::Hlt.into(),
      ]
    );

    // DIVRI
    let p = Compiler::new("DIV $15 $14 90", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::DivRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // DIVIR
    let p = Compiler::new("DIV $15 90 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::RvDivRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // DIVRR
    let p = Compiler::new("DIV $15 $14 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::DivRR.into(), 15, 14, 14, 
        OpCode::Hlt.into(),
      ]
    );

    // POWII
    let p = Compiler::new("POW $14 76.253216 3.7", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), 14, 127, 144, 12, 75, 
        OpCode::Hlt.into(),
      ]
    );

    // POWRI
    let p = Compiler::new("POW $15 $14 90", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::PowRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // POWIR
    let p = Compiler::new("POW $15 90 $14",io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::RvPowRI.into(), 15, 14, 0, 0, 180, 66, 
        OpCode::Hlt.into(),
      ]
    );

    // PowRR
    let p = Compiler::new("POW $15 $14 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::PowRR.into(), 15, 14, 14, 
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_loop() {
    // Test plain loop compilation
    let mut c = Compiler::new("Loop {ADD $14 $30 1}", io::stdout());
    let p = c.compile();

    // Check the initial jump target pre-linking was correct
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 0);
    // Check the output is accurate
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
        OpCode::Jmp.into(), 0, 0, 160, 64, // Jump to 4
        OpCode::Hlt.into()
      ]
    );

    // Test plain loop compilation with function at beginning
    let mut c = Compiler::new("Loop {ADD $14 $30 1} FN foo {SUB $16 $94 $233 RET 1}", io::stdout());
    let p = c.compile();

    // Check the initial jump target pre-linking was correct
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 0);
    // Check the output is accurate
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 96, 65, // `main` starts on *14
        OpCode::SubRR.into(), 16, 94, 233,
        OpCode::Ret.into(), 0, 0, 128, 63,
        OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
        OpCode::Jmp.into(), 0, 0, 96, 65,  // Jump to *14
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_while_loop(){
    // Test while loop compilation when `true`
    let mut c = Compiler::new("while true {noop noop noop}",io::stdout());
    let p = c.compile();

    // Check the initial jump target pre-linking was correct
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 0);
    // Check the output is accurate
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Jmp.into(), 0, 0, 160, 64, 
        OpCode::Hlt.into(),
      ]
    );

    // Test While loop compilation when `false`
    let p = Compiler::new("while false {noop noop noop}", io::stdout()).compile();
    assert_eq!(p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::Hlt.into(),
      ]
    );

    // Test While loop compilation with real condition
    let mut c = Compiler::new("while EQ $15 1 {noop noop noop}", io::stdout());
    let p = c.compile();

    // Check jump to the initial jump to the condition is correct
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 8);
    // Check jump to the initial jump to 5
    assert_eq!(c.linker.jmp_targets[1].value.unwrap(), 5);

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 4
        OpCode::Jmp.into(), 0, 0, 80, 65, // Jump to 13
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
        OpCode::Jnz.into(), EQ as u8, 0, 0, 32, 65, // Jump to 10
        OpCode::Hlt.into()
      ]
    );

    // Test While loop compilation with real condition
    let mut c = Compiler::new("WHILE EQ $15 1 {ADD $15 $15 $54 } FN foo {NOOP NOOP}", io::stdout());
    let p = c.compile();

    // Check jump to the initial jump to the condition is correct
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 9);
    // Check jump to the initial jump to 5
    assert_eq!(c.linker.jmp_targets[1].value.unwrap(), 5);

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 224, 64, // `main` starts on 7
        // foo
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        // Main 
        OpCode::Jmp.into(), 0, 0, 128, 65,// Jump to 16
        OpCode::AddRR.into(), 15, 15, 54,
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
        OpCode::Jnz.into(), EQ as u8, 0, 0, 64, 65, // Jump to 12
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_for_loop(){
    // Test For loop compilation
    let mut c = Compiler::new("for i in 0..9 {noop noop noop}", io::stdout());
    let p = c.compile();   

    // Confirm the jump target has the correct pre-link value
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 6);
    // Confirm the region to be replaced is correct
    assert_eq!(c.linker.jmp_targets[0].region, Region{ start: 25, end: 29 });
    // Check the output is accurate
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
        OpCode::Jz.into(), EQ as u8, 0, 0, 48, 65, // Jump to 11
        OpCode::Hlt.into(),
      ]
    );

    // Test for loop compiles when binary has function
    let mut c = Compiler::new("FOR i IN 0..9 {NOOP NOOP NOOP} FN foo {NOOP NOOP}", io::stdout());
    let p = c.compile();  

    // Confirm the jump target has the correct pre-link value
    assert_eq!(c.linker.jmp_targets[0].value.unwrap(), 6);
    // Confirm the region to be replaced is correct
    assert_eq!(c.linker.jmp_targets[0].region, Region{ start: 25, end: 29 });
    // Check the output is accurate
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 224, 64, // `main` starts on 7
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
        OpCode::Jz.into(), EQ as u8, 0, 0, 80, 65, // Jump to 13
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_if_else() {
    // Compile IF with boolean true check
    // Compile ELSE
    let p = Compiler::new("IF true {Noop Noop Noop Noop} else {Add $15 0 1} Mul $16 1 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Load.into(), 16, 0, 0, 128, 63, 
        OpCode::Hlt.into(),
      ]
    );

    // Compile IF with boolean false check
    let p = Compiler::new("IF false {mul $54 0 1 } else {add $26 $17 1} add $46 0 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        // Else Block
        OpCode::AddRI.into(), 26, 17, 0, 0, 128, 63,
        // Trailing expression
        OpCode::Load.into(), 46, 0, 0, 128, 63,
        OpCode::Hlt.into(),
      ]
    );

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
        OpCode::Jmp.into(), 0, 0, 160, 64, // `main` starts on 5
        // IF expression
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 0, 0,
        OpCode::Jz.into(), EQ as u8, 0, 0, 176, 65, // Jump to idx 22 if the comparison fails
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        // ELSE expression
        OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 128, 63,
        OpCode::Jz.into(), EQ as u8, 0, 0, 48, 66, // Jump to idx 44 if the comparison fails
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
  fn compile_when_defined(){
    let mut c = Compiler::new("Sub $54 $34 $65 fn foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(patch_idx) }) => assert_eq!(*patch_idx, 0),
      _ => panic!("Should be a function pointer"),
    }
    
    // Check the program is correct
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 152, 65, // `main`'s address is *19
        // Beginning of `lib`
        OpCode::AddRR.into(), 14, 14, 15,
        OpCode::Noop.into(),
        OpCode::MulRR.into(), 88, 87, 98,
        OpCode::Ret.into(), 0, 0, 0, 0,
        // Beginning of `main`
        OpCode::SubRR.into(), 54, 34, 65,
        OpCode::DivRR.into(), 65, 58, 30,
        OpCode::Hlt.into(),
      ]
    );

    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(patch_idx) }) => assert_eq!(*patch_idx, 0),
      _ => panic!("Should be a function pointer"),
    }
  }

  #[test]
  #[rustfmt::skip]
  fn compile_call_when_fn_defined_before(){
    let mut c = Compiler::new("Sub $54 $34 $65 fn foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(patch_idx) }) => assert_eq!(*patch_idx, 0),
      _ => panic!("Should be a function pointer"),
    }
      
    // Check the program is correct
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 152, 65, // `main`'s address is *19
        // Beginning of `lib`
        OpCode::AddRR.into(), 14, 14, 15,
        OpCode::Noop.into(),
        OpCode::MulRR.into(), 88, 87, 98,
        OpCode::Ret.into(), 0, 0, 0, 0,
        // Beginning of `main`
        OpCode::SubRR.into(), 54, 34, 65,
        OpCode::DivRR.into(), 65, 58, 30,
        OpCode::Call.into(), 0, 0, 160, 64, // Call 5
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_fn_defined_after_call(){
    let mut c = Compiler::new("CALL foo SUB $54 $34 $65 CALL foo FN foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(patch_idx) }) => assert_eq!(*patch_idx, 0),
      _ => panic!("Should be a function pointer"),
    }

    // Check region information is correct
    let regions = c.linker.inner[0].regions().clone();
    // There should be two elements in region as the `Call` after the definition should use the concrete pointer
    assert_eq!(regions.len(), 2);
    // Regions should be 1..5 and 10..14
    // *after* 18 is added to them since they are calculated relative to `compiler.main` during compilation
    assert_eq!((regions[0].start, regions[0].end), (1, 5));
    assert_eq!((regions[1].start, regions[1].end), (10, 14));

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 152, 65, // `main`'s address is 24
        // Beginning of `lib`
        OpCode::AddRR.into(), 14, 14, 15,
        OpCode::Noop.into(),
        OpCode::MulRR.into(), 88, 87, 98,
        OpCode::Ret.into(), 0, 0, 0, 0,
        // Beginning of `main`
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::SubRR.into(), 54, 34, 65,
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::DivRR.into(), 65, 58, 30,
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_when_fn_contains_recursion(){
    let mut c = Compiler::new("CALL foo FN foo {ADD $14 $14 $15 CALL foo NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
    let p = c.compile();
    // Check the function pointer of `foo` is correct
    match c.table.get(&intern("foo")){
      Some(VarDecl{ ty: Ty::Function(patch_idx) }) => assert_eq!(*patch_idx, 0),
      _ => panic!("Should be a function pointer"),
    }

    // Check region information is correct
    let regions = c.linker.inner[0].regions().clone();
    // There should be 1 element in Patch 
    // - The `Call` after the definition should use the concrete pointer
    // - The recursive call should use the concrete pointer
    assert_eq!(regions.len(), 1);
    assert_eq!(regions[0], Region{start:1, end:5});

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 192, 65, // `main`'s address is 24
        // Beginning of `lib`
        OpCode::AddRR.into(), 14, 14, 15,
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::Noop.into(),
        OpCode::MulRR.into(), 88, 87, 98,
        OpCode::Ret.into(), 0, 0, 0, 0,
        // Beginning of `main`
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::DivRR.into(), 65, 58, 30,
        OpCode::Call.into(), 0, 0, 160, 64, // Call 4
        OpCode::Hlt.into(),
      ]
    );

  }

  #[test]
  #[rustfmt::skip]
  #[should_panic = "\x1b[93mUNAVAILABLE FUNCTION NAME:\x1b[0m The name foo is already in use."]
  fn function_panics_when_name_in_use() {
  

    // Test fuction name reuse fails
    let _ = Compiler::new("FN foo {ADD $14 $14 4} FN foo {NOOP NOOP}", io::stdout()).compile();
  }

  #[test]
  #[rustfmt::skip]
  fn compile_syscall() {
    // TODO: Make it so syscalls can also be called using "call"
    let mut compiler = Compiler::new("syscall foo", io::stdout());
    compiler
      .read_header("C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\spdr-assembler\\src\\test_header.hd",);

    let p = compiler.compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::SysCall.into(), 0,
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_push_pop() {
    let p = Compiler::new("Push $1 Push $1 Pop PopR $16", io::stdout()).compile();

    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Push.into(), 1, 
        OpCode::Push.into(), 1,
        OpCode::Pop.into(),
        OpCode::PopR.into(), 16,
        OpCode::Hlt.into(),
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_eq() {
    // EQII
    let p = Compiler::new("eq 2 2", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
        OpCode::Hlt.into()
      ]
    );
    // EQIR
    let p = Compiler::new("eq $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );
    // EQRR
    let p = Compiler::new("eq $14 $15", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 15, 
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_geq(){
    // GEQII
    let p = Compiler::new("geq 4 2", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
        OpCode::Hlt.into()
        ]
      );
    // GEQRI
    let p = Compiler::new("geq $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );
    // GEQIR
    let p = Compiler::new("geq 1 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63,
        OpCode::Not.into(), EQ as u8, EQ as u8,
        OpCode::Hlt.into(),
      ]
    );
    // GEQRR
    let p = Compiler::new("geq $15 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Geq.into(), 15, 14, 
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_leq(){
    // LEQII
    let p = Compiler::new("leq 4 2", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, OpCode::Hlt.into()
      ]
    );
    // LEQRI
    let p = Compiler::new("leq $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );
    // LEQIR
    let p = Compiler::new("leq 1 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63,
        OpCode::Not.into(), EQ as u8, EQ as u8,
        OpCode::Hlt.into(),
      ]
    );
    // LEQRR
    let p = Compiler::new("leq $15 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Leq.into(), 15, 14, 
        OpCode::Hlt.into()
      ]
    );
  }
  
  #[test]
  #[rustfmt::skip]
  fn compile_gt(){
    // GTII
    let p = Compiler::new("gt 4 2", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
        OpCode::Hlt.into()
      ]);
    // GTRI
    let p = Compiler::new("gt $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );
    // GTIR
    let p = Compiler::new("gt 1 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63,
        OpCode::Not.into(), EQ as u8, EQ as u8,
        OpCode::Hlt.into(),
      ]
    );
    // GTRR
    let p = Compiler::new("gt $15 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Gt.into(), 15, 14, 
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  #[rustfmt::skip]
  fn compile_lt(){
    // LTII
    let p = Compiler::new("LT 2 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, 
        OpCode::Hlt.into()
      ]
    );

    // LTRI
    let p = Compiler::new("LT $14 1", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63, 
        OpCode::Hlt.into()
      ]
    );

    // LTIR
    let p = Compiler::new("LT 1 $14 ", io::stdout()).compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63,
        OpCode::Not.into(), EQ as u8, EQ as u8,
        OpCode::Hlt.into(),
      ]
    );

    // LTRR
    let p = Compiler::new("LT $15 $14", io::stdout()).compile();
    assert_eq!(
      p.as_slice(), 
      [
        OpCode::Jmp.into(), 0, 0, 160, 64, // main starts on 5
        OpCode::CmpRR.into(), CmpFlag::Lt.into(), 15, 14, 
        OpCode::Hlt.into()
      ]
    );
  }

  #[test]
  fn eat_instruction_works() {
    let src = include_str!("full_compilation_test.spdr");
    let p = Compiler::new(src, io::stdout()).eat_compile();
    assert_eq!(p.as_slice(), []);
  }

  #[test]
  #[rustfmt::skip]
  fn compile_all_commands() {
    let src = include_str!("full_compilation_test.spdr");
    let p = Compiler::new(src, io::stdout()).compile();


    let expected = [
      OpCode::Jmp.into(), 0, 0, 136, 65, // Jump to 17
      // Fn
      OpCode::RvSubRI.into(), 13, 90, 0, 0, 112, 65,
      OpCode::Ret.into(), 0, 0, 64, 64,
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
      OpCode::Jmp.into(), 0, 0, 168, 66, // Jump to 84
      // While loop
      OpCode::Jmp.into(), 0, 0, 236, 66, // Jump to 118
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::CmpRR.into(), CmpFlag::Leq.into(), 14, 16,
      OpCode::Jnz.into(), EQ as u8, 0, 0, 194, 66, // Jump to 97
      // For Loop
      OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
      OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::Noop.into(),
      OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
      OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 16, 65,
      OpCode::Jz.into(), EQ as u8, 0, 0, 6, 67, // Jump to 134
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
      OpCode::Jz.into(), EQ as u8, 0, 0, 87, 67, // Jump to 215
      OpCode::Call.into(),  0, 0, 160, 64, // Jump to 9
      // Else If
      OpCode::CmpRI.into(), CmpFlag::Lt.into(), 15, 0, 0, 96, 65,
      OpCode::Jz.into(), EQ as u8,  0, 0, 103, 67, // Jump to 231
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Hlt.into(),
    ];

    // Do an assert
    assert_eq!(p.as_slice(), expected);
  }

  #[test]
  fn execute_simple_scripts() {
    todo!("Test scripts execute in the VM, some modifications will be needed to brin the VM in line with the new ISA")
  }

  impl<'tcx,> Compiler<'tcx,> {
    /// Method created to test `self.eat_current_instruction()` works.
    fn eat_compile(&mut self,) -> Program {
      // Iterate over each each and interpret it as an opcode
      while let Some(instruction,) = self.next_token() {
        self.current_instruction = Some(instruction,);
        // Match the instruction
        self.eat_current_instruction();
      }

      let mut out = self.main.clone();
      self.linker.link(&mut out, &self.lib);
      // Once all lines are compiled return the program
      return out;
    }
  }
}
