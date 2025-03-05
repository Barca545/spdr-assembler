#![feature(stmt_expr_attributes)]
mod assembler_errors;
mod defered_patch;
mod error_printing;
mod interner;
mod tokenizer;
mod compilation_helpers;

use assembler_errors::ASMError;
use defered_patch::DeferredPatches;
use interner::{intern, lookup};
use spdr_isa::{
  program::Program,
  registers::{EQ, REG_COUNT},
  opcodes::OpCode,
};
use std::{
  collections::HashMap,
  env,
  fmt::{Debug, Display},
  fs::read_to_string,
  iter::Peekable,
  usize,
  vec::IntoIter,
};
use tokenizer::{Lexer, Span, Token, TokenKind};

// Refactor:
// - I think there has to be something I can do when parsing a line instead of
//   unwrapping next. It would be better to handle the `Option`. Probably as
//   simple as returning an error if the unwrap fails
// - Currently all variables are global. Each scope (block and function def)
//   should recieve its own symbol table to prevent this
// - Compile for condition needs to handle if a variable (register) is used
// - Eventually I should sub out usizes and choose some number that is platform
//   independent
// - Should I update the compile line thing so it appends directly to the
//   Compiler's self instead of an internal program?
// - Do VarDecls need the Symbol attached to them?
// - Confirm the process for finding a register in Wmem isn't reused. If it is
//   reused, convert it into a function
// - use self.next instead of tokens.next
// - I think there has to be a better way of storing the src to print than storing it in the compiler like that. maybe just intern the whole thing and reference it that way
// - Does the iterator need to be peekable? Do I ever use peeking?

// TODO:
// - Ensure each branch also adds the correct opcode
// - Only jump instructions should accept labels as arguments
// - Add dbg implementation for a Program type that prints arguments in LE form
//   as normal u32
// - Update how the loop's return address works. Making it only a u8 is
//   limiting. Jumps should take 4byte arguments.
// - Register Allocation needs to factor in the offset caused by the reserved
//   registers

// Compiler Rules
// - Names must be unique
// - LOOP/WHILE/FOR must have their own lines
// - The beginning and end of blocks need their own lines
// - All variables are global

fn main() {
  let args = env::args().collect::<Vec<String,>>();

  let path = args[1].trim();

  let src = read_to_string(path).unwrap();

  dbg!(&src);

  let mut compiler = Compiler::new(&src,);

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
  /// Functions hold the index of the program where they were defined.
  Function {
    function_addr:Option<usize,>,
    patch_index:Option<usize,>,
  },
  /// Functions hold the index the VM where stores them in its collection of
  /// external functions.
  ExternalFunction(u8,),
}

impl Display for Ty {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    match self {
      Ty::Register(v,) => write!(f, "Reg({})", v),
      Ty::Label(v,) => write!(f, "Label({})", v),
      Ty::Function {
        function_addr,
        patch_index,
      } => write!(
        f,
        "Function(function_addr:{:?}, patch_index: {:?})",
        function_addr, patch_index
      ),
      Ty::ExternalFunction(idx,) => write!(f, "ExternalFunction({idx})"),
    }
  }
}

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

struct Compiler<'tcx,> {
  /// The Symbol Table for the currently compiling program.
  table:HashMap<u32, VarDecl,>,
  tokens:Peekable<IntoIter<Token,>,>,
  /// The locations to [`Patch`](defered_patch::Patch) into the
  /// program once compilation of the source is finished.
  deferred:DeferredPatches,
  /// Stores the index of the next register available for register allocation.
  open:u8,
  /// Currently compiled Program excluding the instruction being compiled.
  program:Program,
  current_instruction:Option<Token,>,
  _str:&'tcx str,
}
impl<'tcx,> Compiler<'tcx,> {
  /// Create a new empty compiler without a file.
  fn new(src:&'tcx str) -> Self {
    Self {
      table:HashMap::new(),
      tokens:Lexer::new(src).tokenize().into_iter().peekable(),
      deferred:DeferredPatches::new(),
      program:Program::new(),
      open:13,
      current_instruction:None,
      _str:src,
    }
  }

  /// Returns the [`TokenKind`] of the instruction currently being compiled.
  fn current_instruction_kind(&self,) -> TokenKind {
    self.current_instruction.unwrap().kind
  }

  /// Returns the [`Span`] of the instruction currently being compiled.
  fn current_instruction_span(&self,) -> Span {
    self.current_instruction.unwrap().span
  }

  /// Returns the next [`Token`] in the `src`.
  fn next_token(&mut self,) -> Token {
    self.current_instruction = self.tokens.next();
    self.current_instruction.unwrap()
  }

  /// Consume the next `n` [`Token`]s in the `src`.
  fn eat_tokens(&mut self, n:usize){
    for _ in 0..n{
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
      None => panic!(
        "{}",
        ASMError::UndeclaredIdentifier(&lookup(name), span.start)
      ),
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
    match self.tokens.next().unwrap() {
      Token {
        kind: TokenKind::Num(val,),
        ..
      } => val.to_le_bytes(),
      Token {
        kind: TokenKind::Bool(val,),
        ..
      } => (val as u32 as f32).to_le_bytes(),
      other => panic!(
        "{}",
        ASMError::InvalidImmediateType(other.kind, other.span.start)
      ),
    }
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Register`], return
  /// it as a `u8`.
  fn next_token_as_register(&mut self,) -> u8 {
    match self.next_token() {
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
      other => panic!(
        "{}",
        ASMError::NotRegisterOrIdent(other.kind, other.span.start)
      ),
    }
  }

  /// Compiles the .spdr file loaded into the compiler into a .spex executable
  /// file.
  fn compile(&mut self,) -> Program {
    // Iterate over each each and interpret it as an opcode
    while let Some(instruction,) = self.tokens.next() {
      self.current_instruction = Some(instruction,);
      // Match the instruction
      self.compile_current_instruction();
    }

    let mut out = self.program.clone();
    self.deferred.patch(&mut out,);

    // Once all lines are compiled return the program
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
        match self.next_token().kind {
          TokenKind::Eq | TokenKind::Gt | TokenKind::Geq | TokenKind::Lt | TokenKind::Leq => self.eat_tokens(2,),
          TokenKind::Bool(_,) => {}
          other => panic!("{}", ASMError::NotEquality(other,)),
        }
        self.eat_block();
      }
      TokenKind::For => {
        self.eat_tokens(3);
        self.eat_block()},
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
        ASMError::NotAnOpcode(
          self.current_instruction_kind(),
          self.current_instruction_span().start
        )
      ),
    }
  }

  /// Compile the next intruction in the program.
  fn compile_current_instruction(&mut self,) {
    match self.current_instruction.unwrap().kind {
      TokenKind::Load => {
        let reg = self.next_token_as_register();

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        self.program.extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Copy => {
        let dst =  self.next_token_as_register();
        let src = self.next_token_as_register();
        self.program.extend_from_slice(&[
        OpCode::Copy.into(),
        dst,
        src,
      ],)},
      TokenKind::Const | TokenKind::Var => {
        // Add the next token to the symbol table assuming it is an ident
        let ident = self.tokens.next().unwrap();
        let reg = self.add_as_reg(ident,);

        // Eat the `=` sign
        if TokenKind::EqualSign != self.tokens.next().unwrap().kind {
          panic!("{}", ASMError::NoEquals(self.current_instruction_kind()))
        }

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        self.program.extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Add => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_add_expr(&target, &a, &b,)
      }
      TokenKind::Sub => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_sub_expr(&target, &a, &b,)
      }
      TokenKind::Mul => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_mul_expr(&target, &a, &b,)
      }
      TokenKind::Div => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_div_expr(target, &a, &b,)
      }
      TokenKind::Pow => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_pow_expr(&target, &a, &b,)
      }
      TokenKind::Not => {
        let dst = match self.tokens.next().unwrap() {
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

        match self.tokens.next().unwrap() {
          Token {
            kind: TokenKind::Num(b,),
            ..
          } => {
            // If b is an immediate num perform the operation at compile time
            let b = b.to_le_bytes();
            self.program.extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Bool(b,),
            ..
          } => {
            // If b is an immediate bool perform the operation at compile time
            let b = (b as u32).to_le_bytes();
            self.program.extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Register(b,),
            ..
          } => {
            // If b is a register generate the not opcode
            self.program.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          Token {
            kind: TokenKind::Identifier(name,),
            span,
          } => {
            // If b is an identifier generate the not opcode
            let b = self.ident_to_reg(name, span,);
            self.program.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          _ => unreachable!(),
        }
      }
      TokenKind::Eq | 
      TokenKind::Gt | 
      TokenKind::Lt | 
      TokenKind::Geq | 
      TokenKind::Leq=> {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_comparison(&self.current_instruction.unwrap(), &a, &b,);
      }
      TokenKind::Loop => self.compile_loop_expr(),
      TokenKind::While => {
        // Catch the statment here if it is a bool and optimize it out
        if let TokenKind::Bool(b,) = self.tokens.peek().unwrap().kind{
          self.next_token();
          if b{
            self.compile_loop_expr();
          }
          else{ 
            self.eat_block();
          }
          return;
        }

        let cond = self.compile_cond_expr();

        // Use a defered patch here to jump to the check
        self.program.push(OpCode::Jmp.into(),);

        let patch_idx = self
          .deferred
          .reserve(self.program.len(), &mut self.program,);

        // Set the return point for the JNZ to be the begining of the loop block's logic
        let ret = (self.program.len() as f32).to_le_bytes();

        // Compile the block contaning the LOOP's contents and add it to the
        // main program
        // self.program.extend_from_slice(self.compile_block().as_slice(),);
        self.compile_block();

        // Set the defered patch's target to the cond check
        self
          .deferred
          .update_target(patch_idx, self.program.len(),);

        // Check the condition
        self.program.extend_from_slice(cond.as_slice(),);

        // Jump to the `ret` address if the condition is true (not zero)
        self.program.extend_from_slice(&[OpCode::Jnz.into(), ret[0], ret[1], ret[2], ret[3], EQ as u8,],);
      }
      TokenKind::For => self.compile_for_loop_expr(),
      TokenKind::If => self.compile_if_body_expr(),
      TokenKind::Else => {
        let next_operation = *self.tokens.peek().unwrap();
        // If the "instruction" starts with a bracket, compile block should be called
        return match next_operation.kind {
          TokenKind::LCurlyBracket => self.compile_block(),
          // Doing nothing here will make it continue compiling the program which is what we want
          _ => {},
        };
      }
      TokenKind::Fn => {
        // Store the name in the symbol table
        let name = match self.tokens.next().unwrap().kind {
          TokenKind::Identifier(name,) => name,
          other => panic!("{}", ASMError::MissingFnName(other)),
        };

        // Try to fetch the function and update it with the declaration location
        // Panic if the function already has a declaration location
        let function_addr = Some(self.program.len(),);

        let decl = self.table.get_mut(&name,);
        match decl {
          Some(decl,) => match &mut decl.ty {
            Ty::Function {
              function_addr: addr @ None,
              patch_index: Some(patch_idx,),
            } => {
              *addr = function_addr;
              self.deferred.update_target(*patch_idx, function_addr.unwrap(),);
            }
            Ty::Function {
              function_addr: Some(_,),
              ..
            } => panic!("{}", ASMError::UnavailableFunctionName(&lookup(name))),
            _ => panic!("{}", ASMError::NotFunction(decl.ty)),
          },
          // Create a new entry in the symbol table if the function is not in it
          None => {
            let decl = VarDecl::new(Ty::Function {
              function_addr,
              patch_index:None,
            },);
            self.table.insert(name, decl,);
          }
        };
        self.compile_block();
      }
      TokenKind::Call => {
       self.program.push(OpCode::Call.into(),);

        let name = match self.tokens.next().unwrap() {
          Token {
            kind: TokenKind::Identifier(name,),
            ..
          } => name,
          other => panic!(
            "{}",
            ASMError::NoNameCall(other.kind, other.span.start)
          ),
        };

        match self.table.get(&name,) {
          // Try to get the location of the function name from the symbol table
          Some(decl,) => match &decl.ty {
            Ty::Function {
              function_addr: None,
              patch_index: Some(patch_idx,),
              // If the function does not have a declaration location, get its
              // patch index and update the deferred patches
            } => {
              self
                .deferred
                .insert_patch_site(*patch_idx, self.program.len(), &mut self.program,)
            }
            // Compile the addr
            Ty::Function {
              function_addr: Some(addr,),
              ..
            } => self.program.extend_from_slice((*addr as f32).to_le_bytes().as_slice(),),
            _ => panic!("{}", ASMError::NotFunction(decl.ty)),
          },
          // If the function VarDecl is not in the symbol table create one by patching
          None => {
            let patch_idx = self
              .deferred
              .reserve(self.program.len(), &mut self.program,);

            let decl = VarDecl {
              ty:Ty::Function {
                function_addr:None,
                patch_index:Some(patch_idx,),
              },
            };
            self.table.insert(name, decl,);
          }
        }
      }
      TokenKind::SysCall => {
        let call_idx = match self.tokens.next().unwrap() {
          // Confirm the token is an identifier
          Token {
            kind: TokenKind::Identifier(idx,),
            span,
            // Get the vardecl associated with the identifer
          } => match self.table.get(&idx,) {
            // Confirm the decl is an external function
            Some(decl,) => match decl.ty {
              Ty::ExternalFunction(idx,) => idx,
              _ => panic!(
                "{}",
                ASMError::UnregistedSyscall(&lookup(idx), span.start)
              ),
            },
            // If the decl identifer is not registered error
            None => panic!(
              "{}",
              ASMError::UnregistedSyscall(&lookup(idx), span.start)
            ),
          },
          // This should be must be followed by a syscall name not unregisted
          other => panic!(
            "{}",
            ASMError::NoNameCall(other.kind, other.span.start)
          ),
        };

        self.program.extend_from_slice(&[OpCode::SysCall.into(), call_idx,],);
      }
      TokenKind::Label(name,) => {
        // The label's address is the current len of the program
        self
          .table
          .insert(name, VarDecl::new(Ty::Label(self.program.len(),),),);
      }
      TokenKind::Noop => self.program.push(OpCode::Noop.into(),),
      TokenKind::Push => {
        let reg = self.next_token_as_register();
        self.program.extend_from_slice(&[OpCode::Push.into(), reg,],);
      }
      TokenKind::Pop => self.program.push(OpCode::Pop.into(),),
      TokenKind::PopR => {
        let reg = match self.tokens.next().unwrap() {
          Token {
            kind: TokenKind::Register(dst,),
            ..
          } => dst,
          other=> panic!(
            "{}",
            ASMError::NotRegisterOrIdent(other.kind, other.span.start)
          ),
        };
        self.program.extend_from_slice(&[OpCode::PopR.into(), reg,],);
      }
      TokenKind::Wmem => {
        // Get the register storing the destination
        let dst = self.next_token_as_register();
        // Get the register storing the pointer
        let src = self.next_token_as_register();
        // Get the value of the immediate offset
        let i_offset = self.next_token_as_immediate_array();
        // Get the register storing the register offset
        let r_offset = self.next_token_as_register();

        self.program.extend_from_slice(&[
          OpCode::WMem.into(),
          dst,
          src,
          i_offset[0],
          i_offset[1],
          i_offset[2],
          i_offset[3],
          r_offset,
        ],);
      }
      TokenKind::Rmem => {
        // Get the register storing the destination
        let dst = self.next_token_as_register();
        // Get the register storing the pointer
        let src = self.next_token_as_register();
        // Get the value of the immediate offset
        let i_offset = self.next_token_as_immediate_array();
        // Get the register storing the register offset
        let r_offset = self.next_token_as_register();

        self.program.extend_from_slice(&[
          OpCode::RMem.into(),
          dst,
          src,
          i_offset[0],
          i_offset[1],
          i_offset[2],
          i_offset[3],
          r_offset,
        ],);
      }
      TokenKind::MemCpy => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        self.program.extend_from_slice(&[OpCode::MemCpy.into(), dst, src,],);
      }
      TokenKind::Alloc => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        self.program.extend_from_slice(&[OpCode::Alloc.into(), dst, src,],);
      }
      TokenKind::Dealloc => self.program.extend_from_slice(&[OpCode::Dealloc.into(),],),
      TokenKind::Ret => {
        // Number of items to pop from the stack when returning
        let pop_number = self.next_token_as_immediate_array();
        self.program.extend_from_slice(&[
          OpCode::Ret.into(),
          pop_number[0],
          pop_number[1],
          pop_number[2],
          pop_number[3],
        ],);
      }
      TokenKind::Eof => {}
      _ => panic!(
        "{}",
        ASMError::NotAnOpcode(
          self.current_instruction_kind(),
          self.current_instruction_span().start
        )
      ),
    }
  }

  /// Consume and discard the next block in the program.
  fn eat_block(&mut self,) {
    let next = self.tokens.next().unwrap();
    assert!(
      next.kind == TokenKind::LCurlyBracket,
      "Block must begin with {{ not {}",
      next.kind
    );

    // Create the block to be compiled
    while let Some(instruction,) = self.tokens.next() {
      self.current_instruction = Some(instruction,);
      if instruction.kind == TokenKind::RCurlyBracket {
        // Does not need to eat the block because the compile function will call the next token
        break;
      }
      self.eat_current_instruction()
    }
  }

  /// Compile the next block in the program.
  fn compile_block(&mut self,) {
    let next = self.tokens.next().unwrap();
    assert!(
      next.kind == TokenKind::LCurlyBracket,
      "Block must begin with {{ not {}",
      next.kind
    );

    // Create the block to be compiled
    while let Some(instruction,) = self.tokens.next() {
      self.current_instruction = Some(instruction,);
      if self.current_instruction_kind() == TokenKind::RCurlyBracket {
        // Does not need to eat the block because the compile function will call the next token 
        break;
      }
      self.compile_current_instruction()
    }
  }

}

#[cfg(test)]
mod test {
  use spdr_isa::{
    opcodes::{CmpFlag, OpCode}, program::Program, registers::{EQ, LOOP}
  };
  use crate::{interner::intern, Compiler, Ty};

  // TODO: Add support for compiling arrays

  #[test]
  fn load_header() {
    let mut compiler = Compiler::new("",);
    compiler
      .read_header("C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\galaxy-macro-asm\\src\\test_header.hd",);

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

  // TODO: Add some kind of error to the arithmetic if it fails without the
  // expected args
  #[test]
  fn compile_load_cpy() {
    let p = Compiler::new("Load $14 1 Copy $15 $12",).compile();
    #[rustfmt::skip]
    assert_eq!(p.as_slice(),[
      OpCode::Load.into(), 14, 0, 0, 128, 63,
      OpCode::Copy.into(), 15, 12,
    ]);
  }

  #[test]
  fn compile_memcpy_rmem_wmem() {
    let p = Compiler::new("wmem $14 $15 1 $16 memcpy $55 $50 rmem $255 $40 1 $20",).compile();

    #[rustfmt::skip]
    assert_eq!(p.as_slice(),[
      OpCode::WMem.into(), 14, 15, 0, 0, 128, 63, 16,
      OpCode::MemCpy.into(), 55, 50,
      OpCode::RMem.into(), 255, 40, 0, 0, 128, 63, 20
    ]);
  }

  #[test]
  fn compile_alloc_dealloc() {
    let p = Compiler::new("Alloc $14 $90 Dealloc",).compile();

    #[rustfmt::skip]
    assert_eq!(p.as_slice(),[
      OpCode::Alloc.into(), 14, 90,
      OpCode::Dealloc.into(),
    ]);
  }

  #[test]
  fn compile_arith() {
    // ADDII
    let p = Compiler::new("ADD $14 15 10",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::Load.into(), 14, 0, 0, 200, 65]
    );

    // ADDRI
    let p = Compiler::new("ADD $14 $15 10",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::AddRI.into(), 14, 15, 0, 0, 32, 65,]
    );

    // ADDRR
    let p = Compiler::new("ADD $14 $14 $15",).compile();
    assert_eq!(p.as_slice(), [OpCode::AddRR.into(), 14, 14, 15,]);

    // SUBII
    let p = Compiler::new("SUB $14 10 30",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::Load.into(), 14, 0, 0, 160, 193,]
    );

    // SUBIR
    let p = Compiler::new("SUB $15 90 $14",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::RvSubRI.into(), 15, 14, 0, 0, 180, 66]
    );

    // SUBRI
    let p = Compiler::new("SUB $15 $14 90",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::SubRI.into(), 15, 14, 0, 0, 180, 66]
    );

    // SUBRR
    let p = Compiler::new("SUB $15 $14 $14",).compile();
    assert_eq!(p.as_slice(),[OpCode::SubRR.into(), 15, 14, 14]);

    // MULII
    let p = Compiler::new("MUL $14 10 29.32",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::Load.into(), 14, 154, 153, 146, 67,]
    );

    // MULRI
    let p = Compiler::new("MUL $15 $14 10",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::MulRI.into(), 15, 14, 0, 0, 32, 65,]
    );

    // MULRR
    let p = Compiler::new("MUL $15 $14 $14",).compile();
    assert_eq!(p.as_slice(), [OpCode::MulRR.into(), 15, 14, 14]);

    // DIVII
    let p = Compiler::new("DIV $14 32.54 653",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::Load.into(), 14, 42, 28, 76, 61,]
    );

    // DIVRI
    let p = Compiler::new("DIV $15 $14 90",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::DivRI.into(), 15, 14, 0, 0, 180, 66]
    );

    // DIVIR
    let p = Compiler::new("DIV $15 90 $14",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::RvDivRI.into(),  15, 14, 0, 0, 180, 66]
    );

    // DIVRR
    let p = Compiler::new("DIV $15 $14 $14",).compile();
    assert_eq!(p.as_slice(), [OpCode::DivRR.into(), 15, 14, 14]);

    // POWII
    let p = Compiler::new("POW $14 76.253216 3.7",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::Load.into(), 14, 127, 144, 12, 75,]
    );

    // POWRI
    let p = Compiler::new("POW $15 $14 90",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::PowRI.into(), 15, 14, 0, 0, 180, 66]
    );

    // POWIR
    let p = Compiler::new("POW $15 90 $14",).compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::RvPowRI.into(), 15, 14, 0, 0, 180, 66]
    );

    // PowRR
    let p = Compiler::new("POW $15 $14 $14",).compile();
    assert_eq!(p.as_slice(), [OpCode::PowRR.into(), 15, 14, 14]);
  }

  #[test]
  fn compile_loop_for_loop_and_while_loop() {
    // Test plain loop compilation
    let p = Compiler::new("Loop {ADD $14 $30 1}",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
        OpCode::Jmp.into(), 0, 0, 0, 0,
      ]
    );

    // Test while loop compilation when `true`
    let p = Compiler::new("while true {noop noop noop}",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Jmp.into(), 0, 0, 0, 0,
      ]
    );

    // Test While loop compilation when `false`
    let p = Compiler::new("while false {noop noop noop}",).compile();
    assert_eq!(p.as_slice(), []);

    // Test While loop compilation with real condition
    let p = Compiler::new("while EQ $15 1 {noop noop noop}",).compile();

    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Jmp.into(), 0, 0, 0, 65, // 8 in f32 le bytes
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
        OpCode::Jnz.into(), 0, 0, 160, 64, EQ as u8, // <- this should jump to 5
      ]
    );

    // Test For loop compilation
    let p = Compiler::new("for i in 0..9{noop noop noop}",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
        OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
        OpCode::Jz.into(), 0, 0, 192, 64, EQ as u8, 
      ]
    );
  }

  #[test]
  fn compile_if_else() {
    // Compile IF with boolean true check
    // Compile ELSE
    let p = Compiler::new("IF true {Noop Noop Noop Noop} else {Add $15 0 1} Mul $16 1 1",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Load.into(), 16, 0, 0, 128, 63,
      ]
    );

    // Compile IF with boolean false check
    let p = Compiler::new("IF false {mul $54 0 1 } else {add $26 $17 1} add $46 0 1",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(), 
      [
        // Else Block
        OpCode::AddRI.into(), 26, 17, 0, 0, 128, 63, 
        // Trailing expression
        OpCode::Load.into(), 46, 0, 0, 128, 63,
      ]
    );

    // Compile IF with runtime check
    // Compile ELSE IF
    let p = Compiler::new("IF EQ $14 0 {Noop Noop Noop Noop} Else If GT $15 1 {add $26 0 1 Noop Noop Noop} Mul $14 $14 1 ",).compile();
    // If is failing likely because it is placing the jump location after the else
    #[rustfmt::skip]
    assert_eq!(p.as_slice(), [
      // IF expression
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 0, 0,
      OpCode::Jz.into(), EQ as u8, 0, 0, 136, 65, // Jump to idx 17 if the comparison fails
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      // ELSE expression
      OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 128, 63,
      OpCode::Jz.into(), EQ as u8, 0, 0, 28, 66, // Jump to idx 39 if the comparison fails
      OpCode::Load.into(), 26, 0, 0, 128, 63,
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::MulRI.into(), 14, 14, 0, 0, 128, 63,
    ]);
  }

  #[test]
  #[should_panic = "UNAVAILABLE FUNCTION NAME: The name foo is already in use."]
  fn compile_fn_and_use() {
    // Calling works:
    // - When function defined after call
    // - With multiple callsites
    // - With recursion
    // - With return
    let src = "
    call foo

    FN foo {
      Add $14 $14 1
      Noop
      call foo
      Sub $14 $15 $14 
      call foo
      ret 2
    }

    call foo
    call foo 
    ";
    let p = Compiler::new(src,).compile();
    dbg!(&p);
    #[rustfmt::skip]
    assert_eq!(p.as_slice(), [
      OpCode::Call.into(), 0, 0, 160, 64, 
      OpCode::AddRI.into(), 14, 14, 0, 0, 128, 63,
      OpCode::Noop.into(),
      OpCode::Call.into(), 0, 0, 160, 64,
      OpCode::SubRR.into(), 14, 15, 14,
      OpCode::Call.into(), 0, 0, 160, 64,
      OpCode::Ret.into(), 0, 0, 0, 64,
      OpCode::Call.into(), 0, 0, 160, 64, 
      OpCode::Call.into(), 0, 0, 160, 64, 
    ]);

    // Test fuction name reuse fails
    let src = "
    fn foo {noop}
    fn foo {noop noop}
    ";
    let _ = Compiler::new(src,).compile();
  }

  #[test]
  fn compile_syscall() {
    // TODO: Make it so syscalls can also be called using "call"
    let mut compiler = Compiler::new("syscall foo",);
    compiler
      .read_header("C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\galaxy-macro-asm\\src\\test_header.hd",);

    let p = compiler.compile();
    assert_eq!(p.as_slice(), [OpCode::SysCall.into(), 0]);
  }

  #[test]
  fn compile_push_pop() {
    let p = Compiler::new("Push $1 Push $1 Pop PopR $16",).compile();

    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Push.into(), 1, 
        OpCode::Push.into(), 1,
        OpCode::Pop.into(),
        OpCode::PopR.into(), 16,
      ]
    );
  }

  #[test]
  fn compile_equality_checks(){
    // TODO:
    // - Figure out why formating does not work here

    // EQII
    let p = Compiler::new("eq 2 2").compile();
    assert_eq!(p.as_slice(),[OpCode::Load.into(), EQ as u8, 1, 0, 0, 0]);
    // EQIR
    let p = Compiler::new("eq $14 1").compile();
    assert_eq!(p.as_slice(),[OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 128, 63]);
    // EQRR
    let p = Compiler::new("eq $14 $15").compile();
    assert_eq!(p.as_slice(),[OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 15]);

    // GEQII
    let p = Compiler::new("geq 4 2").compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Load.into(), EQ as u8, 1, 0, 0, 0
      ]
    );
    // GEQRI
    let p = Compiler::new("geq $14 1").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63,]
    );
    // GEQIR
    let p = Compiler::new("geq 1 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63, OpCode::Not.into(), EQ as u8, EQ as u8,]
    );
    // GEQRR
    let p = Compiler::new("geq $15 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRR.into(), CmpFlag::Geq.into(), 15, 14,]
    );

    // LEQII
    let p = Compiler::new("leq 4 2").compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Load.into(), EQ as u8, 0, 0, 0, 0
      ]
    );
    // LEQRI
    let p = Compiler::new("leq $14 1").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63,]
    );
    // LEQIR
    let p = Compiler::new("leq 1 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63, OpCode::Not.into(), EQ as u8, EQ as u8,]
    );
    // LEQRR
    let p = Compiler::new("leq $15 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRR.into(), CmpFlag::Leq.into(), 15, 14,]
    );

    // GTII
    let p = Compiler::new("gt 4 2").compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Load.into(), EQ as u8, 1, 0, 0, 0
      ]
    );
    // GTRI
    let p = Compiler::new("gt $14 1").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63,]
    );
    // GTIR
    let p = Compiler::new("gt 1 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63, OpCode::Not.into(), EQ as u8, EQ as u8,]
    );
    // GTRR
    let p = Compiler::new("gt $15 $14").compile();
    assert_eq!(
      p.as_slice(),
      [OpCode::CmpRR.into(), CmpFlag::Gt.into(), 15, 14,]
    );
    
    // LTII
    let p = Compiler::new("LT 2 1").compile();
    assert_eq!(p.as_slice(),[OpCode::Load.into(), EQ as u8, 0, 0, 0, 0]);

    // LTRI
    let p = Compiler::new("LT $14 1").compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63,
      ]
    );

    // LTIR
    let p = Compiler::new("LT 1 $14 ").compile();
    assert_eq!(
      p.as_slice(),
      [
        OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63, OpCode::Not.into(), EQ as u8, EQ as u8
      ]
    );

    // LTRR
    let p = Compiler::new("LT $15 $14").compile();
    assert_eq!(p.as_slice(),[OpCode::CmpRR.into(), CmpFlag::Lt.into(), 15, 14]);
  }

  #[test]
  fn eat_instruction_works(){
    // Somewhere a defered patch is not being eaten and a noop is not being skipped
    let src = include_str!("full_compilation_test.spdr");
    let p = Compiler::new(src).eat_compile();
    assert_eq!(p.as_slice(),[]);
  }

  #[test]
  fn general_test() {
    let src = include_str!("full_compilation_test.spdr");
    let p = Compiler::new(src).compile();
    dbg!(&p);

    // Do an assert
  }


  impl<'tcx> Compiler<'tcx>{
    /// Function created to test `self.eat_current_instruction()` works.
    fn eat_compile(&mut self,) -> Program {
      // Iterate over each each and interpret it as an opcode
      while let Some(instruction,) = self.tokens.next() {
        self.current_instruction = Some(instruction,);
        // Match the instruction
        self.eat_current_instruction();
      }
  
      let mut out = self.program.clone();
      self.deferred.patch(&mut out,);
  
      // Once all lines are compiled return the program
      return out;
    }
  }
}
