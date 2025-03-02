#![feature(iter_next_chunk)]
#![feature(stmt_expr_attributes)]
mod assembler_errors;
mod defered_patch;
mod interner;
mod tokenizer;

use assembler_errors::ASMError;
use defered_patch::DeferredPatches;
use interner::{intern, lookup};
use spdr_isa::{
  program::Program,
  registers::{EQ, LOOP, REG_NUMBER},
  OpCode,
};

use std::{
  collections::HashMap,
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
  println!("Hello, world!");
  let src = "";
  let mut compiler = Compiler::new(src,);

  compiler.read_header("",);

  let _program = compiler.compile();
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
  /// Indicates the order of an RI binary operation is `Register op Immediate`.
  const R_OP_I:u8 = 0;

  /// Indicates the order of an RI binary operation is `I op R`.
  const I_OP_R:u8 = 1;

  fn new(src:&'tcx str,) -> Self {
    let tokens = Lexer::new(src,).tokenize().into_iter().peekable();
    Self {
      table:HashMap::new(),
      tokens,
      deferred:DeferredPatches::new(),
      program:Program::new(),
      open:13,
      current_instruction:None,
      _str:&src,
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

  /// Adds an identifier to the [`Compiler`]'s Symbol Table as a
  /// [`Ty::Register`].
  fn add_as_reg(&mut self, ident:Token,) -> u8 {
    // Get the currently open register and update the indicator to the next open
    // register
    let reg = self.reserve_reg();

    assert!(reg <= REG_NUMBER, "New register allocation strategy needed");

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

  pub fn read_header(&mut self, src:&str,) {
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

  /// Reserves a register for use.
  fn reserve_reg(&mut self,) -> u8 {
    let reg = self.open;
    self.open += 1;
    reg
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
        ASMError::UndeclaredIdentifier(&lookup(name), span.start.ln, span.start.col)
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

  fn compile(&mut self,) -> Program {
    // Iterate over each each and interpret it as an opcode
    while let Some(instruction,) = self.tokens.next() {
      self.current_instruction = Some(instruction,);
      // Match the instruction
      let line = self.compile_instruction();
      self.program.extend_from_slice(line.as_slice(),);
    }

    let mut out = self.program.clone();
    self.deferred.patch(&mut out,);

    // Once all lines are compiled return the program
    return out;
  }

  fn compile_block(&mut self,) -> Program {
    let next = self.tokens.next().unwrap();
    assert!(
      next.kind == TokenKind::LCurlyBracket,
      "Block must begin with {{ not {}",
      next.kind
    );

    // Create the block to be compiled
    let mut program = Program::new();
    while let Some(instruction,) = self.tokens.next() {
      self.current_instruction = Some(instruction,);
      if self.current_instruction_kind() == TokenKind::RCurlyBracket {
        break;
      }
      program.extend_from_slice(self.compile_instruction().as_slice(),);
    }

    program
  }

  /// Compile the next line of the program.
  fn compile_instruction(&mut self,) -> Program {
    let mut program = Program::new();

    match self.current_instruction.unwrap().kind {
      TokenKind::Load => {
        let reg = self.next_token_as_register();

        // Get the immediate as an array and generate the instruction
        let val = self.next_token_as_immediate_array();
        program.extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Copy => program.extend_from_slice(&[
        OpCode::Copy.into(),
        self.next_token_as_register(),
        self.next_token_as_register(),
      ],),
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
        program.extend_from_slice(&[OpCode::Load.into(), reg, val[0], val[1], val[2], val[3],],);
      }
      TokenKind::Add => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_add_statement(&target, &a, &b, &mut program,)
      }
      TokenKind::Sub => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_sub_statement(&target, &a, &b, &mut program,)
      }
      TokenKind::Mul => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_mul_statement(&target, &a, &b, &mut program,)
      }
      TokenKind::Div => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_div_statement(target, &a, &b, &mut program,)
      }
      TokenKind::Pow => {
        let target = self.tokens.next().unwrap();
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_pow_statement(&target, &a, &b, &mut program,)
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
            program.extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Bool(b,),
            ..
          } => {
            // If b is an immediate bool perform the operation at compile time
            let b = (b as u32).to_le_bytes();
            program.extend_from_slice(&[OpCode::Load.into(), dst, !b[0], !b[1], !b[2], !b[3],],);
          }
          Token {
            kind: TokenKind::Register(b,),
            ..
          } => {
            // If b is a register generate the not opcode
            program.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          Token {
            kind: TokenKind::Identifier(name,),
            span,
          } => {
            // If b is an identifier generate the not opcode
            let b = self.ident_to_reg(name, span,);
            program.extend_from_slice(&[OpCode::Not.into(), dst, b,],);
          }
          _ => unreachable!(),
        }
      }
      // All conditionals can be built from EQ and GT
      TokenKind::Eq => {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_equal_check(&a, &b, &mut program,);
      }
      TokenKind::Gt => {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();
        self.compile_greater_than_check(&a, &b, &mut program,);
      }
      // An a < b can be broken into a greater than check with the order of the arguments
      // flipped
      TokenKind::Lt => {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();

        self.compile_greater_than_check(&b, &a, &mut program,);
      }
      // An a >= b can be broken into a greater than check followed by an equals check
      TokenKind::Geq => {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();

        self.compile_greater_than_check(&a, &b, &mut program,);
        self.compile_equal_check(&a, &b, &mut program,);
      }
      // An a <= b can be broken into a greater than check with the order of the arguments
      // flipped followed by an equals check
      TokenKind::Leq => {
        let a = self.tokens.next().unwrap();
        let b = self.tokens.next().unwrap();

        self.compile_greater_than_check(&b, &a, &mut program,);
        self.compile_equal_check(&a, &b, &mut program,);
      }
      TokenKind::Loop => self.compile_loop_statement(),
      TokenKind::While => {
        // jmp loop1           ; Jump to condition first
        // cloop1  nop         ; Execute the content of the loop
        // loop1   cmp ax,1    ; Check the condition
        //         je cloop1   ; Jump to content of the loop if met
        let cond = match self.compile_cond_statement(|s, b| {
          // If the condition is true compile it like a normal loop:
          if b {
            s.compile_loop_statement();
          }
          // If the condition is false compile the block and discard it:
          else {
            let _ = s.compile_block();
          }
        },)
        {
          Some(cond,) => cond,
          None => return Program::new(),
        };

        // Use a defered patch here to jump to the check
        program.push(OpCode::Jmp.into(),);

        let patch_idx = self
          .deferred
          .reserve(self.program.len() + program.len(), &mut program,);

        // Set the return point for the JNZ to be the begining of the loop block's logic
        let ret = ((self.program.len() + program.len()) as f32).to_le_bytes();

        // Compile the block contaning the LOOP's contents and add it to the
        // main program
        program.extend_from_slice(self.compile_block().as_slice(),);

        // Set the defered patch's target to the cond check
        self
          .deferred
          .update_target(patch_idx, self.program.len() + program.len(),);

        // Check the condition
        program.extend_from_slice(cond.as_slice(),);

        // Jump to the `ret` address if the condition is true (not zero)
        program.extend_from_slice(&[OpCode::Jnz.into(), ret[0], ret[1], ret[2], ret[3], EQ,],);
      }
      TokenKind::For => self.compile_for_loop(&mut program,),
      TokenKind::If => {
        // Compile the condition
        let cond = match self.compile_cond_statement(|s, b| {
          // If the condition is always true just compile the block there is no reason to
          // include the check
          if b {
            // Compile the block
            let body = s.compile_block();
            s.program.extend_from_slice(body.as_slice(),);
          }
          // If the condition is false disregard the block
          else {
            // Consume the block
            let _ = s.compile_block();
          }
        },)
        {
          Some(cond,) => cond,
          None => return Program::new(),
        };

        program.extend_from_slice(cond.as_slice(),);

        // Check the condition use a JZ to jump to the end of the IF expression
        // if it is false. Use a defered patch in place of the end of
        // the expression
        program.push(OpCode::Jz.into(),);
        let patch_idx:usize = self
          .deferred
          .reserve(program.len() + self.program.len(), &mut program,);

        // Compile the block
        program.extend_from_slice(self.compile_block().as_slice(),);

        // If the expression is followed by an "Else", compile that before updating the
        // defered patch
        if matches!(self.tokens.peek().unwrap().kind, TokenKind::Else) {
          self.current_instruction = self.tokens.next();
          let else_expr = self.compile_instruction();
          program.extend_from_slice(else_expr.as_slice(),);
        }

        // Update the deferred patch
        self
          .deferred
          .update_target(patch_idx, program.len() + self.program.len(),);
      }
      TokenKind::Else => {
        let next_operation = *self.tokens.peek().unwrap();
        // If the "instruction" starts with a bracket, compile block should be called
        return match next_operation.kind {
          TokenKind::LCurlyBracket => self.compile_block(),
          _ => self.compile_instruction(),
        };
      }
      TokenKind::Fn => {
        // Store the name in the symbol table
        let name = match self.tokens.next().unwrap().kind {
          TokenKind::Identifier(name,) => name,
          other => panic!("{}", ASMError::NoNameFn(other)),
        };

        // Try to fetch the function and update it with the declaration location
        // Panic if the function already has a declaration location
        let function_addr = Some(self.program.len() + program.len(),);

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
        program.extend_from_slice(self.compile_block().as_slice(),);
      }
      TokenKind::Call => {
        program.push(OpCode::Call.into(),);

        let name = match self.tokens.next().unwrap() {
          Token {
            kind: TokenKind::Identifier(name,),
            ..
          } => name,
          other => panic!(
            "{}",
            ASMError::NoNameCall(other.kind, other.span.start.ln, other.span.start.col)
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
                .insert_patch_site(*patch_idx, self.program.len() + program.len(), &mut program,)
            }
            // Compile the addr
            Ty::Function {
              function_addr: Some(addr,),
              ..
            } => program.extend_from_slice((*addr as f32).to_le_bytes().as_slice(),),
            _ => panic!("{}", ASMError::NotFunction(decl.ty)),
          },
          // If the function VarDecl is not in the symbol table create one by patching
          None => {
            let patch_idx = self
              .deferred
              .reserve(self.program.len() + program.len(), &mut program,);

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
                ASMError::UnregistedSyscall(&lookup(idx), span.start.ln, span.start.col)
              ),
            },
            // If the decl identifer is not registered error
            None => panic!(
              "{}",
              ASMError::UnregistedSyscall(&lookup(idx), span.start.ln, span.start.col)
            ),
          },
          // This should be must be followed by a syscall name not unregisted
          other => panic!(
            "{}",
            ASMError::NoNameCall(other.kind, other.span.start.ln, other.span.start.col)
          ),
        };

        program.extend_from_slice(&[OpCode::SysCall.into(), call_idx,],);
      }
      TokenKind::Label(name,) => {
        // The label's address is the current len of the program
        self
          .table
          .insert(name, VarDecl::new(Ty::Label(self.program.len(),),),);
      }
      TokenKind::Noop => program.push(OpCode::Noop.into(),),
      TokenKind::Push => {
        let value = self.next_token_as_immediate_array();
        program.extend_from_slice(&[OpCode::Push.into(), value[0], value[1], value[2], value[3],],);
      }
      TokenKind::Pop => program.push(OpCode::Pop.into(),),
      TokenKind::PopR => {
        let reg = match self.tokens.next().unwrap() {
          Token {
            kind: TokenKind::Register(dst,),
            ..
          } => dst,
          other @ _ => panic!(
            "{}",
            ASMError::NotRegisterOrIdent(other.kind, other.span.start.ln, other.span.start.col)
          ),
        };
        program.extend_from_slice(&[OpCode::PopR.into(), reg,],);
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

        program.extend_from_slice(&[
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

        program.extend_from_slice(&[
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
        program.extend_from_slice(&[OpCode::MemCpy.into(), dst, src,],);
      }
      TokenKind::Alloc => {
        let dst = self.next_token_as_register();
        let src = self.next_token_as_register();
        program.extend_from_slice(&[OpCode::Alloc.into(), dst, src,],);
      }
      TokenKind::Dealloc => {
        program.extend_from_slice(&[OpCode::Dealloc.into(),],);
      }
      TokenKind::Ret => {
        // Number of items to pop from the stack when returning
        let pop_number = self.next_token_as_immediate_array();
        program.extend_from_slice(&[
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
          self.current_instruction_span().start.ln,
          self.current_instruction_span().start.col
        )
      ),
    }
    program
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
        ASMError::InvalidImmediateType(other.kind, other.span.start.ln, other.span.start.col)
      ),
    }
  }

  /// If the next [`Token`] in the source is a [`TokenKind::Register`], return
  /// it as a u8.
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
        ASMError::NotRegisterOrIdent(other.kind, other.span.start.ln, other.span.start.col)
      ),
    }
  }

  fn compile_loop_statement(&mut self,) {
    // Set the return address
    let ret = (self.program.len() as f32).to_le_bytes();

    // Compile the block contaning the LOOP's contents and add it to the
    // main program
    let block = self.compile_block();
    self.program.extend_from_slice(block.as_slice(),);

    // Jump to the `ret` address
    self
      .program
      .extend_from_slice(&[OpCode::Jmp.into(), ret[0], ret[1], ret[2], ret[3],],);
  }

  /// Checks whether the statement is a boolean or a condition statement. If the
  /// expression is a boolean, allows the user to provide a callback for
  /// handling the expressiona. If the statement is an equality statement,
  /// compile it and return the [`Program`].
  fn compile_cond_statement<F,>(&mut self, mut f:F,) -> Option<Program,>
  where F: FnMut(&mut Compiler, bool,) {
    // Check if the cond is a raw boolean
    // let cond = self.tokens.next().unwrap();

    // TODO: Include a check here to ensure the token can begin a condition
    let cond = match self.tokens.next_if(|token| {
      matches!(
        token.kind,
        TokenKind::Eq | TokenKind::Gt | TokenKind::Geq | TokenKind::Lt | TokenKind::Leq | TokenKind::Bool(_)
      )
    },)
    {
      Some(cond,) => cond,
      None => panic!("{}", ASMError::NotEquality(self.next_token().kind,)),
    };

    self.current_instruction = Some(cond,);

    match cond.unwrap_bool() {
      Ok(b,) => {
        // If it is a boolean, handle it however the user wants
        f(self, b,);
        // TODO: I don't like having to return an empty program here.
        // It is possible this should just be pushed into the main program.
        // Then the returned condition is just EQ == EQ
        None
      }
      // Otherwise compile line
      Err(_,) => Some(self.compile_instruction(),),
    }
  }

  fn compile_for_loop(&mut self, program:&mut Program,) {
    // Confirm the next token is an ident and eat it
    // This ident is discarded because the loop_variable uses the LOOP reg
    self.tokens.next().unwrap().unwrap_ident().unwrap();

    // Ensure the syntax contains "in" as required
    let kwd = self.tokens.next().unwrap();
    assert_eq!(
      kwd.kind,
      TokenKind::In,
      "{}",
      ASMError::MissingKwd(TokenKind::For, TokenKind::In, kwd.kind),
    );

    // Parse the range
    let (start, end,) = match self.tokens.next().unwrap().unwrap_range() {
      Ok((start, end,),) => ((start as f32).to_le_bytes(), (end as f32).to_le_bytes(),),
      Err(err,) => panic!("{}", err),
    };

    // Set the counter equal to the range's start
    program.extend_from_slice(&[OpCode::Load.into(), LOOP, start[0], start[1], start[2], start[3],],);

    // Set the return address
    let ret = (program.len() as f32).to_le_bytes();

    // Compile the block
    program.extend_from_slice(self.compile_block().as_slice(),);

    #[rustfmt::skip]
    program.extend_from_slice(&[
      // Increment the counter by the value of 1f32 in le bytes = [0, 0, 128, 63,]
      OpCode::AddRI.into(), LOOP, LOOP, 0, 0, 128, 63,
      // Compare the counter to the range's end and store in EQ
      OpCode::EqRI.into(), LOOP, end[0], end[1], end[2], end[3],
      // JZ EQ to the begining of the loop
      OpCode::Jz.into(), ret[0], ret[1], ret[2], ret[3], EQ,
    ],);
  }

  fn compile_equal_check(&self, token_a:&Token, token_b:&Token, program:&mut Program,) {
    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediates perform the check during compilation
        let result = ((a == b) as u32).to_le_bytes();
        program.extend_from_slice(&[
          OpCode::Load.into(),
          EQ,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Bool(a,), TokenKind::Bool(b,),) => {
        // If both operands are immediates perform the check during compilation
        let result = ((a == b) as u32).to_le_bytes();
        program.extend_from_slice(&[
          OpCode::Load.into(),
          EQ,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::EqRI.into(), a, b[0], b[1], b[2], b[3],],);
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::EqRI.into(), a, b[0], b[1], b[2], b[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        #[rustfmt::skip]
        program.extend_from_slice(&[
          OpCode::EqRI.into(), b, a[0], a[1], a[2], a[3],
          OpCode::Not.into(), EQ, EQ
        ],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        #[rustfmt::skip]
        program.extend_from_slice(&[
          OpCode::EqRI.into(), b, a[0], a[1], a[2], a[3],
          OpCode::Not.into(), EQ, EQ
        ],);
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        program.extend_from_slice(&[OpCode::EqRR.into(), a, b,],);
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::EqRR.into(), a, b,],);
      }
      _ => unreachable!(),
    }
  }

  fn compile_greater_than_check(&self, token_a:&Token, token_b:&Token, program:&mut Program,) {
    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediates perform the check during compilation
        let result = ((a == b) as u32).to_le_bytes();
        program.extend_from_slice(&[
          OpCode::Load.into(),
          EQ,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::GtRI.into(), a, b[0], b[1], b[2], b[3],],);
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::GtRI.into(), a, b[0], b[1], b[2], b[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        #[rustfmt::skip]
        program.extend_from_slice(&[
          OpCode::GtRI.into(), b, a[0], a[1], a[2], a[3],
          OpCode::Not.into(), EQ, EQ
        ],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        #[rustfmt::skip]
        program.extend_from_slice(&[
          OpCode::GtRI.into(), b, a[0], a[1], a[2], a[3],
          OpCode::Not.into(), EQ, EQ
        ],);
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        program.extend_from_slice(&[OpCode::GtRR.into(), a, b,],);
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::GtRR.into(), a, b,],);
      }
      _ => unreachable!(),
    }
  }

  fn compile_add_statement(&self, target:&Token, token_a:&Token, token_b:&Token, program:&mut Program,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!(
        "{}",
        ASMError::NotRegisterOrIdent(target.kind, target.span.start.ln, target.span.start.col),
      ),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a + b).to_le_bytes();

        program.extend_from_slice(&[
          OpCode::Load.into(),
          target,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate value and b is a raw reg
        let a = a.to_le_bytes();
        program.extend_from_slice(&[OpCode::AddRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::AddRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::AddRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        program.extend_from_slice(&[OpCode::AddRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        program.extend_from_slice(&[OpCode::AddRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::AddRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  fn compile_sub_statement(&self, target:&Token, token_a:&Token, token_b:&Token, program:&mut Program,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!(
        "{}",
        ASMError::NotRegisterOrIdent(target.kind, target.span.start.ln, target.span.start.col),
      ),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a - b).to_le_bytes();

        program.extend_from_slice(&[
          OpCode::Load.into(),
          target,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate value and b is a raw reg
        let a = a.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::SubRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::SubRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::SubRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::SubRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        program.extend_from_slice(&[OpCode::SubRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::SubRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  fn compile_mul_statement(&self, target:&Token, token_a:&Token, token_b:&Token, program:&mut Program,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!(
        "{}",
        ASMError::NotRegisterOrIdent(target.kind, target.span.start.ln, target.span.start.col),
      ),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a * b).to_le_bytes();

        program.extend_from_slice(&[
          OpCode::Load.into(),
          target,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate value and b is a raw reg
        let a = a.to_le_bytes();
        program.extend_from_slice(&[OpCode::MulRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::MulRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        program.extend_from_slice(&[OpCode::MulRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        program.extend_from_slice(&[OpCode::MulRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        program.extend_from_slice(&[OpCode::MulRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::MulRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  fn compile_div_statement(&self, target:Token, token_a:&Token, token_b:&Token, program:&mut Program,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!(
        "{}",
        ASMError::NotRegisterOrIdent(target.kind, target.span.start.ln, target.span.start.col),
      ),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a / b).to_le_bytes();

        program.extend_from_slice(&[
          OpCode::Load.into(),
          target,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate value and b is a raw reg
        let a = a.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::DivRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::DivRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::DivRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::DivRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        program.extend_from_slice(&[OpCode::DivRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::DivRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  fn compile_pow_statement(&self, target:&Token, token_a:&Token, token_b:&Token, program:&mut Program,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!(
        "{}",
        ASMError::NotRegisterOrIdent(target.kind, target.span.start.ln, target.span.start.col),
      ),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a.powf(b,)).to_le_bytes();

        program.extend_from_slice(&[
          OpCode::Load.into(),
          target,
          result[0],
          result[1],
          result[2],
          result[3],
        ],)
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate value and b is a raw reg
        let a = a.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::PowRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::PowRI.into(), Self::I_OP_R, target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::PowRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
        program.extend_from_slice(&[OpCode::PowRI.into(), Self::R_OP_I, target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        program.extend_from_slice(&[OpCode::PowRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        program.extend_from_slice(&[OpCode::PowRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }
}

#[cfg(test)]
mod test {
  use spdr_isa::{
    registers::{EQ, LOOP},
    OpCode,
  };

  use crate::{interner::intern, Compiler, Ty};

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
      [p[0], p[1], p[2], p[3], p[4], p[5]],
      [OpCode::Load.into(), 14, 0, 0, 200, 65]
    );

    // ADDRI
    let p = Compiler::new("ADD $14 $15 10",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6]],
      [OpCode::AddRI.into(), 14, 15, 0, 0, 32, 65,]
    );

    // ADDRR
    let p = Compiler::new("ADD $14 $14 $15",).compile();
    assert_eq!([p[0], p[1], p[2], p[3],], [OpCode::AddRR.into(), 14, 14, 15,]);

    // SUBII
    let p = Compiler::new("SUB $14 10 30",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5]],
      [OpCode::Load.into(), 14, 0, 0, 160, 193,]
    );

    // SUBIR
    let p = Compiler::new("SUB $15 90 $14",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::SubRI.into(), Compiler::I_OP_R, 15, 14, 0, 0, 180, 66]
    );

    // SUBRI
    let p = Compiler::new("SUB $15 $14 90",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::SubRI.into(), Compiler::R_OP_I, 15, 14, 0, 0, 180, 66]
    );

    // SUBRR
    let p = Compiler::new("SUB $15 $14 $14",).compile();
    assert_eq!([p[0], p[1], p[2], p[3],], [OpCode::SubRR.into(), 15, 14, 14]);

    // MULII
    let p = Compiler::new("MUL $14 10 29.32",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5]],
      [OpCode::Load.into(), 14, 154, 153, 146, 67,]
    );

    // MULRI
    let p = Compiler::new("MUL $15 $14 10",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6],],
      [OpCode::MulRI.into(), 15, 14, 0, 0, 32, 65,]
    );

    // MULRR
    let p = Compiler::new("MUL $15 $14 $14",).compile();
    assert_eq!([p[0], p[1], p[2], p[3],], [OpCode::MulRR.into(), 15, 14, 14]);

    // DIVII
    let p = Compiler::new("DIV $14 32.54 653",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5]],
      [OpCode::Load.into(), 14, 42, 28, 76, 61,]
    );

    // DIVRI
    let p = Compiler::new("DIV $15 $14 90",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::DivRI.into(), Compiler::R_OP_I, 15, 14, 0, 0, 180, 66]
    );

    // DIVIR
    let p = Compiler::new("DIV $15 90 $14",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::DivRI.into(), Compiler::I_OP_R, 15, 14, 0, 0, 180, 66]
    );

    // DIVRR
    let p = Compiler::new("DIV $15 $14 $14",).compile();
    assert_eq!([p[0], p[1], p[2], p[3],], [OpCode::DivRR.into(), 15, 14, 14]);

    // POWII
    let p = Compiler::new("POW $14 76.253216 3.7",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5]],
      [OpCode::Load.into(), 14, 127, 144, 12, 75,]
    );

    // POWRI
    let p = Compiler::new("POW $15 $14 90",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::PowRI.into(), Compiler::R_OP_I, 15, 14, 0, 0, 180, 66]
    );

    // POWIR
    let p = Compiler::new("POW $15 90 $14",).compile();
    assert_eq!(
      [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]],
      [OpCode::PowRI.into(), Compiler::I_OP_R, 15, 14, 0, 0, 180, 66]
    );

    // PowRR
    let p = Compiler::new("POW $15 $14 $14",).compile();
    assert_eq!([p[0], p[1], p[2], p[3],], [OpCode::PowRR.into(), 15, 14, 14]);
  }

  #[test]
  fn compile_for_while_loop() {
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
        OpCode::EqRI.into(), 15, 0, 0, 128, 63,
        OpCode::Jnz.into(), 0, 0, 160, 64, EQ, // <- this should jump to 5
      ]
    );

    // Test For loop compilation
    let p = Compiler::new("for i in 0..9{noop noop noop}",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Load.into(), LOOP, 0, 0, 0, 0,
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::AddRI.into(), LOOP, LOOP, 0, 0, 128, 63,
        OpCode::EqRI.into(), LOOP, 0, 0, 0, 65,
        OpCode::Jz.into(), 0, 0, 192, 64, EQ, 
      ]
    );

    // This failed while printing because something is wrong with the for loop
    // printing probably an issue with range
    //  Also why is EQ 9 9 compiling to
    // Load $0, 0.000000000000000000000000000000000000000000001
    // shouldn't it just be load 0 true?

    // Loop is just an unconditional jump back to 0
    // While is check + unconditional jump back to declaration which is 0?
    // for is more complicated and I'll have to look it up
    // let src = "for i in 0..9{}";
    // let p = Compiler::new(Lexer::new(src,).tokenize(),).compile();
    // Steps of a for loop
    // - Create counter variable = max of range
    // - Create the loop number = max - min
    // - Sub 1 from the counter
    // - Compile block
    // - At end JNZ counter to the begining
    // assert_eq!([p[1]], [OpCode::Load.into()]);
  }

  #[test]
  fn compile_if_else() {
    // Compile IF with boolean true check
    let p = Compiler::new("IF true {Noop Noop Noop Noop} ",).compile();
    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
        OpCode::Noop.into(),
      ]
    );

    // Compile IF with boolean false check
    let p = Compiler::new("IF false {Noop Noop Noop Noop} ",).compile();
    #[rustfmt::skip]
    assert_eq!(p.as_slice(), []);

    // Compile IF with runtime check
    let p = Compiler::new("IF EQ $14 0 {Noop Noop Noop Noop} Else {Noop Noop Noop Noop} ",).compile();
    #[rustfmt::skip]
    assert_eq!(p.as_slice(), [
      // IF expression
      OpCode::EqRI.into(), 14, 0, 0, 0, 0,
      OpCode::Jz.into(), 0, 0, 152, 65,
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      // ELSE expression
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
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
    let p = Compiler::new("Push 1 Push 1 Pop PopR $16",).compile();

    #[rustfmt::skip]
    assert_eq!(
      p.as_slice(),
      [
        OpCode::Push.into(), 0, 0, 128, 63, 
        OpCode::Push.into(), 0, 0, 128, 63,
        OpCode::Pop.into(),
        OpCode::PopR.into(), 16,
      ]
    );
  }

  #[test]
  fn general_test() {
    dbg!(2f32.to_le_bytes());

    // Make actual tests compiles properly
  }
}
