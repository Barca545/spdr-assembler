use std::mem;
use crate::patch::Patch;
use crate::{assembler_errors::ASMError, Compiler, Token, TokenKind};
use spdr_isa::opcodes::{CmpFlag, OpCode};
use spdr_isa::program::Program;
use spdr_isa::registers::{EQ, LOOP};

/// Possible argument combinations for a binary operation.
pub enum ArgTypes{
  II(f32, f32),
  RI(u8, [u8;4], ),
  IR(u8, [u8;4], ),
  RR(u8, u8),
}

/// Helper functions for compilation
impl<'tcx,> Compiler<'tcx,> {
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
          other => panic!("{}", ASMError::InvalidComparison{ token: *other }),
        };

        self.main.extend_from_slice(&[
          OpCode::Load.into(),
          EQ as u8,
          result[0],
          result[1],
          result[2],
          result[3],
        ],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
      };
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
      };
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
      };
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
      };
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
      };
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } => self.main.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other}),
        };

        return Program::from(&[
          OpCode::Load.into(),
          EQ as u8,
          result[0],
          result[1],
          result[2],
          result[3],
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
          other => panic!("{}", ASMError::InvalidComparison{token:*other})
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
      _ => panic!("{}", ASMError::InvalidMathArgs { operation: op, arg1, arg2})
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
      None => panic!("{}", ASMError::MissingLoopVar{token:ident.kind,span:ident.span,}),
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
          self.eat_current_instruction();
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

  /// Compiles an array by eating tokens until a closing bracket is found and allocating space for them on the heap.
  pub(super) fn compile_array(&mut self){
    // Create a vec to store array entries
    let mut entries = Vec::new();

    // Store the first item in the array
    match self.next_token().unwrap() {
      token @ Token { kind:TokenKind::Num(_), .. } 
      | token @ Token { kind:TokenKind::Bool(_), .. } => {
        entries.push(token);

        // Check for the comma or closing bracket
        // Just consume them the function below the loop will catch it
        match self.next_token().unwrap() {
          // Stop assembling the array if a right bracket is encountered
          Token { kind:TokenKind::RBracket, .. }
          // Keep assembling the array if a comma is encountered
          | Token { kind:TokenKind::Comma, .. } => {},
          // Error if not a comma or the end of the array
          next => panic!("{}", ASMError::MissingComma { a:token , b:next })
        }
      },
      other => panic!("Cannot store {} {} in an array", other.kind, other.span.start)
    }

    while mem::discriminant(&self.peek().unwrap().kind) == mem::discriminant(&entries[0].kind) {
      let token = self.next_token().unwrap();
      entries.push(token);

      // Check for the comma
      match self.next_token().unwrap() {
        // Stop assembling the array if a right bracket is encountered
        Token { kind:TokenKind::RBracket, .. } => break,
        // Keep assembling the array if a comma is encountered
        Token { kind:TokenKind::Comma, .. } => continue,
        // Error if not a comma or the end of the array
        next => panic!("{}", ASMError::MissingComma { a:token , b:next })
      }
    }

    // This is only reached if the array has ended or an unexpected type was encountered
    match self.next_token().unwrap(){
      // Stop assembling the array if a right bracket is encountered
      Token { kind:TokenKind::RBracket, .. } => {},
      // This branch is only reached if there is a some kinda incorrect token in the array
      other => panic!("{}", ASMError::InvalidArrayEntry { token: other, array_type: "NUM" } )
    }

    // Check the number of items in the vec to see how much to allocate
    // TODO: Confirm ALLOC expects a u32 not an f32
    let size = (entries.len() as u32).to_le_bytes();

    // Reserve a register for the Slab and a register for the len
    let slab = self.reserve_reg();
    let len = self.reserve_reg();

        // TODO: Create opcodes to allocate immediately to memory without needing to go through a register
    // Allocate the slab and load the len into memory
    self.main.extend_from_slice(&[
      // Store the len first so we can use that for the allocation
      OpCode::Load.into(), len, size[0], size[1], size[2], size[3],
      OpCode::Alloc.into(), slab, len,
    ]);

    // TODO: Create opcodes to write immediately to memory without needing to go through a register
    // Generate instructions to load values into memory
    // Create a temporary register to store the offset in
    let temp = self.reserve_reg();
    for (i, entry) in entries.iter().enumerate() {
      let bytes = match entry.kind {
        TokenKind::Bool(boolean) => (boolean as u32).to_le_bytes(),
        TokenKind::Num(num) => num.to_le_bytes(),
        _=> unreachable!()
      };

      let idx = (i as u32).to_le_bytes();

      self.main.extend_from_slice(&[
        // First have to load the value into a register
        OpCode::Load.into(), temp, bytes[0], bytes[1], bytes[2], bytes[3],
        // Then write it into the array
        OpCode::WMem.into(), slab, temp, idx[0], idx[1], idx[2], idx[3], 0,
      ])
    }
  }

  // strings should be compiled...somehow else...
  // Maybe they can be stored in the section with the functions
}
