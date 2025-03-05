use crate::{assembler_errors::ASMError, Compiler, Token, TokenKind};
use spdr_isa::opcodes::{CmpFlag, OpCode};
use spdr_isa::program::Program;
use spdr_isa::registers::{EQ, LOOP};

// Refactor:
// - Can the math statements be merged into one helper function?

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
          other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start)),
        };

        self.program.extend_from_slice(&[
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
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } => self.program.extend_from_slice(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      };
      }
      _ => unreachable!(),
    }
  }

  /// Compile a comparison expression (EQ, GT, LT, GEQ, LEQ). Return it as a
  /// program instead of modifying the currently compiled program in place.
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
          other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start)),
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
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is an identity and b is an immediate
        let a = self.ident_to_reg(a, token_a.span,);
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  a, b[0], b[1], b[2], b[3]]),
        Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  a, b[0], b[1], b[2], b[3]]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (TokenKind::Num(a,), TokenKind::Register(b,),) => {
        // If a is an immediate and b is a register
        let a = a.to_le_bytes();
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate and b is an identity
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        // Perform the check and invert the operation
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Eq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Gt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Lt.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Geq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRI.into(), CmpFlag::Leq.into(),  b, a[0], a[1], a[2], a[3], OpCode::Not.into(), EQ as u8, EQ as u8,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If both are registers
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If both are identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      match op {
        Token { kind:TokenKind::Eq, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Eq.into(),  a, b,]),
        Token { kind:TokenKind::Gt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Gt.into(),  a, b,]),
        Token { kind:TokenKind::Lt, .. } => Program::from(&[OpCode::CmpRR.into(), CmpFlag::Lt.into(),  a, b,]),
        Token { kind:TokenKind::Geq, .. } =>Program::from(&[OpCode::CmpRR.into(), CmpFlag::Geq.into(),  a, b,]),
        Token { kind:TokenKind::Leq, .. } =>Program::from(&[OpCode::CmpRR.into(), CmpFlag::Leq.into(),  a, b,]),
        other => panic!("{}", ASMError::InvalidComparison(other.kind, other.span.start))
      }
      }
      (other_1, other_2,) => unreachable!("({},{}) are invalid", other_1, other_2),
    }
  }

  pub(super) fn compile_add_expr(&mut self, target:&Token, token_a:&Token, token_b:&Token,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!("{}", ASMError::NotRegisterOrIdent(target.kind, target.span.start),),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a + b).to_le_bytes();

        self.program.extend_from_slice(&[
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
        self
          .program
          .extend_from_slice(&[OpCode::AddRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::AddRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        self
          .program
          .extend_from_slice(&[OpCode::AddRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        self
          .program
          .extend_from_slice(&[OpCode::AddRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        self
          .program
          .extend_from_slice(&[OpCode::AddRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::AddRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  pub(super) fn compile_sub_expr(&mut self, target:&Token, token_a:&Token, token_b:&Token,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!("{}", ASMError::NotRegisterOrIdent(target.kind, target.span.start),),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a - b).to_le_bytes();

        self.program.extend_from_slice(&[
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
      self.program.extend_from_slice(&[OpCode::RvSubRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::RvSubRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::SubRI.into(),  target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::SubRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        self
          .program
          .extend_from_slice(&[OpCode::SubRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::SubRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  pub(super) fn compile_mul_expr(&mut self, target:&Token, token_a:&Token, token_b:&Token,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!("{}", ASMError::NotRegisterOrIdent(target.kind, target.span.start),),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a * b).to_le_bytes();

        self.program.extend_from_slice(&[
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
        self
          .program
          .extend_from_slice(&[OpCode::MulRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::MulRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        self
          .program
          .extend_from_slice(&[OpCode::MulRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        self
          .program
          .extend_from_slice(&[OpCode::MulRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        self
          .program
          .extend_from_slice(&[OpCode::MulRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::MulRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  pub(super) fn compile_div_expr(&mut self, target:Token, token_a:&Token, token_b:&Token,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!("{}", ASMError::NotRegisterOrIdent(target.kind, target.span.start),),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a / b).to_le_bytes();

        self.program.extend_from_slice(&[
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
      self.program.extend_from_slice(&[OpCode::RvDivRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::RvDivRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::DivRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::DivRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        self
          .program
          .extend_from_slice(&[OpCode::DivRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::DivRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  pub(super) fn compile_pow_expr(&mut self, target:&Token, token_a:&Token, token_b:&Token,) {
    let target = match target.kind {
      TokenKind::Register(reg,) => reg,
      TokenKind::Identifier(name,) => self.ident_to_reg(name, target.span,),
      _ => unreachable!("{}", ASMError::NotRegisterOrIdent(target.kind, target.span.start),),
    };

    match (token_a.kind, token_b.kind,) {
      (TokenKind::Num(a,), TokenKind::Num(b,),) => {
        // If both operands are immediate values perform the operation during
        // compilation
        let result = (a.powf(b,)).to_le_bytes();

        self.program.extend_from_slice(&[
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
      self.program.extend_from_slice(&[OpCode::RvPowRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Num(a,), TokenKind::Identifier(b,),) => {
        // If a is an immediate value and b is a variable
        let a = a.to_le_bytes();
        let b = self.ident_to_reg(b, token_b.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::RvPowRI.into(), target, b, a[0], a[1], a[2], a[3],],);
      }
      (TokenKind::Register(a,), TokenKind::Num(b,),) => {
        // If a is a register and b is an immediate value
        let b = b.to_le_bytes();
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::PowRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Identifier(a,), TokenKind::Num(b,),) => {
        // If a is a variable and b is an immediate value
        let b = b.to_le_bytes();
        let a = self.ident_to_reg(a, token_a.span,);
        #[rustfmt::skip]
      self.program.extend_from_slice(&[OpCode::PowRI.into(), target, a, b[0], b[1], b[2], b[3],],)
      }
      (TokenKind::Register(a,), TokenKind::Register(b,),) => {
        // If they are both registers
        self
          .program
          .extend_from_slice(&[OpCode::PowRR.into(), target, a, b,],)
      }
      (TokenKind::Identifier(a,), TokenKind::Identifier(b,),) => {
        // If they are both identifiers
        let a = self.ident_to_reg(a, token_a.span,);
        let b = self.ident_to_reg(b, token_b.span,);
        self
          .program
          .extend_from_slice(&[OpCode::PowRR.into(), target, a, b,],)
      }
      _ => {}
    }
  }

  /// Compiles the current comparison expression and returns the  [`Program`].
  pub(super) fn compile_cond_expr(&mut self,) -> Program {
    let op = self.next_token();
    let token_a = self.next_token();
    let token_b = self.next_token();
    self.compile_comparison_return(&op, &token_a, &token_b,)
  }

  pub(super) fn compile_for_loop_expr(&mut self,) {
    // Confirm the next token is an ident and eat it
    // This ident is discarded because the loop_variable uses the LOOP reg
    let ident = self.tokens.next().unwrap();
    match ident.unwrap_ident() {
      Some(_,) => {}
      None => panic!("{}", ASMError::MissingLoopVar(ident.span.start, ident.kind)),
    }

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
    #[rustfmt::skip]
  self.program.extend_from_slice(&[
    OpCode::Load.into(), LOOP as u8, start[0], start[1], start[2], start[3],
  ],);

    // Set the return address
    let ret = (self.program.len() as f32).to_le_bytes();

    // Compile the block
    // self.program.extend_from_slice(self.compile_block().as_slice(),);
    self.compile_block();

    #[rustfmt::skip]
  self.program.extend_from_slice(&[
    // Increment the counter by the value of 1f32 in le bytes = [0, 0, 128, 63,]
    OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
    // Compare the counter to the range's end and store in EQ
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, end[0], end[1], end[2], end[3],
    // JZ EQ to the begining of the loop
    OpCode::Jz.into(), ret[0], ret[1], ret[2], ret[3], EQ as u8,
  ],);
  }

  pub(super) fn compile_loop_expr(&mut self,) {
    // Set the return address
    let ret = (self.program.len() as f32).to_le_bytes();

    // Compile the block contaning the LOOP's contents and add it to the
    // main program
    self.compile_block();

    // Jump to the `ret` address
    self
      .program
      .extend_from_slice(&[OpCode::Jmp.into(), ret[0], ret[1], ret[2], ret[3],],);
  }

  /// Compiles the block making up the body of an `if` expression.
  pub(super) fn compile_if_body_expr(&mut self,) {
    if let TokenKind::Bool(b,) = self.tokens.peek().unwrap().kind {
      // Make the bool the current token
      self.next_token();
      if b {
        // If the cond is `true`, just compile the block that makes up its body
        self.compile_block();
        // Also devour any following else block
        if self.tokens.peek().unwrap().kind == TokenKind::Else {
          // Must explicitly get rid of the current token because it is the curly bracket
          self.next_token();
          self.eat_current_instruction();
        }
      }
      else {
        // If the cond is `false` just eat the if
        self.eat_block();
        // If there is an else block compile the code
        if self.tokens.peek().unwrap().kind == TokenKind::Else {
          // Must explicitly get rid of the current token because it is the curly bracket
          self.next_token();
          self.compile_current_instruction();
        }
      }
      return;
    }
    // Compile the condition
    let cond = self.compile_cond_expr();
    self.program.extend_from_slice(cond.as_slice(),);

    // Check the condition use a JZ to jump to the end of the IF expression
    // if it is false.
    // Use a defered patch in place of the end of the expression.
    self.program.extend_from_slice(&[OpCode::Jz.into(), EQ as u8,],);
    let patch_idx = self.deferred.reserve(self.program.len(), &mut self.program,);

    // Compile the block
    self.compile_block();

    // Update the deferred patch
    self.deferred.update_target(patch_idx, self.program.len(),);
  }
}
