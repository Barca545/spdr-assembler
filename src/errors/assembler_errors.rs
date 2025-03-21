use crate::{
  symbol_table::Ty,
  tokenizer::{Span, Token, TokenKind},
};
use thiserror::Error;

#[derive(Debug, Error,)]
pub enum ASMError<'e,> {
  #[error("\x1b[93mUNRECOGNIZED TOKEN:\x1b[0m '{token}' {} is not a legal token.", span.start)]
  UnrecognizedToken { token:String, span:Span, },
  #[error("\x1b[93mNOT AN OPCODE:\x1b[0m {} {} cannot be used as the basis of an opcode.",token.kind, token.span.start)]
  NotAnOpcode { token:Token, },
  #[error("\x1b[93mUNDECLARED Identifier:\x1b[0m {ident} {} is not declared as an identifier before use.", span.start)]
  UndeclaredIdentifier { ident:&'e str, span:Span, },
  #[error("\x1b[93mINVALID COMPARISON OPERATOR:\x1b[0m {} {} is not a valid comparison operator.", token.kind, token.span.start)]
  InvalidComparison { token:Token, },
  #[error(
    "\x1b[93mINVALID IMMEDIATE TYPE:\x1b[0m Immediate value must be a boolean or a number not {} {}.", token.kind, token.span.start
  )]
  InvalidImmediateType { token:Token, },
  #[error("\x1b[93mMISSING KEYWORD:\x1b[0m The identifier in a {0} loop must be followed by {1} not {2}")]
  MissingKwd(TokenKind, TokenKind, TokenKind,),
  #[error("\x1b[93mMISSING LOOP VARIABLE:\x1b[0m For loops must have a loop variable. The loop defined here {} is followed by {}.", span.start, token)]
  MissingLoopVar { token:TokenKind, span:Span, },
  #[error(
    "\x1b[93mMISSING FUNCTION NAME:\x1b[0m A function declaration must be followed by an identifier, not `{}` {}.",token.kind, token.span.start
  )]
  MissingFnName { token:Token, },
  #[error("\x1b[93mNO NAME:\x1b[0m A function call must be followed by an identifier, not `{}` {}",token.kind, token.span.start)]
  NoNameCall { token:Token, },
  // Can these be aggregated?
  #[error("\x1b[93mNOT REGISTER OR IDENTITY:\x1b[0m {} {} is not a register or an identifier.", token.kind, token.span.start)]
  NotRegisterOrIdent { token:Token, },
  #[error("\x1b[93mNOT RANGE:\x1b[0m {} {} is not a range.", token.kind, token.span.start)]
  NotRange { token:Token, },
  #[error("\x1b[93mNOT FUNCTION:\x1b[0m Expected identity to be a function; {0} is not a function.")]
  NotFunction(Ty,),
  #[error("\x1b[93mUNAVAILABLE FUNCTION NAME:\x1b[0m The name {name} {} is already in use.", span.start)]
  UnavailableFunctionName { name:&'e str, span:Span, },
  #[error("\x1b[93mUNDEFINED FUNCTION:\x1b[0m Cannot use {name} {} without defining it.", span.start)]
  UndefinedFunction { name:&'e str, span:Span, },
  #[error(
    "\x1b[93mUNREGISTERED EXTERNAL CALL:\x1b[0m The name {name} {} is not associated with a registered external function call.", span.start
  )]
  UnregistedSyscall { name:&'e str, span:Span, },
  #[error("\x1b[93mINVALID MATH ARGUMENTS:\x1b[0m {} {} must be followed by identifiers or numbers {} {} do not fit the pattern.", operation.kind, operation.span.start, arg1.kind, arg2.kind)]
  InvalidMathArgs {
    operation:Token, arg1:Token, arg2:Token,
  },
  #[error("{} {} is not a Label or Index", target, span.start)]
  InvalidJumpTarget { target:&'e str, span:Span, },
}

impl<'e,> ASMError<'e,> {
  pub fn span(&self,) -> Span {
    match self {
      ASMError::UnrecognizedToken { span, .. } => *span,
      ASMError::NotAnOpcode { token, .. } => token.span,
      ASMError::UndeclaredIdentifier { span, .. } => *span,
      ASMError::InvalidComparison { token, } => token.span,
      ASMError::InvalidImmediateType { token, .. } => token.span,
      ASMError::MissingKwd(..,) => todo!(),
      ASMError::MissingLoopVar { span, .. } => *span,
      ASMError::MissingFnName { token, .. } => token.span,
      ASMError::NoNameCall { token, .. } => token.span,
      ASMError::NotRegisterOrIdent { token, .. } => token.span,
      ASMError::NotRange { token, } => token.span,
      ASMError::NotFunction(..,) => todo!(),
      ASMError::UnavailableFunctionName { span, .. } => *span,
      ASMError::UnregistedSyscall { span, .. } => *span,
      ASMError::UndefinedFunction { span, .. } => *span,
      ASMError::InvalidMathArgs { operation, .. } => operation.span,
      ASMError::InvalidJumpTarget { span, .. } => *span,
    }
  }
}
