use crate::{assembler_errors::ASMError, interner::lookup};
use eyre::Result;
use std::fmt::{Debug, Display};

#[derive(Debug, PartialEq, Clone, Copy,)]
pub struct Span {
  /// The line and col the span begins.
  pub(crate) start:Location,
  /// The line and col the span ends.
  pub(crate) end:Location,
}

impl Span {
  pub fn from_single_char(loc:Location,) -> Self {
    Self { start:loc, end:loc, }
  }
}

#[derive(Debug, PartialEq, Clone, Copy,)]
pub struct Location {
  /// Index in the source string corresponding to this location
  pub(crate) idx:u16,
  pub(crate) ln:u16,
  pub(crate) col:u16,
}

#[derive(PartialEq, Clone, Copy,)]
pub enum TokenKind {
  LCurlyBracket,
  RCurlyBracket,
  LBracket,
  RBracket,
  Minus,
  MinusEqual,
  Plus,
  PlusEqual,
  Star,
  StarEqual,
  Slash,
  SlashEqual,
  EqualSign,
  In,
  Const,
  Var,
  Eq,
  Gt,
  Lt,
  Geq,
  Leq,
  Loop,
  While,
  For,
  If,
  Else,
  Fn,
  Num(f32,),
  Bool(bool,),
  Register(u8,),
  Identifier(u32,),
  Label(u32,),
  Range { start:u32, end:u32, },
  // These are pure opcodes
  Load,
  Copy,
  MemCpy,
  Add,
  Sub,
  Mul,
  Div,
  Pow,
  AddRI,
  SubRI,
  MulRI,
  DivRI,
  PowRI,
  AddRR,
  SubRR,
  MulRR,
  DivRR,
  PowRR,
  EqRI,
  GtRI,
  EqRR,
  GtRR,
  Not,
  Jmp,
  Jnz,
  Call,
  SysCall,
  Wmem,
  Rmem,
  Alloc,
  Dealloc,
  Ret,
  Push,
  Pop,
  PopR,
  Noop,
  Eof,
}

impl Debug for TokenKind {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    Display::fmt(&self, f,)
  }
}

impl Display for TokenKind {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    match self {
      Self::LCurlyBracket => write!(f, "LCurlyBracket"),
      Self::RCurlyBracket => write!(f, "RCurlyBracket"),
      Self::LBracket => write!(f, "LBracket"),
      Self::RBracket => write!(f, "RBracket"),
      Self::Minus => write!(f, "Minus"),
      Self::MinusEqual => write!(f, "MinusEqual"),
      Self::Plus => write!(f, "Plus"),
      Self::PlusEqual => write!(f, "PlusEqual"),
      Self::Star => write!(f, "Star"),
      Self::StarEqual => write!(f, "StarEqual"),
      Self::Slash => write!(f, "Slash"),
      Self::SlashEqual => write!(f, "SlashEqual"),
      Self::EqualSign => write!(f, "EqualSign"),
      Self::Load => write!(f, "Load"),
      Self::Const => write!(f, "Const"),
      Self::Var => write!(f, "Var"),
      Self::Add => write!(f, "Add"),
      Self::Sub => write!(f, "Sub"),
      Self::Mul => write!(f, "Mul"),
      Self::Div => write!(f, "Div"),
      Self::Pow => write!(f, "Pow"),
      Self::AddRI => write!(f, "AddRI"),
      Self::SubRI => write!(f, "SubRI"),
      Self::MulRI => write!(f, "MulRI"),
      Self::DivRI => write!(f, "DivRI"),
      Self::PowRI => write!(f, "PowRI"),
      Self::AddRR => write!(f, "AddRR"),
      Self::SubRR => write!(f, "SubRR"),
      Self::MulRR => write!(f, "MulRR"),
      Self::DivRR => write!(f, "DivRR"),
      Self::PowRR => write!(f, "PowRR"),
      Self::Not => write!(f, "Not"),
      Self::Eq => write!(f, "Eq"),
      Self::Gt => write!(f, "Gt"),
      Self::Lt => write!(f, "Lt"),
      Self::Geq => write!(f, "Geq"),
      Self::Leq => write!(f, "Leq"),
      Self::Loop => write!(f, "Loop"),
      Self::While => write!(f, "While"),
      Self::For => write!(f, "For"),
      Self::If => write!(f, "If"),
      Self::Else => write!(f, "Else"),
      Self::Fn => write!(f, "Fn"),
      Self::Register(arg0,) => write!(f, "Register({arg0})",),
      Self::Identifier(arg0,) => write!(f, "Identifier({})", &lookup(*arg0)),
      Self::Num(arg0,) => write!(f, "Num({})", arg0),
      Self::Bool(arg0,) => write!(f, "Bool({})", arg0),
      Self::Label(arg0,) => write!(f, "Label({})", &lookup(*arg0)),
      Self::Range { start, end, } => write!(f, "Range({start}..{end})"),
      Self::In => write!(f, "In"),
      Self::EqRI => write!(f, "EqRI"),
      Self::GtRI => write!(f, "GtRI"),
      Self::EqRR => write!(f, "EqRR"),
      Self::GtRR => write!(f, "GtRR"),
      Self::Jmp => write!(f, "Jmp"),
      Self::Jnz => write!(f, "Jnz"),
      Self::Call => write!(f, "Call"),
      Self::SysCall => write!(f, "SysCall"),
      Self::Ret => write!(f, "Ret"),
      Self::Wmem => write!(f, "Wmem"),
      Self::Rmem => write!(f, "Rmem"),
      Self::Alloc => write!(f, "Alloc"),
      Self::Dealloc => write!(f, "Dealloc"),
      Self::Push => write!(f, "Push"),
      Self::Pop => write!(f, "Pop"),
      Self::PopR => write!(f, "PopR"),
      Self::MemCpy => write!(f, "MemCpy"),
      Self::Copy => write!(f, "Copy"),
      Self::Noop => write!(f, "Noop"),
      Self::Eof => write!(f, "Eof"),
    }
  }
}

#[derive(Debug, PartialEq, Clone, Copy,)]
pub struct Token {
  pub(crate) kind:TokenKind,
  pub(crate) span:Span,
}

impl Token {
  /// Return a result containing start and stop of a [`TokenKind::Range`].
  pub fn unwrap_range(&self,) -> Result<(u32, u32,),> {
    match self.kind {
      TokenKind::Range { start, end, } => Ok((start, end,),),
      _ => Err(ASMError::NotRange(self.kind, self.span.start.ln, self.span.start.col,).into(),),
    }
  }

  /// Return a result containing the idx of an [`TokenKind::Identifier`].
  pub fn unwrap_ident(&self,) -> Result<u32,> {
    match self.kind {
      TokenKind::Identifier(idx,) => Ok(idx,),
      _ => Err(ASMError::NotRegisterOrIdent(self.kind, self.span.start.ln, self.span.start.col,).into(),),
    }
  }

  /// Return a result containing the idx of an [`TokenKind::Bool`].
  pub fn unwrap_bool(&self,) -> Result<bool,> {
    match self.kind {
      TokenKind::Bool(b,) => Ok(b,),
      _ => Err(ASMError::NotRegisterOrIdent(self.kind, self.span.start.ln, self.span.start.col,).into(),),
    }
  }
}
