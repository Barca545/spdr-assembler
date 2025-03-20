use super::{Location, Span, Token, TokenKind};
use crate::{assembler_errors::ASMError, error_printing::print_error, interner::intern};
use eyre::Result;
use std::io::Write;

// Refactor:
// - See if the next_char_satisfies => eat_current sequence could be one
//   function
// - Turn panics into errors
// - Add error printing/handling
// - Test error handling
// - Update tokens
// - Currently the tokenizer does not work if there is a space at the beginning
//   of the file because eat_while does not run if the current token is Null
// - For mono tokens currently their creation must be follow with
//   self.eat_current() so the next character is a character and not white
//   space. This feels brittle but without it an infinite loop occurs, I am
//   unclear why
// - Catching a raw register should error if the declared register is a reserved
//   reg
// - Not sure I need Jz Jmp and Jnz tokens

/// String terminator
const NULL_CHAR:char = '\0';

pub(crate) struct Lexer {
  pub(crate) src:Vec<char,>,
  /// The current index the in `src` the Lexer is reading.
  pub(crate) current_char:char,
  pub(crate) current:usize,
  // The next index the in `src` the Lexer will ​read.
  pub(crate) next:usize,
  /// The ln of the current character.
  pub(crate) ln:usize,
  /// The line of the current character.
  pub(crate) col:usize,
}

impl Lexer {
  pub(crate) fn new(src:&str,) -> Self {
    let mut src = src.chars().into_iter().collect::<Vec<char,>>();
    // Add a terminator to the end of the input
    src.push(NULL_CHAR,);
    let current_char = src[0];

    Lexer {
      src,
      current_char,
      current:0,
      next:1,
      ln:1,
      col:1,
    }
  }

  /// Returns the next char in the `src`.
  #[inline(always)]
  fn peek_next_char(&self,) -> Option<char,> {
    if self.next < self.src.len() {
      Some(self.src[self.next],)
    }
    else {
      None
    }
  }

  /// Eat the current [`char`].
  fn eat_current(&mut self,) {
    // Update the current line and col
    // This might have to be updated given window's weirdness with \r\n
    if self.current_char == '\n' {
      self.ln += 1;
      self.col = 1;
    }
    else {
      self.col += 1;
    }

    // Update current_char, current, and next
    self.current = self.next;
    self.next += 1;
    self.current_char = self.src[self.current];
  }

  /// If the current char is a '$' parses the numbers following it as a
  /// [TokenKind::Register].
  fn tokenize_register(&mut self,) -> Result<Token,> {
    // Need to move off the non-numeric token
    self.eat_current();
    let (wrd, span,) = self.eat_while(|ch| ch.is_numeric(),);

    match wrd.parse::<u8>() {
      Ok(idx,) => Ok(Token {
        kind:TokenKind::Register(idx,),
        span,
      },),
      Err(err,) => Err(err.into(),),
    }
  }

  /// Use the current char as the basis of the next token.
  pub(crate) fn next_token(&mut self,) -> Result<Token,> {
    // Finish lexing if there are no more characters left
    if self.current_char == NULL_CHAR {
      return Ok(Token {
        kind:TokenKind::Eof,
        span:Span::from_single_char(self.loc(),),
      },);
    }

    // Eat string: If an " is observed, add the next characters as chars until the
    // next " is encountered
    if self.current_char == '"' {
      let (str, span,) = self.eat_while(|ch| ch != '"',);
      return Ok(Token {
        kind:TokenKind::String(intern(&str,),),
        span,
      },);
    }

    // Determine if the character is a single
    let tokenkind = match self.current_char {
      // Check against single char operators
      NULL_CHAR => Some(TokenKind::Eof,),
      '{' => Some(TokenKind::LCurlyBracket,),
      '}' => Some(TokenKind::RCurlyBracket,),
      '[' => Some(TokenKind::LBracket,),
      ']' => Some(TokenKind::RBracket,),
      ',' => Some(TokenKind::Comma,),
      // Catch a raw register declaration
      '$' => return self.tokenize_register(),
      _ => None,
    };

    if let Some(kind,) = tokenkind {
      let token = Ok(Token {
        kind,
        span:Span::from_single_char(self.loc(),),
      },);
      // Needed so the next character is a character and not white space. This feels
      // error prone but without it an infinite loop occurs, I am unclear why
      self.eat_current();
      return token;
    }

    // If the character is alphabetic it might be a keyword or identifier
    if self.current_char.is_alphabetic() {
      // Second condition works because a char is only every one char so it won't
      // match ":_" by accident only ':' or '_'
      let (wrd, mut span,) = self.eat_while(|ch| ch.is_alphabetic() || ":_".contains(ch,),);
      // Catch labels by checking ends with :
      if wrd.ends_with(':',) {
        let kind = TokenKind::Label(intern(&wrd[0..wrd.len() - 1],),);
        span.end.idx = span.end.idx - 1;
        span.end.col = span.end.col - 1;
        return Ok(Token { kind, span, },);
      }

      // Match against kwds
      let kind = match wrd.to_uppercase().as_str() {
        "VAR" => TokenKind::Var,
        "ADD" => TokenKind::Add,
        "SUB" => TokenKind::Sub,
        "MUL" => TokenKind::Mul,
        "DIV" => TokenKind::Div,
        "POW" => TokenKind::Pow,
        "IF" => TokenKind::If,
        "ELSE" => TokenKind::Else,
        "FN" => TokenKind::Fn,
        "LOOP" => TokenKind::Loop,
        "WHILE" => TokenKind::While,
        "FOR" => TokenKind::For,
        "IN" => TokenKind::In,
        "EQ" => TokenKind::Eq,
        "GT" => TokenKind::Gt,
        "LT" => TokenKind::Lt,
        "GEQ" => TokenKind::Geq,
        "LEQ" => TokenKind::Leq,
        "NOT" => TokenKind::Not,
        "TRUE" => TokenKind::Bool(true,),
        "FALSE" => TokenKind::Bool(false,),
        "JMP" => TokenKind::Jmp,
        "JNZ" => TokenKind::Jnz,
        "CALL" => TokenKind::Call,
        "SYSCALL" => TokenKind::SysCall,
        "RET" => TokenKind::Ret,
        "WMEM" => TokenKind::Wmem,
        "RMEM" => TokenKind::Rmem,
        "ALLOC" => TokenKind::Alloc,
        "DEALLOC" => TokenKind::Dealloc,
        "LOAD" => TokenKind::Load,
        "COPY" => TokenKind::Copy,
        "MEMCPY" => TokenKind::MemCpy,
        "NOOP" => TokenKind::Noop,
        "PUSH" => TokenKind::Push,
        "POP" => TokenKind::Pop,
        "POPR" => TokenKind::PopR,
        // Return as an identifer if no kwd match
        _ => TokenKind::Identifier(intern(&wrd,),),
      };
      // Return the token early
      return Ok(Token { kind, span, },);
    }

    if self.current_char.is_numeric() {
      // Tokenize as a number
      let (mut num, mut span,) = self.eat_while(|ch| ch.is_numeric(),);

      // Check if the number is part of a range or a float
      if self.current_char == '.' {
        self.eat_current();
        // For a float, the period will be followed by a numeric char
        // This is necesary because ch.is_numeric() will stop when it encounters a '.'
        // in a float
        if self.current_char.is_numeric() {
          let (end_num, end_span,) = self.eat_while(|ch| ch.is_numeric(),);
          num = format!("{num}.{end_num}");
          span.end = end_span.end
        }
        // For a range, the next char will be a period
        else if self.current_char == '.' {
          // Eat the period
          self.eat_current();

          let is_inclusive = self.current_char == '=';

          // Make sure to eat the equals sign if the range is inclusive
          if is_inclusive {
            self.eat_current();
          }

          // Get the ends of
          let (end, end_span,) = self.eat_while(|ch| ch.is_numeric(),);

          // Make sure it only includes the end number if the range is inclusive
          let end = if is_inclusive {
            end.parse::<u32>().unwrap()
          }
          else {
            end.parse::<u32>().unwrap() - 1
          };

          let kind = TokenKind::Range {
            start:num.parse().unwrap(),
            end,
          };
          let span = Span {
            start:span.start,
            end:end_span.end,
          };
          return Ok(Token { kind, span, },);
        }
      }

      return Ok(Token {
        kind:TokenKind::Num(num.as_str().parse().unwrap(),),
        span,
      },);
    }

    // If this point is reached throw an error
    // Eat until whitespace is encountered. This is the error token.
    let (token, span,) = self.eat_while(|ch| !ch.is_whitespace(),);
    // self.eat_current();
    Err(ASMError::UnrecognizedToken { token, span, }.into(),)
  }

  /// Eats characters as long as the current character satisfies the predicate.
  ///
  /// Returns a string and the [`Span`] of the string's underlying characters.
  pub(crate) fn eat_while<P,>(&mut self, mut predicate:P,) -> (String, Span,)
  where P: FnMut(char,) -> bool {
    let start = self.loc();
    // Location of the last character in the string created by this function
    let mut end = self.loc();

    while self.current_char != NULL_CHAR && predicate(self.src[self.current],) {
      // The end of the span is updated each time we loop. Comes before because
      // `eat_current` sents the current token to what is `next` at this point
      end = self.loc();
      self.eat_current();
    }

    (
      self.src[start.idx as usize..=end.idx as usize].iter().collect(),
      Span { start, end, },
    )
  }

  /// Returns the `Lexer`'s current location.
  fn loc(&self,) -> Location {
    Location {
      idx:self.current as u16,
      ln:self.ln as u16,
      col:self.col as u16,
    }
  }

  /// Checks whether the `current_char` is the beginning of a comment.
  fn is_comment(&self,) -> bool {
    // Check if current character is a '/'
    self.current_char == '/' && self.peek_next_char().map_or(false, |ch| ch == '/',)
  }

  /// Consume characters until the current character does not have the
  /// [`White_Space`](https://www.unicode.org/reports/tr31/) property.
  pub(crate) fn skip_whitespace(&mut self,) {
    self.eat_while(|ch| ch.is_whitespace(),);
  }

  pub fn tokenize<W:Write,>(&mut self, mut w:W,) -> Vec<Token,> {
    let mut tokens = Vec::new();
    let mut errs = Vec::new();

    'tokenize: loop {
      // Check if the line is a comment and skip the line if so
      self.skip_whitespace();
      if self.is_comment() {
        // Skip the line by eating all the characters until a line break is encountered
        self.eat_while(|ch| ch != '\n',);
        continue 'tokenize;
      }
      match self.next_token() {
        Ok(token,) if token.kind == TokenKind::Eof => {
          tokens.push(token,);
          break 'tokenize;
        }
        Ok(token,) => tokens.push(token,),
        Err(err,) => errs.push(err,),
      }
    }

    for err in errs {
      let src = String::from_iter(&self.src,);
      let err = err.downcast::<ASMError>().unwrap();
      print_error(&mut w, &src, err,);
    }

    tokens
  }
}
