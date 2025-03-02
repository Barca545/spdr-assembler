use super::{Location, Span, Token, TokenKind};
use crate::{assembler_errors::ASMError, interner::intern};
use eyre::Result;
use std::str;

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

pub struct Lexer {
  src:Vec<char,>,
  /// The current index the in `src` the Lexer is reading.
  current_char:char,
  current:usize,
  // The next index the in `src` the Lexer will ​read.
  next:usize,
  /// The ln of the current character.
  ln:usize,
  /// The line of the current character.
  col:usize,
}

impl Lexer {
  pub fn new(src:&str,) -> Self {
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
  fn next_char(&self,) -> char {
    self.src[self.next]
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

  /// Check whether the next character in `src` satisfies the function `f`.
  fn next_char_satisfies<F,>(&self, f:F,) -> bool
  where F: Fn(char,) -> bool {
    f(self.next_char(),)
  }

  ///If the current `current_char` is a math symbol ('+','-','*','/') determine
  /// whether it is part of a `_=` [`TokenKind`] and return the [`Token`].
  fn tokenize_math_sym(&mut self,) -> Result<Token,> {
    // Fix how these sort of merge symbols are tokenized. Right now it counts
    // them as one char and assigns them a 1 len span but they should have a
    // 2 len span
    let kind = if self.next_char() == ' ' {
      match self.current_char {
        '+' => TokenKind::Plus,
        '-' => TokenKind::Minus,
        '*' => TokenKind::Star,
        '/' => TokenKind::Slash,
        _ => unreachable!(),
      }
    }
    else {
      // Confirm the next character is an '='
      if self.next_char() != '=' {
        return Err(
          ASMError::IllegalMathToken {
            current:self.current_char,
            next:self.next_char(),
          }
          .into(),
        );
      }

      match self.current_char {
        '+' => TokenKind::PlusEqual,
        '-' => TokenKind::MinusEqual,
        '*' => TokenKind::StarEqual,
        '/' => TokenKind::SlashEqual,
        _ => unreachable!(),
      }
    };

    let start = self.loc();
    self.eat_current();
    let end = self.loc();
    self.eat_current();

    let token = Token {
      kind,
      span:Span { start, end, },
    };

    // This is needed so the current char is not white space?
    self.eat_current();

    return Ok(token,);
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
  fn next_token(&mut self,) -> Result<Token,> {
    self.skip_whitespace();

    // Finish lexing if there are no more characters left
    if self.current_char == NULL_CHAR {
      return Ok(Token {
        kind:TokenKind::Eof,
        span:Span::from_single_char(self.loc(),),
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
      '=' => Some(TokenKind::EqualSign,),
      '+' | '-' | '*' | '/' => return self.tokenize_math_sym(),
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
        "CONST" => TokenKind::Const,
        "VAR" => TokenKind::Var,
        "ADD" => TokenKind::Add,
        "SUB" => TokenKind::Sub,
        "MUL" => TokenKind::Mul,
        "DIV" => TokenKind::Div,
        "POW" => TokenKind::Pow,
        "ADDRI" => TokenKind::AddRI,
        "SUBRI" => TokenKind::SubRI,
        "MULRI" => TokenKind::MulRI,
        "DIVRI" => TokenKind::DivRI,
        "POWRI" => TokenKind::PowRI,
        "ADDRR" => TokenKind::AddRR,
        "SUBRR" => TokenKind::SubRR,
        "MULRR" => TokenKind::MulRR,
        "DIVRR" => TokenKind::DivRR,
        "POWRR" => TokenKind::PowRR,
        "IF" => TokenKind::If,
        "ELSE" => TokenKind::Else,
        "FN" => TokenKind::Fn,
        "LOOP" => TokenKind::Loop,
        "WHILE" => TokenKind::While,
        "FOR" => TokenKind::For,
        "IN" => TokenKind::In,
        "EQRI" => TokenKind::EqRI,
        "GTRI" => TokenKind::GtRI,
        "EQRR" => TokenKind::EqRR,
        "GTRR" => TokenKind::GtRR,
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
    let loc = self.loc();
    panic!(
      "{}",
      ASMError::UnrecognizedToken(&self.current_char.to_string(), loc.ln, loc.col)
    )
  }

  /// Eats characters as long as the current character satisfies the predicate.
  ///
  /// Returns a string and the [`Span`] of the string's underlying characters.
  fn eat_while<P,>(&mut self, mut predicate:P,) -> (String, Span,)
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

  /// Consume characters until the current character does not have the
  /// [`White_Space`](https://www.unicode.org/reports/tr31/) property.
  fn skip_whitespace(&mut self,) {
    self.eat_while(|ch| ch.is_whitespace(),);
  }

  pub fn tokenize(&mut self,) -> Vec<Token,> {
    let mut tokens = Vec::new();
    let mut errs = Vec::new();

    'tokenize: loop {
      // Check if the line is a comment and skip the line if so
      if self.current_char == '/' && self.next_char_satisfies(|ch| ch == '/',) {
        // Skip the line by eating all the characters until a line break is encountered
        self.eat_while(|ch| ch != '\n',);
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

    if errs.len() != 0 {
      // Print the errors if they exist
      // Should panic after printing them all
    }

    tokens
  }
}

#[cfg(test)]
mod test {
  use super::Lexer;
  use crate::{
    interner::intern,
    tokenizer::{Location, Span, Token, TokenKind},
  };

  #[test]
  fn test_skip_whitespace() {
    let src = "
      var test = 18
    ";
    let mut lexer = Lexer::new(src,);
    lexer.skip_whitespace();

    assert_eq!(lexer.src[lexer.current], 'v');
  }

  #[test]
  fn test_eat_while() {
    let src = "var 90 }";

    let mut lex = Lexer::new(src,);

    let (wrd, span,) = lex.eat_while(|ch| ch.is_alphanumeric(),);

    assert_eq!(wrd, "var");
    assert_eq!(span, Span::new([0, 1, 1], [2, 1, 3]));

    lex.skip_whitespace();

    let (num, span,) = lex.eat_while(|ch| ch.is_numeric(),);

    assert_eq!(num, "90");
    assert_eq!(span, Span::new([4, 1, 5], [5, 1, 6]));

    lex.skip_whitespace();

    // This test confirms it doesn't eat the last character
    assert_eq!(lex.next_token().unwrap().kind, TokenKind::RCurlyBracket);
  }

  #[test]
  fn test_next_token() {
    let src = "var";

    let mut lex = Lexer::new(src,);

    let token = lex.next_token().unwrap();

    assert_eq!(
      token,
      Token {
        kind:TokenKind::Var,
        span:Span {
          start:Location { idx:0, ln:1, col:1 },
          end:Location { idx:2, ln:1, col:3 }
        }
      }
    );
  }

  #[test]
  fn test_register_annotation() {
    let src = "$15";

    let tokens = Lexer::new(src,).tokenize();

    assert_eq!(tokens[0].kind, TokenKind::Register(15));
  }

  #[test]
  fn test_comments() {
    let src = "// 15, 98, 70 \r\n70";

    let tokens = Lexer::new(src,).tokenize();

    assert_eq!(tokens.len(), 2);
    assert_eq!(tokens[0].kind, TokenKind::Num(70.0));
    assert_eq!(tokens[0].span, Span::new([16, 2, 1], [17, 2, 2]));
  }

  #[test]
  fn test_range() {
    let src = "0..5 0..=17";

    let mut lex = Lexer::new(src,);
    let tokens = lex.tokenize();

    assert_eq!(tokens[0].kind, TokenKind::Range { start:0, end:4 });
    assert_eq!(tokens[0].span, Span::new([0, 1, 1], [3, 1, 4]));

    assert_eq!(tokens[1].kind, TokenKind::Range { start:0, end:17 });
    assert_eq!(tokens[1].span, Span::new([5, 1, 6], [10, 1, 11]));
  }

  #[test]
  fn test_numbers() {
    let src = "97.65 5.6";

    let tokens = Lexer::new(src,).tokenize();

    assert_eq!(tokens[0].kind, TokenKind::Num(97.65));
    assert_eq!(tokens[0].span, Span::new([0, 1, 1], [4, 1, 5]));

    assert_eq!(tokens[1].kind, TokenKind::Num(5.6));
    assert_eq!(tokens[1].span, Span::new([6, 1, 7], [8, 1, 9]));

    dbg!("4.4".parse::<f32>().unwrap());
  }

  #[test]
  fn test_labels() {
    let src = "label_test:";

    let mut lex = Lexer::new(src,);
    let tokens = lex.tokenize();

    assert_eq!(tokens[0].kind, TokenKind::Label(intern("label_test")));
    assert_eq!(tokens[0].span, Span::new([0, 1, 1], [9, 1, 10]))
  }

  #[test]
  fn test_tokenize() {
    let src =
      include_str!("C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\galaxy-macro-asm\\src\\test_tokens.txt");

    let mut lex = Lexer::new(src,);

    let tokens = lex.tokenize();

    assert_eq!(tokens[0].kind, TokenKind::Var);
    assert_eq!(tokens[0].span, Span::new([0, 1, 1], [2, 1, 3]));

    assert_eq!(tokens[1].kind, TokenKind::Identifier(0));
    assert_eq!(tokens[1].span, Span::new([4, 1, 5], [6, 1, 7]));

    assert_eq!(tokens[2].kind, TokenKind::EqualSign);
    assert_eq!(tokens[2].span, Span::new([8, 1, 9], [8, 1, 9]));

    assert_eq!(tokens[3].kind, TokenKind::Num(15.0));
    assert_eq!(tokens[3].span, Span::new([10, 1, 11], [11, 1, 12]));

    assert_eq!(tokens[4].kind, TokenKind::If);
    assert_eq!(tokens[4].span, Span::new([14, 2, 1], [15, 2, 2]));

    assert_eq!(tokens[5].kind, TokenKind::Gt);
    assert_eq!(tokens[5].span, Span::new([17, 2, 4], [18, 2, 5]));

    assert_eq!(tokens[6].kind, TokenKind::Identifier(0));
    assert_eq!(tokens[6].span, Span::new([20, 2, 7], [22, 2, 9]));

    assert_eq!(tokens[7].kind, TokenKind::Num(14.0));
    assert_eq!(tokens[7].span, Span::new([24, 2, 11], [25, 2, 12]));

    assert_eq!(tokens[8].kind, TokenKind::LCurlyBracket);
    assert_eq!(tokens[8].span, Span::new([27, 2, 14], [27, 2, 14]));

    assert_eq!(tokens[9].kind, TokenKind::Call);
    assert_eq!(tokens[9].span, Span::new([32, 3, 3], [35, 3, 6]));

    assert_eq!(tokens[10].kind, TokenKind::Identifier(1));
    assert_eq!(tokens[10].span, Span::new([37, 3, 8], [39, 3, 10]));

    assert_eq!(tokens[11].kind, TokenKind::RCurlyBracket);
    assert_eq!(tokens[11].span, Span::new([42, 4, 1], [42, 4, 1]));

    assert_eq!(tokens[12].kind, TokenKind::Else);
    assert_eq!(tokens[12].span, Span::new([45, 5, 1], [48, 5, 4]));

    assert_eq!(tokens[13].kind, TokenKind::If);
    assert_eq!(tokens[13].span, Span::new([50, 5, 6], [51, 5, 7]));

    assert_eq!(tokens[14].kind, TokenKind::Lt);
    assert_eq!(tokens[14].span, Span::new([53, 5, 9], [54, 5, 10]));

    assert_eq!(tokens[15].kind, TokenKind::Identifier(0));
    assert_eq!(tokens[15].span, Span::new([56, 5, 12], [58, 5, 14]));

    assert_eq!(tokens[16].kind, TokenKind::Num(4.0));
    assert_eq!(tokens[16].span, Span::new([60, 5, 16], [60, 5, 16]));

    assert_eq!(tokens[17].kind, TokenKind::LCurlyBracket);
    assert_eq!(tokens[17].span, Span::new([62, 5, 18], [62, 5, 18]));

    assert_eq!(tokens[18].kind, TokenKind::Identifier(0));
    assert_eq!(tokens[18].span, Span::new([67, 6, 3], [69, 6, 5]));

    assert_eq!(tokens[19].kind, TokenKind::PlusEqual);
    assert_eq!(tokens[19].span, Span::new([71, 6, 7], [72, 6, 8]));

    assert_eq!(tokens[20].kind, TokenKind::Num(90.0));
    assert_eq!(tokens[20].span, Span::new([74, 6, 10], [75, 6, 11]));

    assert_eq!(tokens[21].kind, TokenKind::RCurlyBracket);
    assert_eq!(tokens[21].span, Span::new([78, 7, 1], [78, 7, 1]));
  }

  impl Span {
    fn new(start:[u16; 3], end:[u16; 3],) -> Self {
      Span {
        start:Location {
          idx:start[0],
          ln:start[1],
          col:start[2],
        },
        end:Location {
          idx:end[0],
          ln:end[1],
          col:end[2],
        },
      }
    }
  }

  #[test]
  fn test_error_printing() {
    unimplemented!()
  }
}
