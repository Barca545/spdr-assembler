use crate::Lexer;
use crate::{
  interner::intern,
  tokenizer::{Location, Span, Token, TokenKind},
};
use std::io;

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
  let tokens = Lexer::new(src,).tokenize(io::stdout(),);
  assert_eq!(tokens[0].kind, TokenKind::Register(15));
}

#[test]
fn test_comments() {
  let src = "// 15, 98, 70 \r\n70";

  let tokens = Lexer::new(src,).tokenize(io::stdout(),);

  assert_eq!(tokens.len(), 2);
  assert_eq!(tokens[0].kind, TokenKind::Num(70.0));
  assert_eq!(tokens[0].span, Span::new([16, 2, 1], [17, 2, 2]));
}

#[test]
fn test_range() {
  let src = "0..5 0..=17";

  let mut lex = Lexer::new(src,);
  let tokens = lex.tokenize(io::stdout(),);

  assert_eq!(tokens[0].kind, TokenKind::Range { start:0, end:4 });
  assert_eq!(tokens[0].span, Span::new([0, 1, 1], [3, 1, 4]));

  assert_eq!(tokens[1].kind, TokenKind::Range { start:0, end:17 });
  assert_eq!(tokens[1].span, Span::new([5, 1, 6], [10, 1, 11]));
}

#[test]
fn test_numbers() {
  let src = "97.65 5.6";

  let tokens = Lexer::new(src,).tokenize(io::stdout(),);

  assert_eq!(tokens[0].kind, TokenKind::Num(97.65));
  assert_eq!(tokens[0].span, Span::new([0, 1, 1], [4, 1, 5]));

  assert_eq!(tokens[1].kind, TokenKind::Num(5.6));
  assert_eq!(tokens[1].span, Span::new([6, 1, 7], [8, 1, 9]));
}

#[test]
fn test_labels() {
  let src = "label_test:";

  let mut lex = Lexer::new(src,);
  let tokens = lex.tokenize(io::stdout(),);

  assert_eq!(tokens[0].kind, TokenKind::Label(intern("label_test")));
  assert_eq!(tokens[0].span, Span::new([0, 1, 1], [9, 1, 10]))
}

#[test]
fn test_tokenize() {
  let src = include_str!("../test/test_tokens.spdr");

  let mut lex = Lexer::new(src,);

  let tokens = lex.tokenize(io::stdout(),);

  assert_eq!(tokens[0].kind, TokenKind::Var);
  assert_eq!(tokens[0].span, Span::new([0, 1, 1], [2, 1, 3]));

  assert_eq!(tokens[1].kind, TokenKind::Identifier(0));
  assert_eq!(tokens[1].span, Span::new([4, 1, 5], [6, 1, 7]));

  assert_eq!(tokens[2].kind, TokenKind::Num(15.0));
  assert_eq!(tokens[2].span, Span::new([8, 1, 9], [9, 1, 10]));

  assert_eq!(tokens[3].kind, TokenKind::If);
  assert_eq!(tokens[3].span, Span::new([12, 2, 1], [13, 2, 2]));

  assert_eq!(tokens[4].kind, TokenKind::Gt);
  assert_eq!(tokens[4].span, Span::new([15, 2, 4], [16, 2, 5]));

  assert_eq!(tokens[5].kind, TokenKind::Identifier(0));
  assert_eq!(tokens[5].span, Span::new([18, 2, 7], [20, 2, 9]));

  assert_eq!(tokens[6].kind, TokenKind::Num(14.0));
  assert_eq!(tokens[6].span, Span::new([22, 2, 11], [23, 2, 12]));

  assert_eq!(tokens[7].kind, TokenKind::LCurlyBracket);
  assert_eq!(tokens[7].span, Span::new([25, 2, 14], [25, 2, 14]));

  assert_eq!(tokens[8].kind, TokenKind::Call);
  assert_eq!(tokens[8].span, Span::new([30, 3, 3], [33, 3, 6]));

  assert_eq!(tokens[9].kind, TokenKind::Identifier(1));
  assert_eq!(tokens[9].span, Span::new([35, 3, 8], [37, 3, 10]));

  assert_eq!(tokens[10].kind, TokenKind::RCurlyBracket);
  assert_eq!(tokens[10].span, Span::new([40, 4, 1], [40, 4, 1]));

  assert_eq!(tokens[11].kind, TokenKind::Else);
  assert_eq!(tokens[11].span, Span::new([43, 5, 1], [46, 5, 4]));

  assert_eq!(tokens[12].kind, TokenKind::If);
  assert_eq!(tokens[12].span, Span::new([48, 5, 6], [49, 5, 7]));

  assert_eq!(tokens[13].kind, TokenKind::Lt);
  assert_eq!(tokens[13].span, Span::new([51, 5, 9], [52, 5, 10]));

  assert_eq!(tokens[14].kind, TokenKind::Identifier(0));
  assert_eq!(tokens[14].span, Span::new([54, 5, 12], [56, 5, 14]));

  assert_eq!(tokens[15].kind, TokenKind::Num(4.0));
  assert_eq!(tokens[15].span, Span::new([58, 5, 16], [58, 5, 16]));

  assert_eq!(tokens[16].kind, TokenKind::LCurlyBracket);
  assert_eq!(tokens[16].span, Span::new([60, 5, 18], [60, 5, 18]));

  assert_eq!(tokens[17].kind, TokenKind::Add);
  assert_eq!(tokens[17].span, Span::new([65, 6, 3], [67, 6, 5]));

  assert_eq!(tokens[18].kind, TokenKind::Identifier(0));
  assert_eq!(tokens[18].span, Span::new([69, 6, 7], [71, 6, 9]));

  assert_eq!(tokens[19].kind, TokenKind::Identifier(0));
  assert_eq!(tokens[19].span, Span::new([73, 6, 11], [75, 6, 13]));

  assert_eq!(tokens[20].kind, TokenKind::Num(90.0));
  assert_eq!(tokens[20].span, Span::new([77, 6, 15], [78, 6, 16]));

  assert_eq!(tokens[21].kind, TokenKind::RCurlyBracket);
  assert_eq!(tokens[21].span, Span::new([81, 7, 1], [81, 7, 1]));
}

#[test]
fn tokenizer_errors_print() {
  let src = include_str!("../../src/test/spdr_error_test.spdr");
  let mut lex = Lexer::new(src,);
  let mut out = Vec::new();
  let _ = lex.tokenize(&mut out,);

  let output = String::from_utf8(out,).unwrap();

  let expected = format!(
      "\x1b[93mUNRECOGNIZED TOKEN:\x1b[0m ';ytx' {} is not a legal token.\nSub $14 ;ytx\n--------\x1b[31m^^^^\x1b[0m\n",
      Location { idx:8, ln:1, col:9, }
    );

  assert_eq!(&output, &expected);

  // Just printing so ppl testing can get the vis
  print!("{}", output);
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
