use crate::{
  errors::{ASMError, ErrorPrinter},
  src_file::SourceFile,
  tokenizer::{Location, Span},
};
use std::io;

#[test]
fn error_printing_from_raw_input() {
  let start = Location { idx:8, ln:1, col:9, };
  let end = Location {
    idx:11, ln:1, col:12,
  };
  let span = Span { start, end, };
  let err = ASMError::UnrecognizedToken {
    token:";ytx".to_string(),
    span,
  };

  let source = SourceFile::new_from_path("./src/test/spdr_error_test.spdr",);

  let mut w = Vec::new();
  ErrorPrinter::print(&mut w, &source, err,);

  let out = String::from_utf8(w,).unwrap();
  let expected = format!(
      "./src/test/spdr_error_test.spdr:1:9:\n\x1b[93mUNRECOGNIZED TOKEN:\x1b[0m ';ytx' {} is not a legal token.\nSub $14 ;ytx\n--------\x1b[31m^^^^\x1b[0m\n",
      span.start
    );
  assert_eq!(out, expected);

  let err = ASMError::UnrecognizedToken {
    token:";ytx".to_string(),
    span,
  };
  ErrorPrinter::print(io::stdout(), &source, err,);
}

#[test]
fn test_color() {
  println!("\x1b[93mError\x1b[0m");
}
