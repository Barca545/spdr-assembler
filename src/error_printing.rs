use crate::assembler_errors::ASMError;
use std::io::Write;

// Refactor:
// - Figure out if there is a more robust way to print the arrow by using the
//   index.

pub(crate) fn print_error<W,>(mut w:W, src:&str, err:ASMError,)
where W: Write {
  // Scan the src, discard everything before a '\n' each time one is encounterd
  let loc = err.span();
  let mut buff = String::new();
  for (idx, ch,) in src.char_indices() {
    if idx > loc.end.idx as usize {
      break;
    }
    if ch == '\n' {
      buff.clear();
    }
    else {
      buff.push(ch,);
    }
  }

  writeln!(w, "{}", err).unwrap();
  writeln!(w, "{}", buff).unwrap();
  let tail_len = (loc.start.col as usize).checked_sub(1,).unwrap_or(0,);
  // Plus one because `loc.end.col - loc.start.col` will always be one less than
  // the proper number of arrows
  let arrow_num = (loc.end.col - loc.start.col) as usize + 1;
  writeln!(
    w,
    "{}\x1b[31m{}\x1b[0m",
    "-".repeat(tail_len,),
    "^".repeat(arrow_num)
  )
  .unwrap();
}

#[cfg(test)]
mod test {
  use super::print_error;
  use crate::{assembler_errors::ASMError, tokenizer::Location, Span};
  use std::io;

  #[test]
  fn error_printing_from_raw_input() {
    let src = include_str!(
      "C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\spdr-assembler\\src\\test\\spdr_error_test.spdr"
    );
    let start = Location { idx:8, ln:1, col:9, };
    let end = Location {
      idx:11, ln:1, col:12,
    };
    let span = Span { start, end, };
    let err = ASMError::UnrecognizedToken {
      token:";ytx".to_string(),
      span,
    };

    let mut w = Vec::new();
    print_error(&mut w, src, err,);

    let out = String::from_utf8(w,).unwrap();
    let expected = format!(
      "\x1b[93mUNRECOGNIZED TOKEN:\x1b[0m ';ytx' {} is not a legal token.\nSub $14 ;ytx\n--------\x1b[31m^^^^\x1b[0m\n",
      span.start
    );
    assert_eq!(out, expected);

    let err = ASMError::UnrecognizedToken {
      token:";ytx".to_string(),
      span,
    };
    print_error(io::stdout(), src, err,);
  }

  #[test]
  fn test_color() {
    println!("\x1b[93mError\x1b[0m");
  }
}
