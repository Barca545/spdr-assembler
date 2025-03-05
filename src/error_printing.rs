use crate::assembler_errors::ASMError;

// Refactor:
// - Figure out if there is a more robust way to print the arrow by using the
//   index.

// TODO:
// - Figure out if span is supposed to cover the whole line or thing you'd want
//   to print to show an error. How does rustc generate a span?

pub(crate) fn print_error(src:&str, err:ASMError,) {
  println!("{}", err);
  // Split the source by lines and print only the valid bit?
  // Scan the src, discard everything before a '\n' each time one is encounterd
  let loc = err.loc();
  let mut buff = String::new();
  for (idx, ch,) in src.char_indices() {
    if idx > loc.idx as usize {
      break;
    }
    if ch == '\n' {
      buff.clear();
    }
    else {
      buff.push(ch,);
    }
  }

  println!("{}", buff);
  let arrow_len = (loc.col as usize).checked_sub(1,).unwrap_or(0,);
  println!("{}", "-".repeat(arrow_len,) + "^");
}

#[cfg(test)]
mod test {
  use super::print_error;
  use crate::{assembler_errors::ASMError, tokenizer::Location};

  #[test]
  fn error_printing_from_raw_input() {
    let src = include_str!(
      "C:\\Users\\jamar\\Documents\\Hobbies\\Coding\\galaxy-macro-asm\\src\\spdr_error_test.spdr"
    );
    let loc = Location { idx:59, ln:5, col:9, };
    let err = ASMError::UnrecognizedToken(".".to_string(), loc,);

    print_error(src, err,);

    // Check the output sent to stdout ==
    // UNRECOGNIZED TOKEN: . (ln 5 col 9) is not a legal token.
    // var b = ;
    // --------^

    unimplemented!("Figure out how to compare the outputs for equality");
  }
}
