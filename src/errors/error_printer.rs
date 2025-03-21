use crate::{errors::ASMError, src_file::SourceFile};
use std::{io::Write, process};

// Refactor:
// - Figure out if there is a more robust way to print the arrow by using the
//   index.

pub struct ErrorPrinter;

impl ErrorPrinter {
  // Needs to take a more generic error so it can print errors that arent for the
  // assembler

  /// Prints the error message and exits the process instead of panicking
  pub(crate) fn graceful_exit<W,>(w:W, src:&SourceFile, err:ASMError,) -> !
  where W: Write {
    Self::print(w, src, err,);
    process::exit(0,)
  }

  /// Prints an Error to the provided [`Write`]r.
  pub(crate) fn print<W,>(mut w:W, src:&SourceFile, err:ASMError,)
  where W: Write {
    // Scan the src, discard everything before a '\n' each time one is encounterd
    let loc = err.span();
    // If there is a path place it at the top of the error message.
    let mut buff = String::new();
    for (idx, ch,) in src.source_str().char_indices() {
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

    // If there is a path, show it
    match src.path() {
      Some(path,) => {
        writeln!(
          w,
          "{}",
          &format!("{}:{}:{}:", path.to_string_lossy(), loc.start.ln, loc.start.col)
        )
        .unwrap();
      }
      None => {}
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
}
