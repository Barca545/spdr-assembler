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
