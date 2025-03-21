mod assembler;
mod cli_integration;
mod errors;
mod interner;
mod patch;
mod src_file;
mod symbol_table;
mod test;
mod tokenizer;

use assembler::Assembler;

use std::{fs::read_to_string, io};

// Experiement with error printing

fn main() {
  let args = cli_integration::parse_arguments().unwrap();

  let src = read_to_string(args.path,).unwrap();

  let mut assembler = Assembler::new(&src, io::stdout(),);

  if let Some(header,) = args.header {
    // TODO: This should be able to take a PathBuf
    assembler.read_header(header,);
  }

  let program = assembler.compile();

  let output_file = &format!("{}/{}.spex", args.output.to_str().unwrap(), args.name);

  // TODO: Program should be able to take a PathBuf
  program.save(output_file,).unwrap();
}
