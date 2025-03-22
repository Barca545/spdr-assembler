mod assembler;
mod cli_integration;
mod errors;
mod interner;
mod patch;
mod src_file;
mod symbol_table;
mod test;
mod tokenizer;

use assembler::AssemblerBuilder;
use errors::ErrorPrinter;
use std::path::PathBuf;

// TODO: Could I use a build.rs to update the documentation in the Readme based
// on the HELP const?

fn main() {
  let args = cli_integration::parse_arguments().unwrap();

  let mut builder = AssemblerBuilder::new();
  // If the app args say they want an immediate source pause execution and wait
  // for the user to enter their code:
  if let Some(str,) = args.str {
    match builder.add_src_str(str,) {
      Ok(_,) => {}
      Err(err,) => ErrorPrinter::graceful_exit_early(err,),
    }
  }
  // Otherwise assume it's from a file
  else {
    match builder.add_src_file(args.path.unwrap(),) {
      Ok(_,) => {}
      Err(err,) => ErrorPrinter::graceful_exit_early(err,),
    }
  }

  // TODO:Could use add_writer here for if they want to print errors to a file I
  // guess?

  let mut assembler = builder.build();

  if let Some(header,) = args.header {
    assembler.read_header(header,);
  }

  let program = assembler.compile();

  // The location where the file should be stored
  let output_path = PathBuf::from(format!("src{}/{}.spex", args.output.to_str().unwrap(), args.name),);

  // TODO: Program should be able to take a PathBuf
  // TODO: once program is updated remove the as_str
  match program.save(output_path.to_str().unwrap(),) {
    Ok(_,) => {}
    Err(err,) => {
      // I am not actually sure this error can ever be anything aside from this
      if err.to_string() == "The system cannot find the path specified. (os error 3)" {
        ErrorPrinter::graceful_exit_early(format!(
          "The system cannot find the path specified. {} does not exist. (os error 3)",
          output_path.display()
        ),)
      }
      else {
        ErrorPrinter::graceful_exit_early(err,)
      }
    }
  }

  "cargo run spdr-assember --update-output ./test --name test --path src/test/full_compilation_test.spdr";
}
