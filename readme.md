Assembler for the [`spdr-vm`](https://github.com/Barca545/spdr-vm.git). Built on top of the [`spdr-isa`](https://github.com/Barca545/spdr-isa.git).

# Using the Assembler

Users can interact with the Assembler via the CLI. The Assembler accepts `.spdr` files via the `--path` command and assembly entered into the CLI as a string via the `--str` command.

```
USAGE:
  spdr-assembler [OPTIONS] --path PATH [INPUT]

FLAGS:
  -h, --help                   Prints help information.
  -v, --version                Prints assembler version information.
  -d, --defaults               Display any assember defaults.
  -p, --print                  Prints the output assembly when completed.


OPTIONS:
  --name STRING                Declares the name of the file.
  --input PATH                 Specify the file to assemble. 
  --str STRING                 Provide a string of assembly.
  --header PATH                Specify a header file.   
  --output PATH                Specify an output path.
  --update-output PATH         Updates the default output path.
  ```