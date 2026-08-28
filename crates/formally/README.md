# ::formally
## The open-source formal methods toolchain

`::formally` is a project that aims to build a comprehensive open-source framework and
toolchain to help the development of formal methods applications.

## What the project currently provides
The project is still in its very early stages and is in active development. These early releases
is meant to be a preview of where the project is going and the start of an open development
process for the project.

What the project *does* currently provide consists in the following:
1. `formally::support` provides common facilities useful for the rest of the project.
   Crucially, it provides a mechanism of error reporting based on the concept of *diagnostic*,
   similar to what seen in many modern compilers, and facilities to produce precise and
   informative error messages throughout the project.
2. `formally::io` provides utilities to parse input and produce output. The main part of the
   module is a *parser combinators* library that allows easy and quick writing of parsers that
   automatically produce precise and high-quality error messages, integrated with the project's
   error reporting infrastructure.
3. `formally::smt` provides an abstraction over Satisfiability Modulo Theories solvers and
   (what will hopefully become) a fully conformant implementation of the SMT-LIBv2 language.
4. A simple toy command-line frontend to test the `formally::smt` module.

The `formally::smt` module is quite under heavy development but can already handle simple
SMT-LIBv2 scripts, solving them with a [Z3](https://github.com/Z3Prover/z3) or
[cvc5](https://cvc5.github.io) backend.

## How to build the crate

The Z3 and cvc5 backends are based on the [z3-sys](https://crates.io/crates/z3-sys) and
[cvc5-sys](https://crates.io/crates/cvc5-sys) crates, respectively, which do not
discover the backend libraries automatically, so we currently need to set include paths and
linker arguments manually.

This is done as follows:
1. for Z3 (for the `smt-z3` feature):
   1. setting the `Z3_SYS_Z3_HEADER` environment variable with the path to `z3.h`, and
   2. passing the correct `-L` flag to the compiler to find the shared library.
2. for cvc5 (for the `smt-cvc5` feature):
   1. setting the `CVC5_LIB_DIR` and `CVC5_INCLUDE_DIR` environment variables with the path to
      the library's directory and the include directory, respectively.
   2. on macOS, setting the `rpath` of the final executable by specifying the
      `-Wl,-rpath,$CVC5_LIB_DIR` option

This can be done conveniently and once and for all by editing Cargo's `config.toml` (see the
*Configuration* section in the
[Cargo Book](https://doc.rust-lang.org/cargo/reference/config.html)):

For example, suppose you are on a macOS system, Z3 has been installed with Homebrew and
the binary distribution of cvc5 has been downloaded from GitHub to `/Users/john/cvc5`.

Then, write this into `~/.cargo/config.toml`:
```cargo
[env]
Z3_SYS_Z3_HEADER="/opt/homebrew/Cellar/z3/4.15.4/include/z3.h"
CVC5_LIB_DIR="/Users/john/cvc5"
CVC5_INCLUDE_DIR="/Users/john/cvc5"

[build]
rustflags=[
    "-C", "link-arg=-L/opt/homebrew/Cellar/z3/5.1.0/lib",
    "-C", "link-arg=-Wl,-rpath,/Users/john/cvc5"
]
```
Version numbers have to be changed accordingly, of course.

Then, one can add the crate to their own project's dependencies as usual:
```text
$ cargo add formally
```


# How to run the command-line frontend

The front-end can be installed through the `formally-cli` package.
```text
$ cargo install formally-cli
```
Then, the `formally` command accepts a `solve` subcommand with the name of an SMT-LIBv2 file to
run.

```text
$ cat test.smtlib
(set-logic ALIA)
(declare-const array (Array Int Int))

(assert (not (= (select (store array 0 42) 0) 42)))

(check-sat)

$ formally solve test.smtlib
unsat
```
