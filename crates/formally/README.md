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
SMT-LIBv2 scripts, solving them with a [Z3](https://github.com/Z3Prover/z3) backend.

## How to build the crate

The Z3 backend is based on the [z3_sys](https://crates.io/crates/z3-sys) crate which does not
discover Z3's library automatically, so we currently need to set include paths and linker
arguments manually.

This is done by setting the `Z3_SYS_Z3_HEADER` environment variable with the path to
`z3.h` and passing the correct `-L` flag to the compiler to find the shared library.

This can be done conveniently and once and for all by adding the following lines to Cargo's
`config.toml` (see the *Configuration* section in the
[Cargo Book](https://doc.rust-lang.org/cargo/reference/config.html)):

For example, supposing Z3 has been installed with Homebrew on a macOS system:
```cargo
[env]
Z3_SYS_Z3_HEADER="/opt/homebrew/Cellar/z3/4.15.3/include/z3.h"

[build]
rustflags=["-C", "link-arg=-L/opt/homebrew/Cellar/z3/4.15.3/lib/"]
rustdocflags=["-C", "link-arg=-L/opt/homebrew/Cellar/z3/4.15.3/lib/"]
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
