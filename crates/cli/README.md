# ::formally
## The open-source formal methods toolchain

``::formally`` is an early-stage work-in-progress project to provide an extensive and extensible toolchain for building
formal methods tools and applications.

This package implements a simple command-line front-end that currently tests the SMT functionalities of [formally].  
Please take a look at the documentation of the main package for more information on the project.

The front-end can be installed through the `formally-cli` package.
```
$ cargo install formally-cli
```

Then, the `formally` command accepts a `solve` subcommand with the name of an SMT-LIBv2 file to run.
```
$ cat test.smtlib
(set-logic ALIA)
(declare-const array (Array Int Int))

(assert (not (= (select (store array 0 42) 0) 42)))

(check-sat)

$ formally solve test.smtlib
unsat
```

We again refer to the main [formally] package for more information.

[formally]: https://crates.io/crates/formally