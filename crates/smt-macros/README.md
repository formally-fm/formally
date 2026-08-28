# ::formally
## The open-source formal methods toolchain

``::formally`` is an early-stage work-in-progress project to provide an extensive and extensible toolchain for building
formal methods tools and applications.

This package contains the procedural macros exported by the `formally::smt` subcrate. This is not meant to be used 
directly. Instead, use the main [formally] crate and enable its `"smt"` feature.

```
formally = { version = "0.2.0", features = ["smt"] }
```

We refer to the documentation of the main [formally] package for details.

[formally]: https://crates.io/crates/formally