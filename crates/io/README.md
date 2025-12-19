# ::formally
## The open-source formal methods toolchain

``::formally`` is an early-stage work-in-progress project to provide an extensive and extensible toolchain for building
formal methods tools and applications.

This package contains the `formally::io` subcrate. This is not meant to be used directly. Instead, use the main
[formally] crate and enable its `"io"` feature.

```
formally = { version = "0.2025.12", features = ["io"] }
```

We refer to the documentation of the main [formally] package for details.

[formally]: https://crates.io/crates/formally