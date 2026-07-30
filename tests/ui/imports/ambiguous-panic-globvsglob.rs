//@ edition: 2024
//@ check-pass
#![crate_type = "lib"]
mod m1 {
    pub use core::prelude::v1::*;
}

mod m2 {
    pub use std::prelude::v1::*;
}

fn foo() {
    use m1::*;
    use m2::*;

    // Both globs resolve to the same edition-specific macro, so this is not ambiguous.
    panic!();
}
