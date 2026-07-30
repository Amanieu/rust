//@ aux-build:assert-cross-edition.rs
//@ check-pass
//@ edition:2024

extern crate assert_cross_edition;

fn main() {
    // The `assert!` invocation was written in Edition 2018, so its non-format argument must use
    // the pre-2021 `std::panic!` behavior even though this crate uses Edition 2024.
    assert_cross_edition::assert_with_owned_message!();
}
