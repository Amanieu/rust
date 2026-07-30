//@ edition:2018

#![crate_type = "lib"]

#[macro_export]
macro_rules! assert_with_owned_message {
    () => {
        assert!(true, ::std::string::String::new());
    };
}
