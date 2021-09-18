#![deny(missing_docs)]
#![no_std]

//! A set of macros similar to the standard library's `assert_*` macros, but return early instead of panicking.
//! # Example
//! ```
//! use soft_assert::*;
//!
//! fn not_twenty(x: i32) -> Option<i32> {
//!     // This will return `Option::default()`, which is `None`
//!     soft_assert_ne!(x, 20);
//!     Some(x)
//! }
//!
//! fn double_if_greater_than_5(x: i32) -> i32 {
//!     // But here we don't want to return `i32::default()`,
//!     // so we specify a return value.
//!     soft_assert!(x > 5, x);
//!     x * 2
//! }
//!
//! fn main() {
//!     assert!(not_twenty(10).is_some());   
//!     assert!(not_twenty(20).is_none());   
//!
//!     let doubled = double_if_greater_than_5(13);
//!     assert_eq!(doubled, 26);    
//!     let not_doubled = double_if_greater_than_5(2);
//!     assert_eq!(not_doubled, 2);   
//! }
//!
//! ```
//!
//! This crate is `#![no_std]`

#[macro_export]
/// Asserts a condition is true, returning otherwise.
///
/// Non-panicking version of [`assert`](https://doc.rust-lang.org/std/macro.assert.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_assert!(false, Err(e))`. Ownership of any captured values is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
macro_rules! soft_assert {
    ($e:expr) => {
        if !$e {
            return Default::default();
        }
    };
    ($e:expr,) => {
        $crate::soft_assert!($e)
    };
    ($e:expr, $failed:expr) => {
        if !$e {
            return $failed;
        }
    };
    ($e:expr, $failed:expr,) => {
        $crate::soft_assert!($e)
    };
}

/// Asserts two values are equal, returning otherwise.
///
/// Non-panicking version of [`assert_eq`](https://doc.rust-lang.org/std/macro.assert_eq.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_assert_eq!(1, 2, Err(e))`. Ownership of any captured values is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
#[macro_export]
macro_rules! soft_assert_eq {
    ($x:expr, $y:expr) => {
        if { $x } != { $y } {
            return;
        }
    };
    ($x:expr, $y:expr,) => {
        $crate::soft_assert_eq!($x, $y)
    };
    ($x:expr, $y:expr, $failed:expr) => {
        if { $x } != { $y } {
            return $failed;
        }
    };
    ($x:expr, $y:expr, $failed:expr,) => {
        $crate::soft_assert_eq!($x, $y, $failed)
    };
}

/// Asserts two values are not equal, returning otherwise.
///
/// Non-panicking version of [`assert_ne`](https://doc.rust-lang.org/std/macro.assert_ne.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_assert_ne!(2 + 2, 4, Err(e))`. Ownership of any captured values is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
#[macro_export]
macro_rules! soft_assert_ne {
    ($x:expr, $y:expr) => {
        if { $x } == { $y } {
            return;
        }
    };
    ($x:expr, $y:expr,) => {
        $crate::soft_assert_ne!($x, $y)
    };
    ($x:expr, $y:expr, $failed:expr) => {
        if { $x } == { $y } {
            return $failed;
        }
    };
    ($x:expr, $y:expr, $failed:expr,) => {
        $crate::soft_assert_ne!($x, $y, $failed)
    };
}

#[macro_export]
/// Asserts a value matches a pattern, returning otherwise.
///
/// Non-panicking version of [`assert_matches`](https://doc.rust-lang.org/std/assert_matches/macro.assert_matches.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_assert_matches!(x, None, Err(e))`. Ownership of any captured values is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
macro_rules! soft_assert_matches {
    ($e:expr, $p:pat) => {
        match $e {
            $p => (),
            _ => return;
        }
    };
    ($e:expr, $p:pat,) => {
        $crate::soft_assert_matches!($x, $y)
    };
    ($e:expr, $p:pat, $failed:expr) => {
        match $e {
            $p => (),
            _ => return $failed;
        }
    };
    ($e:expr, $p:pat, $failed:expr,) => {
        $crate::soft_assert_matches!($x, $y, $failed)
    };
}

/// If debug assertions are enabled, asserts a condition is true, returning otherwise.
///
/// Non-panicking version of [`debug_assert`](https://doc.rust-lang.org/std/macro.debug_assert.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_debug_assert!(false, Err(e))`. Ownership of the value is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
#[macro_export]
macro_rules! soft_debug_assert {
    ($e:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert!($e);
    };
    ($e:expr,) => {
        $crate::soft_debug_assert!($e);
    };
    ($e:expr, $failed:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert!($e, $failed);
    };
    ($e:expr, $failed:expr,) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert!($e, $failed);
    };
}

/// If debug assertions are enabled, asserts two values are equal, returning otherwise.
///
/// Non-panicking version of [`debug_assert_eq`](https://doc.rust-lang.org/std/macro.debug_assert_eq.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_debug_assert_eq!(1, 2, Err(e))`. Ownership of the value is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
#[macro_export]
macro_rules! soft_debug_assert_eq {
    ($x:expr, $y:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_eq!($x, $y);
    };
    ($x:expr, $y:expr,) => {
        $crate::soft_debug_assert_eq!($x, $y);
    };
    ($x:expr, $y:expr, $failed:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_eq!($x, $y, $failed);
    };
    ($x:expr, $y:expr, $failed:expr,) => {
        $crate::soft_debug_assert_eq!($x, $y, $failed);
    };
}

/// If debug assertions are enabled, asserts two values are not equal, returning otherwise.
///
/// Non-panicking version of [`debug_assert_ne`](https://doc.rust-lang.org/std/macro.debug_assert.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_debug_assert_ne!(2 + 2, 4, Err(e))`. Ownership of the value is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
#[macro_export]
macro_rules! soft_debug_assert_ne {
    ($x:expr, $y:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_ne!($x, $y);
    };
    ($x:expr, $y:expr,) => {
        $crate::soft_debug_assert_ne!($x, $y);
    };
    ($x:expr, $y:expr, $failed:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_ne!($x, $y, $failed);
    };
    ($x:expr, $y:expr, $failed:expr,) => {
        $crate::soft_debug_assert_ne!($x, $y, $failed);
    };
}

#[macro_export]
/// Asserts a value matches a pattern, returning otherwise.
///
/// Non-panicking version of [`debug_assert_matches`](https://doc.rust-lang.org/std/assert_matches/macro.debug_assert_matches.html).
///
/// # Custom return values
/// Unless otherwise specified, this will return the default value of the return type (if it has one).
/// A custom value can be returned instead by supplying it as an additional argument (similar to `assert`'s custom message),
/// i.e. `soft_debug_assert_match!(x, None, Err(e))`. Ownership of any captured values is only taken if the assertion fails, so you can
/// continue to use them later on.
///
/// This does *not* perform `Err(..)`-wrapping, to allow returning any value.
macro_rules! soft_debug_assert_matches {
    ($e:expr, $p:pat) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_match!($e, $p);
    };
    ($e:expr, $p:pat,) => {
        $crate::soft_debug_assert_match!($e, $p);
    };
    ($e:expr, $p:pat, $failed:expr) => {
        #[cfg(debug_assertions)]
        $crate::soft_assert_match!($e, $p, $failed);
    };
    ($e:expr, $p:pat, $failed:expr,) => {
        $crate::soft_debug_assert_match!($e, $p, $failed);
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert!((|| {
            soft_assert!(true, false);
            true
        })());
        assert!((|| {
            soft_assert!(false, true);
            false
        })());
        assert!((|| {
            soft_assert_eq!((1..=10).sum::<i32>(), 55, false);
            true
        })());
        assert!((|| {
            soft_assert_eq!((1..=10).sum::<i32>(), 3141, true);
            false
        })());
        assert!((|| {
            soft_assert_ne!((1..=10).sum::<i32>(), 3151, false);
            true
        })());
        assert!((|| {
            soft_assert_ne!((1..=10).sum::<i32>(), 55, true);
            false
        })());
    }
}
