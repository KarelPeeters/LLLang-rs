// not very useful
#![allow(clippy::len_without_is_empty)]
// new and default don't really have the same meaning
#![allow(clippy::new_without_default)]
// false positives when function is cheap (eg .len())
#![allow(clippy::or_fun_call)]
// annoying to fix
#![allow(clippy::result_large_err)]
// sometimes indices are clearer
#![allow(clippy::needless_range_loop)]
// not very informative or actionable
#![allow(clippy::too_many_arguments)]

// usually means an important bug
#![deny(unused_must_use)]

#[macro_use]
mod util;
pub mod front;
pub mod back;
pub mod mid;
pub mod tools;