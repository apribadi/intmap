//! This crate implements a fast hash map and hash set keyed by `NonZeroU64`s.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

mod prelude;
pub mod map;
pub mod rng;
pub mod set;
