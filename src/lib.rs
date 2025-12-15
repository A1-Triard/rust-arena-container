#![cfg_attr(feature="nightly", feature(allocator_api))]
#![cfg_attr(feature="nightly", feature(associated_type_defaults))]

#![deny(warnings)]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(allow(dead_code))))]
#![doc(test(attr(allow(unused_variables))))]
#![allow(unknown_lints)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::non_canonical_clone_impl)]
#![allow(clippy::non_canonical_partial_ord_impl)]
#![allow(clippy::type_complexity)]

//! ## Feature flags
#![doc=document_features::document_features!()]

#![no_std]

//#[doc=include_str!("../README.md")]
//type _DocTestReadme = ();

mod index;

mod nightly;

pub use nightly::*;
