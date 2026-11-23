//! FIPS 205 §11.1 SHAKE instantiation. The hypertree, XMSS, and public
//! algorithms have the same sources as the SHA-2 family.

pub mod hash;
mod wots;
mod fors;
#[path = "../xmss.rs"]
mod xmss;
#[path = "../ht.rs"]
mod ht;
#[path = "../slh.rs"]
pub mod slh;
#[path = "../api.rs"]
pub mod api;
#[path = "../adapter.rs"]
pub mod adapter;
