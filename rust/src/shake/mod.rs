//! FIPS 205 §11.1 SHAKE instantiation. The hypertree, XMSS, and public
//! algorithms have the same sources as the SHA-2 family.

// The shared SLH and XMSS sources use these blocks for SHA-2-specific kernels.
macro_rules! sha2_only {
    ($($item:tt)*) => {  };
}

#[cfg(all(feature = "platform-sha2", any(all(target_arch = "aarch64", target_endian = "little"), all(target_arch = "x86_64", target_feature = "sse2"))))]
mod batch;
#[cfg(all(feature = "platform-sha2", any(all(target_arch = "aarch64", target_endian = "little"), all(target_arch = "x86_64", target_feature = "sse2"))))]
mod fors_batch;
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
