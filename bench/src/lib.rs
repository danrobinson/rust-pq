//! Uniform wrappers around every SLH-DSA-SHA2-128s implementation under test.
//!
//! Each implementation offers: key generation from the three FIPS 205 seeds
//! (where the API allows), deterministic pure signing with an empty context
//! (where the API allows), and pure verification with an empty context.
//! Keys cross the interface as the standard byte encodings
//! (SK = SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root, PK = PK.seed ‖ PK.root); each
//! wrapper parses them into its library's key object once, outside the timed
//! region, the way a long-lived signer would hold a key.

use std::ffi::c_void;

pub const N: usize = 16;
pub const SK_BYTES: usize = 64;
pub const PK_BYTES: usize = 32;
pub const SIG_BYTES: usize = 7856;

pub type Keygen = Box<dyn Fn(&[u8; N], &[u8; N], &[u8; N]) -> (Vec<u8>, Vec<u8>)>;
pub type Signer = Box<dyn Fn(&[u8]) -> Vec<u8>>;
pub type Verifier = Box<dyn Fn(&[u8], &[u8]) -> bool>;

pub struct Impl {
    /// Short name used in benchmark IDs.
    pub name: &'static str,
    /// FIPS 205 SLH-DSA (true) or round-3 SPHINCS+ (false).
    pub fips205: bool,
    /// Whether keygen honours the supplied seeds.
    pub seeded_keygen: bool,
    /// Whether `make_signer` signs deterministically (opt_rand = PK.seed).
    pub deterministic: bool,
    /// Uses SHA-256 from the `sha2` crate (affected by the soft-backend switch).
    pub uses_sha2_crate: bool,
    /// Rust code compiled by this crate's rustc invocation (affected by LTO/target-cpu).
    pub is_rust: bool,
    pub keygen: Keygen,
    pub make_signer: Box<dyn Fn(&[u8]) -> Signer>,
    pub make_verifier: Box<dyn Fn(&[u8]) -> Verifier>,
}

fn arr<const L: usize>(b: &[u8]) -> [u8; L] {
    b.try_into().expect("length")
}

// ---------------------------------------------------------------- verified crate and variants

macro_rules! slhdsa_like {
    ($name:expr, $krate:ident) => {
        Impl {
            name: $name,
            fips205: true,
            seeded_keygen: true,
            deterministic: true,
            uses_sha2_crate: false,
            is_rust: true,
            keygen: Box::new(|a, b, c| {
                let (sk, pk) = $krate::slh_keygen_internal(a, b, c);
                (sk.to_vec(), pk.to_vec())
            }),
            make_signer: Box::new(|sk| {
                let sk: [u8; SK_BYTES] = arr(sk);
                let addrnd: [u8; N] = arr(&sk[2 * N..3 * N]); // deterministic: opt_rand = PK.seed
                Box::new(move |m| $krate::slh_sign(m, &[], &sk, &addrnd).unwrap())
            }),
            make_verifier: Box::new(|pk| {
                let pk: [u8; PK_BYTES] = arr(pk);
                Box::new(move |m, s| $krate::slh_verify(m, s, &[], &pk))
            }),
        }
    };
}

/// The verified crate, ../rust. With this crate's `hw` feature it is built with its
/// opt-in `hw-sha2` backend and named accordingly.
pub fn verified() -> Impl {
    slhdsa_like!(if cfg!(feature = "hw") { "verified+hw-sha2" } else { "verified" }, slhdsa)
}
/// The interface programs are meant to use (../compat): RustCrypto's types and traits
/// around the verified crate. The same functions as `verified`, reached through the key
/// types, with the stack they used wiped after key generation and signing.
pub fn verified_api() -> Impl {
    use slhdsa_api::signature::{Keypair, Signer as _, Verifier as _};
    use slhdsa_api::{Sha2_128s, Signature, SigningKey, VerifyingKey};
    Impl {
        name: if cfg!(feature = "hw") { "verified-api+hw-sha2" } else { "verified-api" },
        fips205: true,
        seeded_keygen: true,
        deterministic: true,
        uses_sha2_crate: false,
        is_rust: true,
        keygen: Box::new(|a, b, c| {
            let sk = SigningKey::<Sha2_128s>::slh_keygen_internal(a, b, c);
            (sk.to_vec(), sk.verifying_key().to_vec())
        }),
        make_signer: Box::new(|sk| {
            let sk = SigningKey::<Sha2_128s>::try_from(sk).unwrap();
            Box::new(move |m| sk.sign(m).to_vec())
        }),
        make_verifier: Box::new(|pk| {
            let pk = VerifyingKey::<Sha2_128s>::try_from(pk).unwrap();
            Box::new(move |m, s| match Signature::<Sha2_128s>::try_from(s) {
                Ok(sig) => pk.verify(m, &sig).is_ok(),
                Err(_) => false,
            })
        }),
    }
}
/// The pre-optimisation verified crate (copy in variants/base, see Cargo.toml).
pub fn verified_before() -> Impl {
    slhdsa_like!("verified-before", slhdsa_base)
}
pub fn variant_a() -> Impl {
    slhdsa_like!("variant-A", slhdsa_a)
}
pub fn variant_b() -> Impl {
    slhdsa_like!("variant-B", slhdsa_b)
}
pub fn variant_c() -> Impl {
    slhdsa_like!("variant-C", slhdsa_c)
}
/// The current verified crate + ARMv8 SHA-2 intrinsics in `compress` (not verified).
pub fn variant_d() -> Impl {
    slhdsa_like!("variant-D", slhdsa_d)
}

// ---------------------------------------------------------------- RustCrypto slh-dsa

pub fn rustcrypto() -> Impl {
    use slh_dsa::{Sha2_128s, Signature, SigningKey, VerifyingKey};
    Impl {
        name: "rustcrypto-slh-dsa",
        fips205: true,
        seeded_keygen: true,
        deterministic: true,
        uses_sha2_crate: true,
        is_rust: true,
        keygen: Box::new(|a, b, c| {
            let sk = SigningKey::<Sha2_128s>::slh_keygen_internal(a, b, c);
            (sk.to_bytes().to_vec(), sk.as_ref().to_bytes().to_vec())
        }),
        make_signer: Box::new(|sk| {
            let sk = SigningKey::<Sha2_128s>::try_from(sk).unwrap();
            // opt_rand = None selects the deterministic variant (opt_rand = PK.seed).
            Box::new(move |m| sk.try_sign_with_context(m, &[], None).unwrap().to_vec())
        }),
        make_verifier: Box::new(|pk| {
            let vk = VerifyingKey::<Sha2_128s>::try_from(pk).unwrap();
            Box::new(move |m, s| match Signature::<Sha2_128s>::try_from(s) {
                Ok(sig) => vk.try_verify_with_context(m, &[], &sig).is_ok(),
                Err(_) => false,
            })
        }),
    }
}

// ---------------------------------------------------------------- fips205

struct NoRng;
impl rand_core_06::RngCore for NoRng {
    fn next_u32(&mut self) -> u32 {
        panic!("deterministic signing must not draw randomness")
    }
    fn next_u64(&mut self) -> u64 {
        panic!("deterministic signing must not draw randomness")
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        panic!("deterministic signing must not draw randomness")
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), rand_core_06::Error> {
        panic!("deterministic signing must not draw randomness")
    }
}
impl rand_core_06::CryptoRng for NoRng {}

pub fn fips205() -> Impl {
    use fips205::slh_dsa_sha2_128s as p;
    use fips205::traits::{KeyGen, SerDes, Signer as _, Verifier as _};
    Impl {
        name: "fips205",
        fips205: true,
        seeded_keygen: true,
        deterministic: true,
        uses_sha2_crate: true,
        is_rust: true,
        keygen: Box::new(|a, b, c| {
            let (pk, sk) = p::KG::keygen_from_seed(a, b, c);
            (sk.into_bytes().to_vec(), pk.into_bytes().to_vec())
        }),
        make_signer: Box::new(|sk| {
            let sk = p::PrivateKey::try_from_bytes(arr(sk)).unwrap();
            Box::new(move |m| sk.try_sign_with_rng(&mut NoRng, m, &[], false).unwrap().to_vec())
        }),
        make_verifier: Box::new(|pk| {
            let pk = p::PublicKey::try_from_bytes(arr(pk)).unwrap();
            Box::new(move |m, s| match <[u8; SIG_BYTES]>::try_from(s) {
                Ok(sig) => pk.verify(m, &sig, &[]),
                Err(_) => false,
            })
        }),
    }
}

// ---------------------------------------------------------------- OpenSSL (C, via c/ossl_harness.c)

extern "C" {
    fn bench_ossl_init() -> i32;
    fn bench_ossl_keygen_seed(seed48: *const u8) -> *mut c_void;
    fn bench_ossl_free(k: *mut c_void);
    fn bench_ossl_load_priv(sk: *const u8) -> *mut c_void;
    fn bench_ossl_load_pub(pk: *const u8) -> *mut c_void;
    fn bench_ossl_export(k: *mut c_void, sk: *mut u8, pk: *mut u8) -> i32;
    fn bench_ossl_sign(k: *mut c_void, m: *const u8, ml: usize, sig: *mut u8, sl: usize, det: i32) -> usize;
    fn bench_ossl_verify(k: *mut c_void, m: *const u8, ml: usize, sig: *const u8, sl: usize) -> i32;
    pub fn bench_ossl_sha256(m: *const u8, l: usize, out: *mut u8) -> i32;
}

struct OsslKey(*mut c_void);
impl Drop for OsslKey {
    fn drop(&mut self) {
        unsafe { bench_ossl_free(self.0) }
    }
}

pub fn openssl() -> Impl {
    assert!(unsafe { bench_ossl_init() } == 1, "OpenSSL lacks SLH-DSA-SHA2-128s");
    Impl {
        name: "openssl",
        fips205: true,
        seeded_keygen: true,
        deterministic: true,
        uses_sha2_crate: false,
        is_rust: false,
        keygen: Box::new(|a, b, c| {
            let mut seed = [0u8; 3 * N];
            seed[..N].copy_from_slice(a);
            seed[N..2 * N].copy_from_slice(b);
            seed[2 * N..].copy_from_slice(c);
            let k = OsslKey(unsafe { bench_ossl_keygen_seed(seed.as_ptr()) });
            assert!(!k.0.is_null());
            let (mut sk, mut pk) = (vec![0u8; SK_BYTES], vec![0u8; PK_BYTES]);
            assert_eq!(unsafe { bench_ossl_export(k.0, sk.as_mut_ptr(), pk.as_mut_ptr()) }, 1);
            (sk, pk)
        }),
        make_signer: Box::new(|sk| {
            let k = OsslKey(unsafe { bench_ossl_load_priv(sk.as_ptr()) });
            assert!(!k.0.is_null());
            Box::new(move |m| {
                let k = &k; // capture the whole OsslKey (not just the pointer field), so it lives as long as the closure
                let mut sig = vec![0u8; SIG_BYTES];
                let l = unsafe { bench_ossl_sign(k.0, m.as_ptr(), m.len(), sig.as_mut_ptr(), SIG_BYTES, 1) };
                assert_eq!(l, SIG_BYTES);
                sig
            })
        }),
        make_verifier: Box::new(|pk| {
            let k = OsslKey(unsafe { bench_ossl_load_pub(pk.as_ptr()) });
            assert!(!k.0.is_null());
            Box::new(move |m, s| {
                let k = &k;
                (unsafe { bench_ossl_verify(k.0, m.as_ptr(), m.len(), s.as_ptr(), s.len()) }) == 1
            })
        }),
    }
}

// ---------------------------------------------------------------- slhdsa-c (portable C, vendored)

#[repr(C)]
pub struct SlhParam {
    _private: [u8; 0],
}
extern "C" {
    static slh_dsa_sha2_128s: SlhParam;
    fn slh_keygen_internal(sk: *mut u8, pk: *mut u8, a: *const u8, b: *const u8, c: *const u8, p: *const SlhParam) -> i32;
    fn slh_sign(sig: *mut u8, m: *const u8, ml: usize, ctx: *const u8, cl: usize, sk: *const u8, addrnd: *const u8, p: *const SlhParam) -> usize;
    fn slh_verify(m: *const u8, ml: usize, sig: *const u8, sl: usize, ctx: *const u8, cl: usize, pk: *const u8, p: *const SlhParam) -> i32;
}

pub fn slhdsa_c() -> Impl {
    Impl {
        name: "slhdsa-c",
        fips205: true,
        seeded_keygen: true,
        deterministic: true,
        uses_sha2_crate: false,
        is_rust: false,
        keygen: Box::new(|a, b, c| {
            let (mut sk, mut pk) = (vec![0u8; SK_BYTES], vec![0u8; PK_BYTES]);
            unsafe { slh_keygen_internal(sk.as_mut_ptr(), pk.as_mut_ptr(), a.as_ptr(), b.as_ptr(), c.as_ptr(), &slh_dsa_sha2_128s) };
            (sk, pk)
        }),
        make_signer: Box::new(|sk| {
            let sk: [u8; SK_BYTES] = arr(sk);
            Box::new(move |m| {
                let mut sig = vec![0u8; SIG_BYTES];
                let addrnd = &sk[2 * N..3 * N];
                let l = unsafe { slh_sign(sig.as_mut_ptr(), m.as_ptr(), m.len(), [].as_ptr(), 0, sk.as_ptr(), addrnd.as_ptr(), &slh_dsa_sha2_128s) };
                assert_eq!(l, SIG_BYTES);
                sig
            })
        }),
        make_verifier: Box::new(|pk| {
            let pk: [u8; PK_BYTES] = arr(pk);
            Box::new(move |m, s| unsafe { slh_verify(m.as_ptr(), m.len(), s.as_ptr(), s.len(), [].as_ptr(), 0, pk.as_ptr(), &slh_dsa_sha2_128s) } == 1)
        }),
    }
}

// ---------------------------------------------------------------- PQClean round-3 SPHINCS+ (pqcrypto-sphincsplus)

extern "C" {
    // Present in the PQClean "clean" library linked by pqcrypto-sphincsplus, but not wrapped by it.
    fn PQCLEAN_SPHINCSSHA2128SSIMPLE_CLEAN_crypto_sign_seed_keypair(pk: *mut u8, sk: *mut u8, seed: *const u8) -> i32;
}

pub fn pqclean() -> Impl {
    use pqcrypto_sphincsplus::sphincssha2128ssimple as p;
    use pqcrypto_traits::sign::{DetachedSignature as _, PublicKey as _, SecretKey as _};
    Impl {
        name: "pqclean-r3",
        fips205: false,
        seeded_keygen: true,
        deterministic: false,
        uses_sha2_crate: false,
        is_rust: false,
        keygen: Box::new(|a, b, c| {
            let mut seed = [0u8; 3 * N];
            seed[..N].copy_from_slice(a);
            seed[N..2 * N].copy_from_slice(b);
            seed[2 * N..].copy_from_slice(c);
            let (mut sk, mut pk) = (vec![0u8; SK_BYTES], vec![0u8; PK_BYTES]);
            unsafe { PQCLEAN_SPHINCSSHA2128SSIMPLE_CLEAN_crypto_sign_seed_keypair(pk.as_mut_ptr(), sk.as_mut_ptr(), seed.as_ptr()) };
            (sk, pk)
        }),
        make_signer: Box::new(|sk| {
            let sk = p::SecretKey::from_bytes(sk).unwrap();
            // PQClean signs with fresh randomness (randomised SPHINCS+); no deterministic API.
            Box::new(move |m| p::detached_sign(m, &sk).as_bytes().to_vec())
        }),
        make_verifier: Box::new(|pk| {
            let pk = p::PublicKey::from_bytes(pk).unwrap();
            Box::new(move |m, s| match p::DetachedSignature::from_bytes(s) {
                Ok(sig) => p::verify_detached_signature(&sig, m, &pk).is_ok(),
                Err(_) => false,
            })
        }),
    }
}

/// All implementations, in the order used for benchmarking. `BENCH_REVERSE=1`
/// reverses it (the suite is run in both orders to spread drift in background load).
/// `BENCH_ONLY=name1,name2` restricts the set.
pub fn all() -> Vec<Impl> {
    let mut v = vec![
        verified(),
        verified_api(),
        verified_before(),
        rustcrypto(),
        fips205(),
        openssl(),
        slhdsa_c(),
        pqclean(),
        variant_a(),
        variant_b(),
        variant_c(),
        variant_d(),
    ];
    if let Ok(only) = std::env::var("BENCH_ONLY") {
        let names: Vec<&str> = only.split(',').collect();
        v.retain(|i| i.name == "verified" || i.name == "verified-api" || i.name == "verified-before" || names.contains(&i.name));
    }
    if std::env::var("BENCH_REVERSE").map(|s| s == "1").unwrap_or(false) {
        v.reverse();
    }
    v
}

/// The fixed seeds and messages used everywhere.
pub const SK_SEED: [u8; N] = [0x11; N];
pub const SK_PRF: [u8; N] = [0x22; N];
pub const PK_SEED: [u8; N] = [0x33; N];

pub fn message(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i as u32).wrapping_mul(2654435761).to_be_bytes()[0]).collect()
}
