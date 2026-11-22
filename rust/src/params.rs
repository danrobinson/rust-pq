//! Parameter set SLH-DSA-SHA2-128s (FIPS 205, Table 2).

/// Security parameter: hash output length in bytes.
pub const N: usize = 16;
/// Height of each XMSS tree (h').
pub const HP: u32 = 9;
/// Number of hypertree layers.
pub const D: u32 = 7;
/// FORS tree height.
pub const A: u32 = 12;
/// Number of FORS trees.
pub const K: u32 = 14;
/// Winternitz parameter, log2.
pub const LG_W: u32 = 4;
/// Winternitz parameter w = 2^LG_W.
pub const W: u32 = 16;
/// Message digest length in bytes.
pub const M: usize = 30;
/// WOTS+ message chains.
pub const LEN1: usize = 32;
/// WOTS+ checksum chains.
pub const LEN2: usize = 3;
/// WOTS+ chains in total.
pub const LEN: usize = 35;

/// Bytes of the digest used for FORS: ceil(K*A/8).
pub const MD_BYTES: usize = 21;
/// Bytes of the digest used for the tree index: ceil((H - H/D)/8).
pub const TREE_BYTES: usize = 7;
/// Bytes of the digest used for the leaf index: ceil(H/(8D)).
pub const LEAF_BYTES: usize = 2;

pub const WOTS_SIG_BYTES: usize = 560; // LEN * N
pub const XMSS_SIG_BYTES: usize = 704; // (LEN + HP) * N
pub const FORS_SIG_BYTES: usize = 2912; // K * (1 + A) * N
pub const HT_SIG_BYTES: usize = 4928; // D * XMSS_SIG_BYTES
pub const SIG_BYTES: usize = 7856; // N + FORS_SIG_BYTES + HT_SIG_BYTES
pub const PK_BYTES: usize = 32;
pub const SK_BYTES: usize = 64;
/// The random bytes key generation consumes: `SK.seed ‖ SK.prf ‖ PK.seed`.
pub const SEED_BYTES: usize = 48; // 3 * N
/// Length of the PKCS#8 encoding of a private key, and of the
/// SubjectPublicKeyInfo encoding of a public key.
pub const PKCS8_BYTES: usize = 84; // 20 + SK_BYTES
pub const SPKI_BYTES: usize = 50; // 18 + PK_BYTES
