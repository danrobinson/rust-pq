//! The hypertree (FIPS 205 §7).

use alloc::vec::Vec;
use crate::address::Adrs;
use crate::hash::Seed;
use crate::params::{D, HP, N, XMSS_SIG_BYTES};
use crate::xmss::{xmss_node, xmss_pk_from_sig, xmss_sign};

/// Algorithm 12, `ht_sign`.
pub fn ht_sign(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed, idx_tree: u64, idx_leaf: u32) -> Vec<u8> {
    let mut sig: Vec<u8> = Vec::new();
    let mut root = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < D {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let s = xmss_sign(&root, sk_seed, leaf, seed, adrs);
        root = xmss_pk_from_sig(leaf, &s, &root, seed, adrs);
        sig.extend_from_slice(&s);
        leaf = (tree & ((1u64 << HP) - 1)) as u32;
        tree >>= HP;
        j += 1;
    }
    sig
}

/// [`ht_sign`] with every value that a one-time key signs computed twice.
///
/// A fault while one tree is being computed gives a wrong root, which the
/// next layer would then sign correctly: the signature still verifies, and it
/// shows a one-time key signing a second value, which is what a forger needs.
/// Checking the finished signature cannot see that. So each root is computed
/// by two routes that share no work, from the XMSS signature as a verifier
/// would (`a`) and from the secret seed as key generation would (`b`), and
/// compared before the next layer uses it. The top root is known in advance:
/// it is `PK.root`.
///
/// `m_a` and `m_b` are the bottom message, the FORS public key, from two such
/// routes. Each layer signs the `a` value and recomputes the root with the
/// `b` value as the message, so a value damaged between its check and its
/// use is caught one layer up.
///
/// Returns the signature, and whether every pair agreed. When they did, the
/// signature is the one [`ht_sign`] returns for `m_a`.
pub fn ht_sign_checked(
    m_a: &[u8; N],
    m_b: &[u8; N],
    sk_seed: &[u8; N],
    seed: &Seed,
    idx_tree: u64,
    idx_leaf: u32,
    pk_root: &[u8; N],
) -> (Vec<u8>, bool) {
    let mut sig: Vec<u8> = Vec::new();
    let mut msg_a = *m_a;
    let mut msg_b = *m_b;
    let mut ok = true;
    if !(msg_a == msg_b) {
        ok = false;
    }
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < D {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let s = xmss_sign(&msg_a, sk_seed, leaf, seed, adrs);
        let root_a = xmss_pk_from_sig(leaf, &s, &msg_b, seed, adrs);
        let root_b = if j + 1 < D { xmss_node(sk_seed, 0, HP, seed, adrs) } else { *pk_root };
        if !(root_a == root_b) {
            ok = false;
        }
        sig.extend_from_slice(&s);
        msg_a = root_a;
        msg_b = root_b;
        leaf = (tree & ((1u64 << HP) - 1)) as u32;
        tree >>= HP;
        j += 1;
    }
    (sig, ok)
}

/// Algorithm 13, `ht_verify`. `sig` holds `D` XMSS signatures.
pub fn ht_verify(
    m: &[u8; N],
    sig: &[u8],
    seed: &Seed,
    idx_tree: u64,
    idx_leaf: u32,
    pk_root: &[u8; N],
) -> bool {
    let mut node = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < D {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let off = j as usize * XMSS_SIG_BYTES;
        node = xmss_pk_from_sig(leaf, &sig[off..off + XMSS_SIG_BYTES], &node, seed, adrs);
        leaf = (tree & ((1u64 << HP) - 1)) as u32;
        tree >>= HP;
        j += 1;
    }
    node == *pk_root
}
