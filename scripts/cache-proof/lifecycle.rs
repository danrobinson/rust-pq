// Compiled with the verbatim production TopTreeCache lifecycle methods by check-cache-endtoend.py.
// Verifies key association, precomputation, lookup, MRU move-to-front, insertion, eviction,
// capacity truncation, reuse (zero rebuilds on hit), and end-to-end cached signing dispatch
// across all 12 FIPS 205 parameter sets (SHA-2 and SHAKE).

use std::sync::atomic::{AtomicUsize, Ordering};

static BUILD_CALLS: AtomicUsize = AtomicUsize::new(0);
static LAST_D2_HIT: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub n: usize,
    pub h: u32,
    pub d: u32,
    pub hp: u32,
    pub a: u32,
    pub k: u32,
    pub m: usize,
}

impl Params {
    pub const fn md_bytes(&self) -> usize {
        ((self.k * self.a) as usize + 7) / 8
    }
    pub const fn tree_bits(&self) -> u32 {
        self.h - self.hp
    }
    pub const fn tree_bytes(&self) -> usize {
        (self.tree_bits() as usize + 7) / 8
    }
    pub const fn leaf_bytes(&self) -> usize {
        (self.hp as usize + 7) / 8
    }
}

fn block<const N: usize>(buf: &[u8], idx: usize) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&buf[idx * N..(idx + 1) * N]);
    out
}

fn to_int(bytes: &[u8]) -> u64 {
    let mut acc = 0u64;
    for &b in bytes {
        acc = (acc << 8) | b as u64;
    }
    acc
}

fn tag_node<const N: usize>(
    family: u8,
    hp: u32,
    layer: u32,
    tree_index: u64,
    sk_seed: &[u8; N],
    pk_seed: &[u8; N],
    pos: usize,
) -> [u8; N] {
    let mut out = [0u8; N];
    let mut h: u64 = 0x51a3_cafe_0000_0001u64
        ^ ((family as u64) << 56)
        ^ ((hp as u64) << 48)
        ^ ((layer as u64) << 32)
        ^ tree_index.rotate_left(13)
        ^ (pos as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    for (i, (&s, &p)) in sk_seed.iter().zip(pk_seed.iter()).enumerate() {
        h ^= ((s as u64) << ((i % 8) * 8)) ^ ((p as u64).rotate_left(7) << (((i + 3) % 8) * 8));
        h = h.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        h ^= h >> 30;
    }
    for (i, b) in out.iter_mut().enumerate() {
        h = h.wrapping_add(0x9e37_79b9_7f4a_7c15 ^ (i as u64));
        let mut z = h;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        *b = (z ^ (z >> 31)) as u8;
    }
    out
}

fn symbolic_tree<const N: usize>(
    family: u8,
    hp: u32,
    layer: u32,
    tree_index: u64,
    sk_seed: &[u8; N],
    pk_seed: &[u8; N],
) -> Vec<[u8; N]> {
    let total = tree_node_count(hp);
    (0..total)
        .map(|pos| tag_node(family, hp, layer, tree_index, sk_seed, pk_seed, pos))
        .collect()
}

fn symbolic_digest<const N: usize>(
    family: u8,
    p: &Params,
    sk_prf: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
    addrnd: &[u8; N],
    ctx: &[u8],
    m: &[u8],
) -> ([u8; N], Vec<u8>) {
    // Encode the target layer d-2 tree index directly into the digest when m starts with
    // marker 0xD2 followed by u64 little-endian target_d2 so tests can drive arbitrary hit/miss/eviction patterns.
    let mut r = [0u8; N];
    for i in 0..N {
        r[i] = sk_prf[i] ^ addrnd[i] ^ pk_seed[i] ^ pk_root[i] ^ family;
    }
    let mut digest = vec![0u8; p.m];
    if m.len() >= 9 && m[0] == 0xD2 {
        let target_d2 = u64::from_le_bytes(m[1..9].try_into().unwrap());
        let mask = (1u64 << p.hp) - 1;
        let idx_tree = (target_d2 & mask) << ((p.d - 2) * p.hp);
        let lo = p.md_bytes();
        let tb = p.tree_bytes();
        for b in 0..tb {
            let shift = (tb - 1 - b) * 8;
            digest[lo + b] = if shift < 64 { (idx_tree >> shift) as u8 } else { 0 };
        }
        digest[0] = ctx.len() as u8;
    } else {
        for (i, slot) in digest.iter_mut().enumerate() {
            *slot = (i as u8)
                .wrapping_add(family)
                .wrapping_add(ctx.len() as u8)
                .wrapping_add(m.len() as u8);
        }
    }
    (r, digest)
}

fn check_sign_dispatch<const N: usize>(
    family: u8,
    p: &Params,
    sk_seed: &[u8; N],
    pk_seed: &[u8; N],
    r: &[u8; N],
    digest: &[u8],
    top_tree: &[[u8; N]],
    layer_d2_hit: Option<&[[u8; N]]>,
) -> Vec<u8> {
    // 1. Top tree must match exact symbolic (layer = d - 1, tree = 0) tree for this key & family.
    let expected_top = symbolic_tree(family, p.hp, p.d - 1, 0, sk_seed, pk_seed);
    assert_eq!(top_tree, expected_top.as_slice(), "top_tree mismatch in sign_from_digest");

    // 2. If layer_d2_hit is Some(d2), it must match the exact symbolic tree for (layer = d - 2, tree = tree_d2).
    if let Some(d2) = layer_d2_hit {
        let expected_tree_d2 = if p.d < 2 {
            0
        } else {
            digest_tree(p, digest) >> ((p.d - 2) * p.hp)
        };
        let expected_d2 = symbolic_tree(family, p.hp, p.d - 2, expected_tree_d2, sk_seed, pk_seed);
        assert_eq!(d2, expected_d2.as_slice(), "layer_d2_hit mismatch in sign_from_digest");
        LAST_D2_HIT.store(1, Ordering::Relaxed);
    } else {
        LAST_D2_HIT.store(0, Ordering::Relaxed);
    }

    // 3. Return canonical signature tag independent of whether layer_d2 hit or missed!
    let mut sig = Vec::with_capacity(1 + N + digest.len());
    sig.push(family);
    sig.extend_from_slice(r);
    sig.extend_from_slice(digest);
    sig
}

mod sha2_ops {
    use super::*;

    pub(super) fn build_xmss_tree<const N: usize>(
        hp: u32,
        layer: u32,
        tree_index: u64,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Vec<[u8; N]> {
        BUILD_CALLS.fetch_add(1, Ordering::Relaxed);
        symbolic_tree(0, hp, layer, tree_index, sk_seed, pk_seed)
    }

    pub(super) fn internal_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        symbolic_digest(0, p, sk_prf, pk_seed, pk_root, addrnd, &[], m)
    }

    pub(super) fn pure_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        ctx: &[u8],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        symbolic_digest(0, p, sk_prf, pk_seed, pk_root, addrnd, ctx, m)
    }

    pub(super) fn sign_from_digest<const N: usize>(
        p: &Params,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        r: &[u8; N],
        digest: &[u8],
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Vec<u8> {
        check_sign_dispatch(0, p, sk_seed, pk_seed, r, digest, top_tree, layer_d2_hit)
    }
}

mod shake_ops {
    use super::*;

    pub(super) fn build_xmss_tree<const N: usize>(
        hp: u32,
        layer: u32,
        tree_index: u64,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Vec<[u8; N]> {
        BUILD_CALLS.fetch_add(1, Ordering::Relaxed);
        symbolic_tree(1, hp, layer, tree_index, sk_seed, pk_seed)
    }

    pub(super) fn internal_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        symbolic_digest(1, p, sk_prf, pk_seed, pk_root, addrnd, &[], m)
    }

    pub(super) fn pure_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        ctx: &[u8],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        symbolic_digest(1, p, sk_prf, pk_seed, pk_root, addrnd, ctx, m)
    }

    pub(super) fn sign_from_digest<const N: usize>(
        p: &Params,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        r: &[u8; N],
        digest: &[u8],
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Vec<u8> {
        check_sign_dispatch(1, p, sk_seed, pk_seed, r, digest, top_tree, layer_d2_hit)
    }
}

// PRODUCTION_CACHE_ITEMS

fn msg_for_d2(target_d2: u64) -> [u8; 9] {
    let mut m = [0u8; 9];
    m[0] = 0xD2;
    m[1..9].copy_from_slice(&target_d2.to_le_bytes());
    m
}

fn check_param_set<const N: usize>(family: HashFamily, p: Params, precompute: bool) {
    let seeds: Vec<u8> = (0..3 * N).map(|i| (i as u8).wrapping_mul(37).wrapping_add(11)).collect();
    let mut sk = vec![0u8; 4 * N];
    let mut pk = vec![0u8; 2 * N];
    let addrnd = [0x5Au8; N];

    // 1. keygen_with_cache builds exactly 1 tree (top tree) and matches TopTreeCache::new
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let cache = keygen_with_cache::<N>(family, &p, &seeds, &mut sk, &mut pk);
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 1);
    assert!(cache.matches_key(&sk));
    assert_eq!(cache.pk_seed(), &pk[..N]);
    assert_eq!(cache.pk_root(), &pk[N..]);

    let cache2 = TopTreeCache::<N>::new(family, &p, &sk);
    assert_eq!(cache, cache2);

    // 2. Key-mismatch rejection: wrong len, flipped pk_seed, flipped pk_root
    assert!(!cache.matches_key(&sk[..4 * N - 1]));
    let mut bad_seed = sk.clone();
    bad_seed[2 * N] ^= 1;
    assert!(!cache.matches_key(&bad_seed));
    let mut bad_root = sk.clone();
    bad_root[3 * N] ^= 1;
    assert!(!cache.matches_key(&bad_root));

    // 3. Immutable signing reuses top tree with ZERO tree builds
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let m0 = msg_for_d2(0);
    let sig_base = cache.sign(&p, &m0, b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 0);

    // Context > 255 rejected without panicking
    let bad_ctx = vec![0u8; 256];
    assert!(cache.sign(&p, &m0, &bad_ctx, &sk, &addrnd).is_none());

    // 4. Dynamic MRU insertion, reuse, move-to-front, eviction, and capacity truncation
    let mut mru = cache.clone().with_layer_d2_capacity(2);
    assert_eq!(mru.layer_d2_cached_trees(), 0);

    // Miss on tree 1 -> builds 1 tree, inserted at front [1]
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let sig1 = mru.sign_mut(&p, &msg_for_d2(1), b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 1);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 1);
    assert_eq!(mru.layer_d2_cached_trees(), 1);
    assert_eq!(mru.layer_d2[0].tree_index, 1);

    // Hit at head on tree 1 -> ZERO rebuilds!
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let sig1_again = mru.sign_mut(&p, &msg_for_d2(1), b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 1);
    assert_eq!(sig1_again, sig1);
    assert_eq!(mru.layer_d2[0].tree_index, 1);

    // Miss on tree 2 -> builds 1 tree, inserted at front [2, 1]
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let _ = mru.sign_mut(&p, &msg_for_d2(2), b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 1);
    assert_eq!(mru.layer_d2_cached_trees(), 2);
    assert_eq!(mru.layer_d2[0].tree_index, 2);
    assert_eq!(mru.layer_d2[1].tree_index, 1);

    // Hit at non-head on tree 1 -> ZERO rebuilds, MRU moves 1 to front [1, 2]!
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let _ = mru.sign_mut(&p, &msg_for_d2(1), b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 1);
    assert_eq!(mru.layer_d2[0].tree_index, 1);
    assert_eq!(mru.layer_d2[1].tree_index, 2);

    // Miss on tree 3 at capacity 2 -> evicts LRU tail (2), inserts 3 at front [3, 1]!
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let _ = mru.sign_mut(&p, &msg_for_d2(3), b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 1);
    assert_eq!(mru.layer_d2_cached_trees(), 2);
    assert_eq!(mru.layer_d2[0].tree_index, 3);
    assert_eq!(mru.layer_d2[1].tree_index, 1);

    // Hit on tree 0 (equals sig_base!) -> evicts 1, inserts 0 at front [0, 3]!
    let sig0_mru = mru.sign_mut(&p, &m0, b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(sig0_mru, sig_base);
    assert_eq!(mru.layer_d2[0].tree_index, 0);
    assert_eq!(mru.layer_d2[1].tree_index, 3);

    // Truncation via set_layer_d2_capacity(1) drops tail (3), keeps [0]
    mru.set_layer_d2_capacity(1);
    assert_eq!(mru.layer_d2_cached_trees(), 1);
    assert_eq!(mru.layer_d2[0].tree_index, 0);

    // sign_internal_mut on cached tree 0 -> ZERO rebuilds!
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let _ = mru.sign_internal_mut(&p, &m0, &sk, &addrnd);
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 1);

    // Truncation to 0 clears cache; subsequent sign_mut does NOT cache
    mru.set_layer_d2_capacity(0);
    assert_eq!(mru.layer_d2_cached_trees(), 0);
    BUILD_CALLS.store(0, Ordering::Relaxed);
    let sig0_nocache = mru.sign_mut(&p, &m0, b"ctx", &sk, &addrnd).unwrap();
    assert_eq!(sig0_nocache, sig_base);
    assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
    assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 0);

    // 5. Upfront precompute_layer_d2 (for -f sets where 2^hp <= 16)
    if precompute {
        let mut pre = cache.clone();
        BUILD_CALLS.store(0, Ordering::Relaxed);
        pre.precompute_layer_d2(&p, &sk);
        let count = 1usize << p.hp;
        assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), count);
        assert_eq!(pre.layer_d2_cached_trees(), count);
        for t in 0..count as u64 {
            BUILD_CALLS.store(0, Ordering::Relaxed);
            let s_imm = pre.sign(&p, &msg_for_d2(t), b"pre", &sk, &addrnd).unwrap();
            assert_eq!(BUILD_CALLS.load(Ordering::Relaxed), 0);
            assert_eq!(LAST_D2_HIT.load(Ordering::Relaxed), 1);
            let s_ref = cache.sign(&p, &msg_for_d2(t), b"pre", &sk, &addrnd).unwrap();
            assert_eq!(s_imm, s_ref);
        }
    }
}

fn main() {
    for family in [HashFamily::Sha2, HashFamily::Shake] {
        // All 12 FIPS 205 Table 2 parameter sets (6 SHA-2 + 6 SHAKE)
        check_param_set::<16>(family, Params { n: 16, h: 63, d: 7,  hp: 9, a: 12, k: 14, m: 30 }, false); // 128s
        check_param_set::<16>(family, Params { n: 16, h: 66, d: 22, hp: 3, a: 6,  k: 33, m: 34 }, true);  // 128f
        check_param_set::<24>(family, Params { n: 24, h: 63, d: 7,  hp: 9, a: 14, k: 17, m: 39 }, false); // 192s
        check_param_set::<24>(family, Params { n: 24, h: 66, d: 22, hp: 3, a: 8,  k: 33, m: 42 }, true);  // 192f
        check_param_set::<32>(family, Params { n: 32, h: 64, d: 8,  hp: 8, a: 14, k: 22, m: 47 }, false); // 256s
        check_param_set::<32>(family, Params { n: 32, h: 68, d: 17, hp: 4, a: 9,  k: 35, m: 49 }, true);  // 256f
    }
}
