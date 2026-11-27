// ============================================================================
// SLH-DSA-SHAKE (FIPS 205 §11.1) Metal Compute Kernels
// Concatenated after slhdsa.metal (reuses shared ADRS_* and *Desc/*Params types).
// ============================================================================

struct ShakeKeyMaterial {
    uint64_t sk_seed[4]; // little-endian lanes (first N/8 used)
    uint64_t pk_seed[4]; // little-endian lanes (first N/8 used)
};

// ============================================================================
// Keccak-f[1600] Permutation (In-Place Rho+Pi+Chi for Low GPU Register Pressure)
// ============================================================================

constant uint64_t KECCAK_RC[24] = {
    0x0000000000000001ul, 0x0000000000008082ul, 0x800000000000808aul, 0x8000000080008000ul,
    0x000000000000808bul, 0x0000000080000001ul, 0x8000000080008081ul, 0x8000000000008009ul,
    0x000000000000008aul, 0x0000000000000088ul, 0x0000000080008009ul, 0x000000008000000aul,
    0x000000008000808bul, 0x800000000000008bul, 0x8000000000008089ul, 0x8000000000008003ul,
    0x8000000000008002ul, 0x8000000000000080ul, 0x000000000000800aul, 0x800000008000000aul,
    0x8000000080008081ul, 0x8000000000008080ul, 0x0000000080000001ul, 0x8000000080008008ul
};

inline uint64_t rotl64(uint64_t x, uint64_t n) {
    return (x << n) | (x >> (64ul - n));
}

inline uint32_t bswap32(uint32_t x) {
    return ((x & 0x000000FFu) << 24) |
           ((x & 0x0000FF00u) <<  8) |
           ((x & 0x00FF0000u) >>  8) |
           ((x & 0xFF000000u) >> 24);
}

inline uint64_t bswap64(uint64_t x) {
    uint32_t lo = uint32_t(x);
    uint32_t hi = uint32_t(x >> 32);
    return (uint64_t(bswap32(lo)) << 32) | uint64_t(bswap32(hi));
}

inline void store_le64(device uint8_t *dst, uint64_t v) {
    dst[0] = uint8_t(v);
    dst[1] = uint8_t(v >>  8);
    dst[2] = uint8_t(v >> 16);
    dst[3] = uint8_t(v >> 24);
    dst[4] = uint8_t(v >> 32);
    dst[5] = uint8_t(v >> 40);
    dst[6] = uint8_t(v >> 48);
    dst[7] = uint8_t(v >> 56);
}

template <uint NL>
inline void write_shake_node_bytes(device uint8_t *dst, const thread uint64_t node[NL]) {
    for (uint i = 0; i < NL; ++i) {
        store_le64(dst + 8u * i, node[i]);
    }
}

template <uint NL>
inline void write_shake_node_bytes_tg(device uint8_t *dst, const threadgroup uint64_t *node) {
    for (uint i = 0; i < NL; ++i) {
        store_le64(dst + 8u * i, node[i]);
    }
}

#define KECCAK_PI_RHO(dst, rot) do { uint64_t _t = a[dst]; a[dst] = rotl64(_cur, rot); _cur = _t; } while (0)

#define KECCAK_CHI_ROW(r) do {                         \
    uint64_t _t0 = a[(r) + 0];                         \
    uint64_t _t1 = a[(r) + 1];                         \
    uint64_t _t2 = a[(r) + 2];                         \
    uint64_t _t3 = a[(r) + 3];                         \
    uint64_t _t4 = a[(r) + 4];                         \
    a[(r) + 0] = _t0 ^ ((~_t1) & _t2);                 \
    a[(r) + 1] = _t1 ^ ((~_t2) & _t3);                 \
    a[(r) + 2] = _t2 ^ ((~_t3) & _t4);                 \
    a[(r) + 3] = _t3 ^ ((~_t4) & _t0);                 \
    a[(r) + 4] = _t4 ^ ((~_t0) & _t1);                 \
} while (0)

inline void keccak_f1600(thread uint64_t a[25]) {
    for (uint round = 0u; round < 24u; ++round) {
        // Theta
        uint64_t c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20];
        uint64_t c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21];
        uint64_t c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22];
        uint64_t c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23];
        uint64_t c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24];

        uint64_t d0 = c4 ^ rotl64(c1, 1ul);
        uint64_t d1 = c0 ^ rotl64(c2, 1ul);
        uint64_t d2 = c1 ^ rotl64(c3, 1ul);
        uint64_t d3 = c2 ^ rotl64(c4, 1ul);
        uint64_t d4 = c3 ^ rotl64(c0, 1ul);

        a[ 0] ^= d0; a[ 5] ^= d0; a[10] ^= d0; a[15] ^= d0; a[20] ^= d0;
        a[ 1] ^= d1; a[ 6] ^= d1; a[11] ^= d1; a[16] ^= d1; a[21] ^= d1;
        a[ 2] ^= d2; a[ 7] ^= d2; a[12] ^= d2; a[17] ^= d2; a[22] ^= d2;
        a[ 3] ^= d3; a[ 8] ^= d3; a[13] ^= d3; a[18] ^= d3; a[23] ^= d3;
        a[ 4] ^= d4; a[ 9] ^= d4; a[14] ^= d4; a[19] ^= d4; a[24] ^= d4;

        // Rho + Pi (in-place 24-cycle)
        uint64_t _cur = a[1];
        KECCAK_PI_RHO(10,  1ul);
        KECCAK_PI_RHO( 7,  3ul);
        KECCAK_PI_RHO(11,  6ul);
        KECCAK_PI_RHO(17, 10ul);
        KECCAK_PI_RHO(18, 15ul);
        KECCAK_PI_RHO( 3, 21ul);
        KECCAK_PI_RHO( 5, 28ul);
        KECCAK_PI_RHO(16, 36ul);
        KECCAK_PI_RHO( 8, 45ul);
        KECCAK_PI_RHO(21, 55ul);
        KECCAK_PI_RHO(24,  2ul);
        KECCAK_PI_RHO( 4, 14ul);
        KECCAK_PI_RHO(15, 27ul);
        KECCAK_PI_RHO(23, 41ul);
        KECCAK_PI_RHO(19, 56ul);
        KECCAK_PI_RHO(13,  8ul);
        KECCAK_PI_RHO(12, 25ul);
        KECCAK_PI_RHO( 2, 43ul);
        KECCAK_PI_RHO(20, 62ul);
        KECCAK_PI_RHO(14, 18ul);
        KECCAK_PI_RHO(22, 39ul);
        KECCAK_PI_RHO( 9, 61ul);
        KECCAK_PI_RHO( 6, 20ul);
        a[1] = rotl64(_cur, 44ul);

        // Chi
        KECCAK_CHI_ROW(0);
        KECCAK_CHI_ROW(5);
        KECCAK_CHI_ROW(10);
        KECCAK_CHI_ROW(15);
        KECCAK_CHI_ROW(20);

        // Iota
        a[0] ^= KECCAK_RC[round];
    }
}

// ============================================================================
// SHAKE256 Tweakable Hashes (Full 32-Byte ADRS, All Lane-Aligned!)
// ============================================================================

inline void adrs_full_lanes(
    uint32_t layer,
    uint64_t tree,
    uint32_t typ,
    uint32_t keypair,
    uint32_t word2,
    uint32_t word3,
    thread uint64_t &ad0,
    thread uint64_t &ad1,
    thread uint64_t &ad2,
    thread uint64_t &ad3
) {
    ad0 = uint64_t(bswap32(layer));
    ad1 = bswap64(tree);
    ad2 = uint64_t(bswap32(typ)) | (uint64_t(bswap32(keypair)) << 32);
    ad3 = uint64_t(bswap32(word2)) | (uint64_t(bswap32(word3)) << 32);
}

// Single-block SHAKE256 tweakable hash (F or PRF): PK.seed (NL) || ADRS (4) || val (NL)
// Total lanes = 2*NL + 4 <= 12 < 17 (always fits in 1 Keccak block!)
template <uint NL>
inline void shake_thash_short(
    const thread uint64_t pk_seed[NL],
    uint64_t ad0, uint64_t ad1, uint64_t ad2, uint64_t ad3,
    const thread uint64_t in_val[NL],
    thread uint64_t out_val[NL]
) {
    uint64_t st[25];
    for (uint i = 0; i < NL; ++i) st[i] = pk_seed[i];
    st[NL + 0] = ad0;
    st[NL + 1] = ad1;
    st[NL + 2] = ad2;
    st[NL + 3] = ad3;
    for (uint i = 0; i < NL; ++i) st[NL + 4 + i] = in_val[i];
    st[2 * NL + 4] = 0x1Ful;
    for (uint i = 2 * NL + 5; i < 25; ++i) st[i] = 0ul;
    st[16] |= 0x8000000000000000ul;

    keccak_f1600(st);
    for (uint i = 0; i < NL; ++i) out_val[i] = st[i];
}

// Single-block SHAKE256 pair hash (H): PK.seed (NL) || ADRS (4) || left (NL) || right (NL)
// Total lanes = 3*NL + 4 <= 16 < 17 (always fits in 1 Keccak block!)
template <uint NL>
inline void shake_thash_pair(
    const device ShakeKeyMaterial &km,
    uint32_t layer,
    uint64_t tree,
    uint32_t typ,
    uint32_t keypair,
    uint32_t height,
    uint32_t index,
    const thread uint64_t left[NL],
    const thread uint64_t right[NL],
    thread uint64_t out[NL]
) {
    uint64_t st[25];
    for (uint i = 0; i < NL; ++i) st[i] = km.pk_seed[i];
    adrs_full_lanes(layer, tree, typ, keypair, height, index,
                    st[NL + 0], st[NL + 1], st[NL + 2], st[NL + 3]);
    for (uint i = 0; i < NL; ++i) st[NL + 4 + i] = left[i];
    for (uint i = 0; i < NL; ++i) st[2 * NL + 4 + i] = right[i];
    for (uint i = 3 * NL + 4; i < 25; ++i) st[i] = 0ul;
    // Note: when NL == 4, 3*NL + 4 == 16, so 0x1F and 0x80..00 both XOR into st[16]!
    st[3 * NL + 4] ^= 0x1Ful;
    st[16] ^= 0x8000000000000000ul;

    keccak_f1600(st);
    for (uint i = 0; i < NL; ++i) out[i] = st[i];
}

// Streaming lane-aligned SHAKE256 sponge for T_len (WOTS_PK) and T_k (FORS_ROOTS)
struct ShakeSponge {
    uint64_t st[25];
    uint32_t pos;

    template <uint NL>
    void init(const device uint64_t pk_seed[4], uint32_t layer, uint64_t tree,
              uint32_t typ, uint32_t keypair) {
        for (uint i = 0; i < 25; ++i) st[i] = 0ul;
        for (uint i = 0; i < NL; ++i) st[i] = pk_seed[i];
        adrs_full_lanes(layer, tree, typ, keypair, 0u, 0u,
                        st[NL + 0], st[NL + 1], st[NL + 2], st[NL + 3]);
        pos = NL + 4u;
    }

    inline void absorb_lane(uint64_t lane) {
        st[pos++] ^= lane;
        if (pos == 17u) {
            keccak_f1600(st);
            pos = 0u;
        }
    }

    template <uint NL>
    void finish(thread uint64_t out[NL]) {
        st[pos] ^= 0x1Ful;
        st[16] ^= 0x8000000000000000ul;
        keccak_f1600(st);
        for (uint i = 0; i < NL; ++i) out[i] = st[i];
    }
};

template <uint NL>
inline void shake_run_wots_chain(
    const thread uint64_t pk_seed[NL],
    const thread uint64_t sk_seed[NL],
    uint32_t layer,
    uint64_t tree,
    uint32_t keypair,
    uint32_t chain,
    uint32_t steps,
    thread uint64_t val[NL]
) {
    uint64_t ad0, ad1, ad2, ad3;
    adrs_full_lanes(layer, tree, ADRS_WOTS_PRF, keypair, chain, 0u, ad0, ad1, ad2, ad3);
    shake_thash_short<NL>(pk_seed, ad0, ad1, ad2, ad3, sk_seed, val);
    if (steps == 0u) return;

    // Switch type from WOTS_PRF (5) to WOTS_HASH (0): clear low 32 bits of ad2
    ad2 &= 0xFFFFFFFF00000000ul;
    uint64_t ad3_base = uint64_t(bswap32(chain));
    for (uint32_t s = 0u; s < steps; ++s) {
        uint64_t ad3_s = ad3_base | (uint64_t(bswap32(s)) << 32);
        shake_thash_short<NL>(pk_seed, ad0, ad1, ad2, ad3_s, val, val);
    }
}

// ============================================================================
// SHAKE Kernel 1: shake_wots_chains (1 thread per WOTS+ chain)
// ============================================================================

template <uint NL>
inline void shake_wots_chains_impl(
    const device ShakeKeyMaterial *keys,
    const device XmssTreeDesc *trees,
    device uint64_t *out_chain_tips,
    constant XmssParams &p,
    uint32_t gid
) {
    uint32_t total_chains = p.num_trees * p.leaves_per_tree * p.wots_len;
    if (gid >= total_chains) return;

    uint32_t chain = gid % p.wots_len;
    uint32_t leaf_global = gid / p.wots_len;
    uint32_t leaf_idx = leaf_global % p.leaves_per_tree;
    uint32_t tree_idx = leaf_global / p.leaves_per_tree;

    XmssTreeDesc desc = trees[tree_idx];
    uint64_t pk_seed[NL], sk_seed[NL];
    for (uint i = 0; i < NL; ++i) {
        pk_seed[i] = keys[desc.key_idx].pk_seed[i];
        sk_seed[i] = keys[desc.key_idx].sk_seed[i];
    }

    uint64_t tip[NL];
    shake_run_wots_chain<NL>(pk_seed, sk_seed, desc.layer, desc.tree, leaf_idx, chain, 15u, tip);

    uint32_t out_off = gid * NL;
    for (uint i = 0; i < NL; ++i) {
        out_chain_tips[out_off + i] = tip[i];
    }
}

// ============================================================================
// SHAKE Kernel 2: shake_wots_tlen (1 thread per WOTS+ leaf)
// ============================================================================

template <uint NL>
inline void shake_wots_tlen_impl(
    const device ShakeKeyMaterial *keys,
    const device XmssTreeDesc *trees,
    const device uint64_t *chain_tips,
    device uint64_t *out_leaves,
    constant XmssParams &p,
    uint32_t gid
) {
    uint32_t total_leaves = p.num_trees * p.leaves_per_tree;
    if (gid >= total_leaves) return;

    uint32_t leaf_idx = gid % p.leaves_per_tree;
    uint32_t tree_idx = gid / p.leaves_per_tree;
    XmssTreeDesc desc = trees[tree_idx];
    uint32_t tip_base = gid * p.wots_len * NL;

    ShakeSponge sp;
    sp.init<NL>(keys[desc.key_idx].pk_seed, desc.layer, desc.tree, ADRS_WOTS_PK, leaf_idx);
    uint32_t total_lanes = p.wots_len * NL;
    for (uint32_t i = 0; i < total_lanes; ++i) {
        sp.absorb_lane(chain_tips[tip_base + i]);
    }
    uint64_t leaf[NL];
    sp.finish<NL>(leaf);

    uint32_t out_off = gid * NL;
    for (uint i = 0; i < NL; ++i) {
        out_leaves[out_off + i] = leaf[i];
    }
}

// ============================================================================
// SHAKE Kernel 3: shake_xmss_leaves_streaming (zero intermediate buffer)
// ============================================================================

template <uint NL>
inline void shake_xmss_leaves_streaming_impl(
    const device ShakeKeyMaterial *keys,
    const device XmssTreeDesc *trees,
    device uint64_t *out_leaves,
    constant XmssParams &p,
    uint32_t gid
) {
    uint32_t total_leaves = p.num_trees * p.leaves_per_tree;
    if (gid >= total_leaves) return;

    uint32_t leaf_idx = gid % p.leaves_per_tree;
    uint32_t tree_idx = gid / p.leaves_per_tree;
    XmssTreeDesc desc = trees[tree_idx];

    uint64_t pk_seed[NL], sk_seed[NL];
    for (uint i = 0; i < NL; ++i) {
        pk_seed[i] = keys[desc.key_idx].pk_seed[i];
        sk_seed[i] = keys[desc.key_idx].sk_seed[i];
    }

    ShakeSponge sp;
    sp.init<NL>(keys[desc.key_idx].pk_seed, desc.layer, desc.tree, ADRS_WOTS_PK, leaf_idx);
    for (uint32_t c = 0; c < p.wots_len; ++c) {
        uint64_t tip[NL];
        shake_run_wots_chain<NL>(pk_seed, sk_seed, desc.layer, desc.tree, leaf_idx, c, 15u, tip);
        for (uint i = 0; i < NL; ++i) {
            sp.absorb_lane(tip[i]);
        }
    }
    uint64_t leaf[NL];
    sp.finish<NL>(leaf);

    uint32_t out_off = gid * NL;
    for (uint i = 0; i < NL; ++i) {
        out_leaves[out_off + i] = leaf[i];
    }
}

// ============================================================================
// SHAKE Kernel 4: shake_xmss_reduce (1 threadgroup of 2^(hp-1) threads per tree)
// ============================================================================

template <uint NL>
inline void shake_xmss_reduce_impl(
    const device ShakeKeyMaterial *keys,
    const device XmssTreeDesc *trees,
    const device uint64_t *leaves,
    device uint64_t *out_roots,
    device uint8_t *out_sigs,
    constant XmssParams &p,
    threadgroup uint64_t *tg_nodes,
    uint32_t tg_id,
    uint32_t tid
) {
    if (tg_id >= p.num_trees) return;

    XmssTreeDesc desc = trees[tg_id];
    const device ShakeKeyMaterial &km = keys[desc.key_idx];
    uint32_t leaf_base = tg_id * p.leaves_per_tree;
    uint32_t half_leaves = p.leaves_per_tree >> 1;
    bool has_auth = (desc.target_leaf != 0xFFFFFFFFu);

    if (has_auth && tid == 0u) {
        uint32_t sib0 = desc.target_leaf ^ 1u;
        uint32_t sib_off = (leaf_base + sib0) * NL;
        uint64_t node[NL];
        for (uint i = 0; i < NL; ++i) node[i] = leaves[sib_off + i];
        write_shake_node_bytes<NL>(out_sigs + desc.auth_byte_off, node);
    }

    {
        uint64_t left[NL], right[NL], parent[NL];
        uint32_t l_off = (leaf_base + 2u * tid) * NL;
        uint32_t r_off = (leaf_base + 2u * tid + 1u) * NL;
        for (uint i = 0; i < NL; ++i) {
            left[i] = leaves[l_off + i];
            right[i] = leaves[r_off + i];
        }
        shake_thash_pair<NL>(km, desc.layer, desc.tree, ADRS_TREE, 0u, 1u, tid, left, right, parent);
        for (uint i = 0; i < NL; ++i) {
            tg_nodes[tid * NL + i] = parent[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint32_t cur_cnt = half_leaves >> 1;
    for (uint32_t lvl = 2u; lvl <= p.hp; ++lvl) {
        if (has_auth) {
            uint32_t sib = (desc.target_leaf >> (lvl - 1u)) ^ 1u;
            if (tid == sib) {
                write_shake_node_bytes_tg<NL>(out_sigs + desc.auth_byte_off + (lvl - 1u) * NL * 8u,
                                              tg_nodes + tid * NL);
            }
        }
        uint64_t parent[NL];
        if (tid < cur_cnt) {
            uint64_t left[NL], right[NL];
            for (uint i = 0; i < NL; ++i) {
                left[i] = tg_nodes[(2u * tid) * NL + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NL + i];
            }
            shake_thash_pair<NL>(km, desc.layer, desc.tree, ADRS_TREE, 0u, lvl, tid, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NL; ++i) {
                tg_nodes[tid * NL + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        cur_cnt >>= 1;
    }

    if (tid == 0u) {
        uint32_t out_off = tg_id * NL;
        for (uint i = 0; i < NL; ++i) {
            out_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// SHAKE Kernel 5: shake_fors_pass1 (2 leaves per thread -> 100% active lvl 1)
// ============================================================================

template <uint NL>
inline void shake_fors_pass1_impl(
    const device ShakeKeyMaterial *keys,
    const device ForsJobDesc *jobs,
    device uint64_t *out_sub_roots,
    device uint8_t *out_sigs,
    constant ForsParams &p,
    threadgroup uint64_t *tg_nodes,
    uint32_t tg_id,
    uint32_t tid
) {
    uint32_t total_tgs = p.num_sigs * p.k * p.subtrees_per_tree;
    if (tg_id >= total_tgs) return;

    uint32_t st_local = tg_id % p.subtrees_per_tree;
    uint32_t tmp = tg_id / p.subtrees_per_tree;
    uint32_t tree_i = tmp % p.k;
    uint32_t sig_idx = tmp / p.k;

    const device ForsJobDesc &job = jobs[sig_idx];
    const device ShakeKeyMaterial &km = keys[job.key_idx];

    uint64_t pk_seed[NL], sk_seed[NL];
    for (uint i = 0; i < NL; ++i) {
        pk_seed[i] = km.pk_seed[i];
        sk_seed[i] = km.sk_seed[i];
    }

    uint32_t leaf0_in_tree = (st_local << p.s1) + (2u * tid);
    uint32_t leaf1_in_tree = leaf0_in_tree + 1u;
    uint32_t leaf0_word3 = (tree_i << p.a) + leaf0_in_tree;
    uint32_t leaf1_word3 = leaf0_word3 + 1u;
    uint32_t target = job.indices[tree_i];
    uint32_t n_bytes = NL * 8u;
    uint32_t fors_tree_sig_off = job.sig_byte_off + n_bytes + tree_i * (1u + p.a) * n_bytes;

    uint64_t ad0, ad1, ad2_prf, ad3_0;
    adrs_full_lanes(0u, job.idx_tree, ADRS_FORS_PRF, job.idx_leaf, 0u, leaf0_word3,
                    ad0, ad1, ad2_prf, ad3_0);
    uint64_t ad2_tree = uint64_t(bswap32(ADRS_FORS_TREE)) | (uint64_t(bswap32(job.idx_leaf)) << 32);
    uint64_t ad3_1 = uint64_t(bswap32(leaf1_word3)) << 32;

    uint64_t sk0[NL], leaf0[NL], sk1[NL], leaf1[NL];
    shake_thash_short<NL>(pk_seed, ad0, ad1, ad2_prf, ad3_0, sk_seed, sk0);
    shake_thash_short<NL>(pk_seed, ad0, ad1, ad2_tree, ad3_0, sk0, leaf0);
    shake_thash_short<NL>(pk_seed, ad0, ad1, ad2_prf, ad3_1, sk_seed, sk1);
    shake_thash_short<NL>(pk_seed, ad0, ad1, ad2_tree, ad3_1, sk1, leaf1);

    if (leaf0_in_tree == target) {
        write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off, sk0);
        write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off + n_bytes, leaf1);
    } else if (leaf1_in_tree == target) {
        write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off, sk1);
        write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off + n_bytes, leaf0);
    }

    {
        uint64_t parent1[NL];
        uint32_t node1_word3 = (tree_i << (p.a - 1u)) + (st_local << (p.s1 - 1u)) + tid;
        shake_thash_pair<NL>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                             1u, node1_word3, leaf0, leaf1, parent1);
        for (uint i = 0; i < NL; ++i) {
            tg_nodes[tid * NL + i] = parent1[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    bool in_subtree = ((target >> p.s1) == st_local);

    for (uint32_t lvl = 2u; lvl <= p.s1; ++lvl) {
        uint32_t cur_cnt = 1u << (p.s1 - lvl);
        if (in_subtree) {
            uint32_t sib_in_tree = (target >> (lvl - 1u)) ^ 1u;
            uint32_t mask = (1u << (p.s1 - lvl + 1u)) - 1u;
            uint32_t sib_local = sib_in_tree & mask;
            if (tid == sib_local) {
                write_shake_node_bytes_tg<NL>(out_sigs + fors_tree_sig_off + lvl * n_bytes,
                                              tg_nodes + tid * NL);
            }
        }
        uint64_t parent[NL];
        if (tid < cur_cnt) {
            uint64_t left[NL], right[NL];
            for (uint i = 0; i < NL; ++i) {
                left[i] = tg_nodes[(2u * tid) * NL + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NL + i];
            }
            uint32_t node_word3 = (tree_i << (p.a - lvl)) + (st_local << (p.s1 - lvl)) + tid;
            shake_thash_pair<NL>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                                 lvl, node_word3, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NL; ++i) {
                tg_nodes[tid * NL + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0u) {
        uint32_t out_off = ((sig_idx * p.k + tree_i) * p.subtrees_per_tree + st_local) * NL;
        for (uint i = 0; i < NL; ++i) {
            out_sub_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// SHAKE Kernel 6: shake_fors_pass2 (2 sub-roots per thread, s2 > 0)
// ============================================================================

template <uint NL>
inline void shake_fors_pass2_impl(
    const device ShakeKeyMaterial *keys,
    const device ForsJobDesc *jobs,
    const device uint64_t *in_sub_roots,
    device uint64_t *out_fors_roots,
    device uint8_t *out_sigs,
    constant ForsParams &p,
    threadgroup uint64_t *tg_nodes,
    uint32_t tg_id,
    uint32_t tid
) {
    uint32_t total_trees = p.num_sigs * p.k;
    if (tg_id >= total_trees) return;

    uint32_t tree_i = tg_id % p.k;
    uint32_t sig_idx = tg_id / p.k;
    const device ForsJobDesc &job = jobs[sig_idx];
    const device ShakeKeyMaterial &km = keys[job.key_idx];

    uint32_t target = job.indices[tree_i];
    uint32_t n_bytes = NL * 8u;
    uint32_t fors_tree_sig_off = job.sig_byte_off + n_bytes + tree_i * (1u + p.a) * n_bytes;

    {
        uint32_t l_off = (tg_id * p.subtrees_per_tree + 2u * tid) * NL;
        uint32_t r_off = l_off + NL;
        uint64_t left[NL], right[NL], parent1[NL];
        for (uint i = 0; i < NL; ++i) {
            left[i] = in_sub_roots[l_off + i];
            right[i] = in_sub_roots[r_off + i];
        }
        uint32_t lvl1 = p.s1 + 1u;
        uint32_t sib1 = (target >> p.s1) ^ 1u;
        if (2u * tid == sib1) {
            write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off + lvl1 * n_bytes, left);
        } else if (2u * tid + 1u == sib1) {
            write_shake_node_bytes<NL>(out_sigs + fors_tree_sig_off + lvl1 * n_bytes, right);
        }
        uint32_t node1_word3 = (tree_i << (p.a - lvl1)) + tid;
        shake_thash_pair<NL>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                             lvl1, node1_word3, left, right, parent1);
        for (uint i = 0; i < NL; ++i) {
            tg_nodes[tid * NL + i] = parent1[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint32_t step = 2u; step <= p.s2; ++step) {
        uint32_t lvl = p.s1 + step;
        uint32_t cur_cnt = 1u << (p.s2 - step);
        uint32_t sib = (target >> (lvl - 1u)) ^ 1u;
        if (tid == sib) {
            write_shake_node_bytes_tg<NL>(out_sigs + fors_tree_sig_off + lvl * n_bytes,
                                          tg_nodes + tid * NL);
        }
        uint64_t parent[NL];
        if (tid < cur_cnt) {
            uint64_t left[NL], right[NL];
            for (uint i = 0; i < NL; ++i) {
                left[i] = tg_nodes[(2u * tid) * NL + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NL + i];
            }
            uint32_t node_word3 = (tree_i << (p.a - lvl)) + tid;
            shake_thash_pair<NL>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                                 lvl, node_word3, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NL; ++i) {
                tg_nodes[tid * NL + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0u) {
        uint32_t out_off = tg_id * NL;
        for (uint i = 0; i < NL; ++i) {
            out_fors_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// SHAKE Kernel 7: shake_fors_pk (1 thread per signature: T_k over k FORS roots)
// ============================================================================

template <uint NL>
inline void shake_fors_pk_impl(
    const device ShakeKeyMaterial *keys,
    const device ForsJobDesc *jobs,
    const device uint64_t *fors_roots,
    device uint64_t *out_pk_fors,
    constant ForsParams &p,
    uint32_t sig_idx
) {
    if (sig_idx >= p.num_sigs) return;

    const device ForsJobDesc &job = jobs[sig_idx];
    const device ShakeKeyMaterial &km = keys[job.key_idx];
    uint32_t root_base = sig_idx * p.k * NL;

    ShakeSponge sp;
    sp.init<NL>(km.pk_seed, 0u, job.idx_tree, ADRS_FORS_ROOTS, job.idx_leaf);
    uint32_t total_lanes = p.k * NL;
    for (uint32_t i = 0; i < total_lanes; ++i) {
        sp.absorb_lane(fors_roots[root_base + i]);
    }
    uint64_t pk[NL];
    sp.finish<NL>(pk);

    uint32_t out_off = sig_idx * NL;
    for (uint i = 0; i < NL; ++i) {
        out_pk_fors[out_off + i] = pk[i];
    }
}

// ============================================================================
// SHAKE Kernel 8: shake_wots_sign (1 thread per WOTS+ chain across all layers)
// ============================================================================

template <uint NL>
inline uint32_t shake_wots_digit_at(const thread uint64_t msg[NL], uint32_t chain) {
    uint32_t len1 = 16u * NL; // 2 * N = 16 * (N / 8)
    if (chain < len1) {
        uint32_t byte_idx = chain >> 1;
        uint8_t b = uint8_t(msg[byte_idx >> 3] >> (8u * (byte_idx & 7u)));
        return ((chain & 1u) == 0u) ? ((b >> 4) & 0xFu) : (b & 0xFu);
    }
    uint32_t csum = 0u;
    for (uint i = 0; i < NL; ++i) {
        uint64_t lane = msg[i];
        for (uint b = 0; b < 8u; ++b) {
            uint32_t byte_val = uint32_t((lane >> (8u * b)) & 0xFFul);
            csum += 15u - ((byte_val >> 4) & 0xFu);
            csum += 15u - (byte_val & 0xFu);
        }
    }
    uint32_t c_idx = chain - len1; // 0, 1, or 2
    return (csum >> (8u - 4u * c_idx)) & 0xFu;
}

template <uint NL>
inline void shake_wots_sign_impl(
    const device ShakeKeyMaterial *keys,
    const device WotsSignLayerDesc *layers,
    const device uint64_t *pk_fors,
    const device uint64_t *xmss_roots,
    device uint8_t *out_sigs,
    constant WotsSignParams &p,
    uint32_t gid
) {
    uint32_t total_chains = p.num_layers * p.wots_len;
    if (gid >= total_chains) return;

    uint32_t chain = gid % p.wots_len;
    uint32_t layer_global = gid / p.wots_len;
    WotsSignLayerDesc desc = layers[layer_global];
    const device ShakeKeyMaterial &km = keys[desc.key_idx];

    uint64_t msg[NL];
    if (desc.layer == 0u) {
        uint32_t off = desc.sig_idx * NL;
        for (uint i = 0; i < NL; ++i) msg[i] = pk_fors[off + i];
    } else {
        uint32_t off = (desc.sig_idx * p.d + (desc.layer - 1u)) * NL;
        for (uint i = 0; i < NL; ++i) msg[i] = xmss_roots[off + i];
    }

    uint32_t steps = shake_wots_digit_at<NL>(msg, chain);

    uint64_t pk_seed[NL], sk_seed[NL];
    for (uint i = 0; i < NL; ++i) {
        pk_seed[i] = km.pk_seed[i];
        sk_seed[i] = km.sk_seed[i];
    }

    uint64_t sig_val[NL];
    shake_run_wots_chain<NL>(pk_seed, sk_seed, desc.layer, desc.tree, desc.keypair, chain, steps, sig_val);

    write_shake_node_bytes<NL>(out_sigs + desc.wots_byte_off + chain * NL * 8u, sig_val);
}

// ============================================================================
// Concrete SHAKE Kernel Entry Points for N = 16 (NL=2), N = 24 (NL=3), N = 32 (NL=4)
// ============================================================================

#define DEFINE_SHAKE_KERNELS(SUFFIX, NL)                                             \
kernel void shake_wots_chains_##SUFFIX(                                              \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    device uint64_t *out_chain_tips [[buffer(2)]],                                   \
    constant XmssParams &p [[buffer(3)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    shake_wots_chains_impl<NL>(keys, trees, out_chain_tips, p, gid);                 \
}                                                                                    \
                                                                                     \
kernel void shake_wots_tlen_##SUFFIX(                                                \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    const device uint64_t *chain_tips [[buffer(2)]],                                 \
    device uint64_t *out_leaves [[buffer(3)]],                                       \
    constant XmssParams &p [[buffer(4)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    shake_wots_tlen_impl<NL>(keys, trees, chain_tips, out_leaves, p, gid);           \
}                                                                                    \
                                                                                     \
kernel void shake_xmss_leaves_streaming_##SUFFIX(                                    \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    device uint64_t *out_leaves [[buffer(2)]],                                       \
    constant XmssParams &p [[buffer(3)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    shake_xmss_leaves_streaming_impl<NL>(keys, trees, out_leaves, p, gid);           \
}                                                                                    \
                                                                                     \
kernel void shake_xmss_reduce_##SUFFIX(                                              \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    const device uint64_t *leaves [[buffer(2)]],                                     \
    device uint64_t *out_roots [[buffer(3)]],                                        \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant XmssParams &p [[buffer(5)]],                                            \
    threadgroup uint64_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    shake_xmss_reduce_impl<NL>(keys, trees, leaves, out_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void shake_fors_pass1_##SUFFIX(                                               \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    device uint64_t *out_sub_roots [[buffer(2)]],                                    \
    device uint8_t *out_sigs [[buffer(3)]],                                          \
    constant ForsParams &p [[buffer(4)]],                                            \
    threadgroup uint64_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    shake_fors_pass1_impl<NL>(keys, jobs, out_sub_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void shake_fors_pass2_##SUFFIX(                                               \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    const device uint64_t *in_sub_roots [[buffer(2)]],                               \
    device uint64_t *out_fors_roots [[buffer(3)]],                                   \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant ForsParams &p [[buffer(5)]],                                            \
    threadgroup uint64_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    shake_fors_pass2_impl<NL>(keys, jobs, in_sub_roots, out_fors_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void shake_fors_pk_##SUFFIX(                                                  \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    const device uint64_t *fors_roots [[buffer(2)]],                                 \
    device uint64_t *out_pk_fors [[buffer(3)]],                                      \
    constant ForsParams &p [[buffer(4)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    shake_fors_pk_impl<NL>(keys, jobs, fors_roots, out_pk_fors, p, gid);             \
}                                                                                    \
                                                                                     \
kernel void shake_wots_sign_##SUFFIX(                                                \
    const device ShakeKeyMaterial *keys [[buffer(0)]],                               \
    const device WotsSignLayerDesc *layers [[buffer(1)]],                            \
    const device uint64_t *pk_fors [[buffer(2)]],                                    \
    const device uint64_t *xmss_roots [[buffer(3)]],                                 \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant WotsSignParams &p [[buffer(5)]],                                        \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    shake_wots_sign_impl<NL>(keys, layers, pk_fors, xmss_roots, out_sigs, p, gid);   \
}

DEFINE_SHAKE_KERNELS(N16, 2)
DEFINE_SHAKE_KERNELS(N24, 3)
DEFINE_SHAKE_KERNELS(N32, 4)
