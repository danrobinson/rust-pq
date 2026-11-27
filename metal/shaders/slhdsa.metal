#include <metal_stdlib>
using namespace metal;

// ============================================================================
// Constants & Shared Structs (matching #[repr(C)] Rust definitions)
// ============================================================================

constant uint32_t ADRS_WOTS_HASH  = 0u;
constant uint32_t ADRS_WOTS_PK    = 1u;
constant uint32_t ADRS_TREE       = 2u;
constant uint32_t ADRS_FORS_TREE  = 3u;
constant uint32_t ADRS_FORS_ROOTS = 4u;
constant uint32_t ADRS_WOTS_PRF   = 5u;
constant uint32_t ADRS_FORS_PRF   = 6u;

struct KeyMaterial {
    uint32_t sk_seed[8];   // big-endian words (first N/4 used)
    uint32_t state256[8];  // SHA-256 state after PK.seed || 0^{64-N}
    uint64_t state512[8];  // SHA-512 state after PK.seed || 0^{128-N}
};

struct XmssTreeDesc {
    uint64_t tree;
    uint32_t key_idx;
    uint32_t layer;
    uint32_t target_leaf;   // 0xFFFFFFFFu for keygen (no auth extraction)
    uint32_t auth_byte_off; // byte offset in out_sigs for hp * N auth bytes
};

struct ForsJobDesc {
    uint64_t idx_tree;
    uint32_t key_idx;
    uint32_t idx_leaf;
    uint32_t sig_byte_off;  // byte offset of signature start in out_sigs
    uint32_t _pad;
    uint32_t indices[36];   // fors_indices[0..k]
};

struct WotsSignLayerDesc {
    uint64_t tree;
    uint32_t key_idx;
    uint32_t layer;
    uint32_t keypair;
    uint32_t sig_idx;
    uint32_t wots_byte_off;
    uint32_t _pad;
};

struct XmssParams {
    uint32_t num_trees;
    uint32_t hp;
    uint32_t leaves_per_tree;
    uint32_t wots_len;
};

struct ForsParams {
    uint32_t num_sigs;
    uint32_t k;
    uint32_t a;
    uint32_t s1;
    uint32_t s2;
    uint32_t subtrees_per_tree;
};

struct WotsSignParams {
    uint32_t num_layers;
    uint32_t d;
    uint32_t wots_len;
};

// ============================================================================
// SHA-256 Compression (Register-Resident Unrolled Rolling 16-Word Schedule)
// ============================================================================

constant uint32_t K256[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

inline uint32_t rotr32(uint32_t x, uint32_t n) {
    return rotate(x, 32u - n);
}

#define SHA256_R(a, b, c, d, e, f, g, h, k, wi)                                      \
    do {                                                                             \
        uint32_t s1 = rotr32(e, 6u) ^ rotr32(e, 11u) ^ rotr32(e, 25u);               \
        uint32_t ch = g ^ (e & (f ^ g));                                             \
        uint32_t t1 = h + s1 + ch + (k) + (wi);                                      \
        uint32_t s0 = rotr32(a, 2u) ^ rotr32(a, 13u) ^ rotr32(a, 22u);               \
        uint32_t maj = (a & b) | (c & (a | b));                                      \
        d += t1;                                                                     \
        h = t1 + s0 + maj;                                                           \
    } while (0)

#define SHA256_WEXT(w, j)                                                            \
    do {                                                                             \
        uint32_t x = w[((j) + 1) & 15];                                              \
        uint32_t y = w[((j) + 14) & 15];                                             \
        uint32_t ss0 = rotr32(x, 7u) ^ rotr32(x, 18u) ^ (x >> 3);                    \
        uint32_t ss1 = rotr32(y, 17u) ^ rotr32(y, 19u) ^ (y >> 10);                  \
        w[(j)] = w[(j)] + ss0 + w[((j) + 9) & 15] + ss1;                             \
    } while (0)

#define SHA256_16_INIT(w)                                                            \
    SHA256_R(a, b, c, d, e, f, g, h, K256[ 0], w[ 0]);                               \
    SHA256_R(h, a, b, c, d, e, f, g, K256[ 1], w[ 1]);                               \
    SHA256_R(g, h, a, b, c, d, e, f, K256[ 2], w[ 2]);                               \
    SHA256_R(f, g, h, a, b, c, d, e, K256[ 3], w[ 3]);                               \
    SHA256_R(e, f, g, h, a, b, c, d, K256[ 4], w[ 4]);                               \
    SHA256_R(d, e, f, g, h, a, b, c, K256[ 5], w[ 5]);                               \
    SHA256_R(c, d, e, f, g, h, a, b, K256[ 6], w[ 6]);                               \
    SHA256_R(b, c, d, e, f, g, h, a, K256[ 7], w[ 7]);                               \
    SHA256_R(a, b, c, d, e, f, g, h, K256[ 8], w[ 8]);                               \
    SHA256_R(h, a, b, c, d, e, f, g, K256[ 9], w[ 9]);                               \
    SHA256_R(g, h, a, b, c, d, e, f, K256[10], w[10]);                               \
    SHA256_R(f, g, h, a, b, c, d, e, K256[11], w[11]);                               \
    SHA256_R(e, f, g, h, a, b, c, d, K256[12], w[12]);                               \
    SHA256_R(d, e, f, g, h, a, b, c, K256[13], w[13]);                               \
    SHA256_R(c, d, e, f, g, h, a, b, K256[14], w[14]);                               \
    SHA256_R(b, c, d, e, f, g, h, a, K256[15], w[15]);

#define SHA256_16_EXT(w, base)                                                       \
    SHA256_WEXT(w,  0); SHA256_R(a, b, c, d, e, f, g, h, K256[(base) +  0], w[ 0]);  \
    SHA256_WEXT(w,  1); SHA256_R(h, a, b, c, d, e, f, g, K256[(base) +  1], w[ 1]);  \
    SHA256_WEXT(w,  2); SHA256_R(g, h, a, b, c, d, e, f, K256[(base) +  2], w[ 2]);  \
    SHA256_WEXT(w,  3); SHA256_R(f, g, h, a, b, c, d, e, K256[(base) +  3], w[ 3]);  \
    SHA256_WEXT(w,  4); SHA256_R(e, f, g, h, a, b, c, d, K256[(base) +  4], w[ 4]);  \
    SHA256_WEXT(w,  5); SHA256_R(d, e, f, g, h, a, b, c, K256[(base) +  5], w[ 5]);  \
    SHA256_WEXT(w,  6); SHA256_R(c, d, e, f, g, h, a, b, K256[(base) +  6], w[ 6]);  \
    SHA256_WEXT(w,  7); SHA256_R(b, c, d, e, f, g, h, a, K256[(base) +  7], w[ 7]);  \
    SHA256_WEXT(w,  8); SHA256_R(a, b, c, d, e, f, g, h, K256[(base) +  8], w[ 8]);  \
    SHA256_WEXT(w,  9); SHA256_R(h, a, b, c, d, e, f, g, K256[(base) +  9], w[ 9]);  \
    SHA256_WEXT(w, 10); SHA256_R(g, h, a, b, c, d, e, f, K256[(base) + 10], w[10]);  \
    SHA256_WEXT(w, 11); SHA256_R(f, g, h, a, b, c, d, e, K256[(base) + 11], w[11]);  \
    SHA256_WEXT(w, 12); SHA256_R(e, f, g, h, a, b, c, d, K256[(base) + 12], w[12]);  \
    SHA256_WEXT(w, 13); SHA256_R(d, e, f, g, h, a, b, c, K256[(base) + 13], w[13]);  \
    SHA256_WEXT(w, 14); SHA256_R(c, d, e, f, g, h, a, b, K256[(base) + 14], w[14]);  \
    SHA256_WEXT(w, 15); SHA256_R(b, c, d, e, f, g, h, a, K256[(base) + 15], w[15]);

inline void sha256_compress(thread uint32_t st[8], thread uint32_t w[16]) {
    uint32_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint32_t e = st[4], f = st[5], g = st[6], h = st[7];

    SHA256_16_INIT(w);
    for (uint base = 16u; base < 64u; base += 16u) {
        SHA256_16_EXT(w, base);
    }

    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
}

// Compresses block w[16] from read-only base_st into out[8].
inline void sha256_compress_from(
    const thread uint32_t base_st[8],
    thread uint32_t w[16],
    thread uint32_t out[8]
) {
    uint32_t a = base_st[0], b = base_st[1], c = base_st[2], d = base_st[3];
    uint32_t e = base_st[4], f = base_st[5], g = base_st[6], h = base_st[7];

    SHA256_16_INIT(w);
    for (uint base = 16u; base < 64u; base += 16u) {
        SHA256_16_EXT(w, base);
    }

    out[0] = base_st[0] + a; out[1] = base_st[1] + b;
    out[2] = base_st[2] + c; out[3] = base_st[3] + d;
    out[4] = base_st[4] + e; out[5] = base_st[5] + f;
    out[6] = base_st[6] + g; out[7] = base_st[7] + h;
}

// ============================================================================
// SHA-512 Compression (for N = 24, 32: H and T_len / T_k)
// ============================================================================

constant uint64_t K512[80] = {
    0x428a2f98d728ae22ul, 0x7137449123ef65cdul, 0xb5c0fbcfec4d3b2ful, 0xe9b5dba58189dbbcul,
    0x3956c25bf348b538ul, 0x59f111f1b605d019ul, 0x923f82a4af194f9bul, 0xab1c5ed5da6d8118ul,
    0xd807aa98a3030242ul, 0x12835b0145706fbeul, 0x243185be4ee4b28cul, 0x550c7dc3d5ffb4e2ul,
    0x72be5d74f27b896ful, 0x80deb1fe3b1696b1ul, 0x9bdc06a725c71235ul, 0xc19bf174cf692694ul,
    0xe49b69c19ef14ad2ul, 0xefbe4786384f25e3ul, 0x0fc19dc68b8cd5b5ul, 0x240ca1cc77ac9c65ul,
    0x2de92c6f592b0275ul, 0x4a7484aa6ea6e483ul, 0x5cb0a9dcbd41fbd4ul, 0x76f988da831153b5ul,
    0x983e5152ee66dfabul, 0xa831c66d2db43210ul, 0xb00327c898fb213ful, 0xbf597fc7beef0ee4ul,
    0xc6e00bf33da88fc2ul, 0xd5a79147930aa725ul, 0x06ca6351e003826ful, 0x142929670a0e6e70ul,
    0x27b70a8546d22ffcul, 0x2e1b21385c26c926ul, 0x4d2c6dfc5ac42aedul, 0x53380d139d95b3dful,
    0x650a73548baf63deul, 0x766a0abb3c77b2a8ul, 0x81c2c92e47edaee6ul, 0x92722c851482353bul,
    0xa2bfe8a14cf10364ul, 0xa81a664bbc423001ul, 0xc24b8b70d0f89791ul, 0xc76c51a30654be30ul,
    0xd192e819d6ef5218ul, 0xd69906245565a910ul, 0xf40e35855771202aul, 0x106aa07032bbd1b8ul,
    0x19a4c116b8d2d0c8ul, 0x1e376c085141ab53ul, 0x2748774cdf8eeb99ul, 0x34b0bcb5e19b48a8ul,
    0x391c0cb3c5c95a63ul, 0x4ed8aa4ae3418acbul, 0x5b9cca4f7763e373ul, 0x682e6ff3d6b2b8a3ul,
    0x748f82ee5defb2fcul, 0x78a5636f43172f60ul, 0x84c87814a1f0ab72ul, 0x8cc702081a6439ecul,
    0x90befffa23631e28ul, 0xa4506cebde82bde9ul, 0xbef9a3f7b2c67915ul, 0xc67178f2e372532bul,
    0xca273eceea26619cul, 0xd186b8c721c0c207ul, 0xeada7dd6cde0eb1eul, 0xf57d4f7fee6ed178ul,
    0x06f067aa72176fbaul, 0x0a637dc5a2c898a6ul, 0x113f9804bef90daeul, 0x1b710b35131c471bul,
    0x28db77f523047d84ul, 0x32caab7b40c72493ul, 0x3c9ebe0a15c9bebcul, 0x431d67c49c100d4cul,
    0x4cc5d4becb3e42b6ul, 0x597f299cfc657e2aul, 0x5fcb6fab3ad6faecul, 0x6c44198c4a475817ul
};

inline uint64_t rotr64(uint64_t x, uint64_t n) {
    return (x >> n) | (x << (64ul - n));
}

#define SHA512_R(a, b, c, d, e, f, g, h, k, wi)                                      \
    do {                                                                             \
        uint64_t s1 = rotr64(e, 14ul) ^ rotr64(e, 18ul) ^ rotr64(e, 41ul);           \
        uint64_t ch = g ^ (e & (f ^ g));                                             \
        uint64_t t1 = h + s1 + ch + (k) + (wi);                                      \
        uint64_t s0 = rotr64(a, 28ul) ^ rotr64(a, 34ul) ^ rotr64(a, 39ul);           \
        uint64_t maj = (a & b) | (c & (a | b));                                      \
        d += t1;                                                                     \
        h = t1 + s0 + maj;                                                           \
    } while (0)

#define SHA512_WEXT(w, j)                                                            \
    do {                                                                             \
        uint64_t x = w[((j) + 1) & 15];                                              \
        uint64_t y = w[((j) + 14) & 15];                                             \
        uint64_t ss0 = rotr64(x, 1ul) ^ rotr64(x, 8ul) ^ (x >> 7);                   \
        uint64_t ss1 = rotr64(y, 19ul) ^ rotr64(y, 61ul) ^ (y >> 6);                 \
        w[(j)] = w[(j)] + ss0 + w[((j) + 9) & 15] + ss1;                             \
    } while (0)

#define SHA512_16_INIT(w)                                                            \
    SHA512_R(a, b, c, d, e, f, g, h, K512[ 0], w[ 0]);                               \
    SHA512_R(h, a, b, c, d, e, f, g, K512[ 1], w[ 1]);                               \
    SHA512_R(g, h, a, b, c, d, e, f, K512[ 2], w[ 2]);                               \
    SHA512_R(f, g, h, a, b, c, d, e, K512[ 3], w[ 3]);                               \
    SHA512_R(e, f, g, h, a, b, c, d, K512[ 4], w[ 4]);                               \
    SHA512_R(d, e, f, g, h, a, b, c, K512[ 5], w[ 5]);                               \
    SHA512_R(c, d, e, f, g, h, a, b, K512[ 6], w[ 6]);                               \
    SHA512_R(b, c, d, e, f, g, h, a, K512[ 7], w[ 7]);                               \
    SHA512_R(a, b, c, d, e, f, g, h, K512[ 8], w[ 8]);                               \
    SHA512_R(h, a, b, c, d, e, f, g, K512[ 9], w[ 9]);                               \
    SHA512_R(g, h, a, b, c, d, e, f, K512[10], w[10]);                               \
    SHA512_R(f, g, h, a, b, c, d, e, K512[11], w[11]);                               \
    SHA512_R(e, f, g, h, a, b, c, d, K512[12], w[12]);                               \
    SHA512_R(d, e, f, g, h, a, b, c, K512[13], w[13]);                               \
    SHA512_R(c, d, e, f, g, h, a, b, K512[14], w[14]);                               \
    SHA512_R(b, c, d, e, f, g, h, a, K512[15], w[15]);

#define SHA512_16_EXT(w, base)                                                       \
    SHA512_WEXT(w,  0); SHA512_R(a, b, c, d, e, f, g, h, K512[(base) +  0], w[ 0]);  \
    SHA512_WEXT(w,  1); SHA512_R(h, a, b, c, d, e, f, g, K512[(base) +  1], w[ 1]);  \
    SHA512_WEXT(w,  2); SHA512_R(g, h, a, b, c, d, e, f, K512[(base) +  2], w[ 2]);  \
    SHA512_WEXT(w,  3); SHA512_R(f, g, h, a, b, c, d, e, K512[(base) +  3], w[ 3]);  \
    SHA512_WEXT(w,  4); SHA512_R(e, f, g, h, a, b, c, d, K512[(base) +  4], w[ 4]);  \
    SHA512_WEXT(w,  5); SHA512_R(d, e, f, g, h, a, b, c, K512[(base) +  5], w[ 5]);  \
    SHA512_WEXT(w,  6); SHA512_R(c, d, e, f, g, h, a, b, K512[(base) +  6], w[ 6]);  \
    SHA512_WEXT(w,  7); SHA512_R(b, c, d, e, f, g, h, a, K512[(base) +  7], w[ 7]);  \
    SHA512_WEXT(w,  8); SHA512_R(a, b, c, d, e, f, g, h, K512[(base) +  8], w[ 8]);  \
    SHA512_WEXT(w,  9); SHA512_R(h, a, b, c, d, e, f, g, K512[(base) +  9], w[ 9]);  \
    SHA512_WEXT(w, 10); SHA512_R(g, h, a, b, c, d, e, f, K512[(base) + 10], w[10]);  \
    SHA512_WEXT(w, 11); SHA512_R(f, g, h, a, b, c, d, e, K512[(base) + 11], w[11]);  \
    SHA512_WEXT(w, 12); SHA512_R(e, f, g, h, a, b, c, d, K512[(base) + 12], w[12]);  \
    SHA512_WEXT(w, 13); SHA512_R(d, e, f, g, h, a, b, c, K512[(base) + 13], w[13]);  \
    SHA512_WEXT(w, 14); SHA512_R(c, d, e, f, g, h, a, b, K512[(base) + 14], w[14]);  \
    SHA512_WEXT(w, 15); SHA512_R(b, c, d, e, f, g, h, a, K512[(base) + 15], w[15]);

inline void sha512_compress(thread uint64_t st[8], thread uint64_t w[16]) {
    uint64_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint64_t e = st[4], f = st[5], g = st[6], h = st[7];

    SHA512_16_INIT(w);
    for (uint base = 16u; base < 80u; base += 16u) {
        SHA512_16_EXT(w, base);
    }

    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
}

// ============================================================================
// Helpers: Byte Packing, ADRSc Word Building, Short/Pair/Stream Tweakable Hash
// ============================================================================

inline void store_be32(device uint8_t *dst, uint32_t v) {
    dst[0] = uint8_t(v >> 24);
    dst[1] = uint8_t(v >> 16);
    dst[2] = uint8_t(v >> 8);
    dst[3] = uint8_t(v);
}

template <uint NW>
inline void write_node_bytes(device uint8_t *dst, const thread uint32_t node[NW]) {
    for (uint i = 0; i < NW; ++i) {
        store_be32(dst + 4u * i, node[i]);
    }
}

template <uint NW>
inline void write_node_bytes_tg(device uint8_t *dst, const threadgroup uint32_t *node) {
    for (uint i = 0; i < NW; ++i) {
        store_be32(dst + 4u * i, node[i]);
    }
}

// Builds ADRSc prefix words W[0..4] + carry16 (top 16 bits = word3 & 0xFFFF).
inline void adrs_to_w256(
    uint32_t layer,
    uint64_t tree,
    uint32_t typ,
    uint32_t keypair,
    uint32_t word2,
    uint32_t word3,
    thread uint32_t &w0,
    thread uint32_t &w1,
    thread uint32_t &w2,
    thread uint32_t &w3,
    thread uint32_t &w4,
    thread uint32_t &w5_hi
) {
    uint32_t tree_hi = uint32_t(tree >> 32);
    uint32_t tree_lo = uint32_t(tree);
    w0 = ((layer & 0xFFu) << 24) | (tree_hi >> 8);
    w1 = (tree_hi << 24) | (tree_lo >> 8);
    w2 = ((tree_lo & 0xFFu) << 24) | ((typ & 0xFFu) << 16) | (keypair >> 16);
    w3 = (keypair << 16) | (word2 >> 16);
    w4 = (word2 << 16) | (word3 >> 16);
    w5_hi = (word3 << 16);
}

// Single-block SHA-256 tweakable hash (F or PRF) for N = 4 * NW (NW = 4, 6, 8).
template <uint NW>
inline void thash_short_words(
    const thread uint32_t seed_st[8],
    uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3, uint32_t w4, uint32_t w5_hi,
    const thread uint32_t in_val[NW],
    thread uint32_t out_val[NW]
) {
    uint32_t w[16];
    w[0] = w0;
    w[1] = w1;
    w[2] = w2;
    w[3] = w3;
    w[4] = w4;
    w[5] = w5_hi | (in_val[0] >> 16);
    for (uint i = 0; i < NW - 1; ++i) {
        w[6 + i] = (in_val[i] << 16) | (in_val[i + 1] >> 16);
    }
    w[5 + NW] = (in_val[NW - 1] << 16) | 0x00008000u;
    for (uint i = 6 + NW; i < 15; ++i) {
        w[i] = 0u;
    }
    w[15] = (86u + 4u * NW) * 8u;

    uint32_t st[8];
    sha256_compress_from(seed_st, w, st);
    for (uint i = 0; i < NW; ++i) {
        out_val[i] = st[i];
    }
}

// Pair hash H(PK.seed, ADRS, left || right): SHA-256 for NW=4 (N=16), SHA-512 for NW=6,8 (N=24,32).
template <uint NW>
inline void thash_pair_words(
    const device KeyMaterial &km,
    uint32_t layer,
    uint64_t tree,
    uint32_t typ,
    uint32_t keypair,
    uint32_t height,
    uint32_t index,
    const thread uint32_t left[NW],
    const thread uint32_t right[NW],
    thread uint32_t out[NW]
) {
    if (NW == 4) {
        uint32_t seed_st[8];
        for (uint i = 0; i < 8; ++i) seed_st[i] = km.state256[i];
        uint32_t w[16];
        uint32_t w5_hi;
        adrs_to_w256(layer, tree, typ, keypair, height, index, w[0], w[1], w[2], w[3], w[4], w5_hi);
        w[5]  = w5_hi | (left[0] >> 16);
        w[6]  = (left[0] << 16) | (left[1] >> 16);
        w[7]  = (left[1] << 16) | (left[2] >> 16);
        w[8]  = (left[2] << 16) | (left[3] >> 16);
        w[9]  = (left[3] << 16) | (right[0] >> 16);
        w[10] = (right[0] << 16) | (right[1] >> 16);
        w[11] = (right[1] << 16) | (right[2] >> 16);
        w[12] = (right[2] << 16) | (right[3] >> 16);
        w[13] = (right[3] << 16) | 0x00008000u;
        w[14] = 0u;
        w[15] = (86u + 32u) * 8u;
        uint32_t st[8];
        sha256_compress_from(seed_st, w, st);
        for (uint i = 0; i < NW; ++i) out[i] = st[i];
    } else {
        uint64_t st[8];
        for (uint i = 0; i < 8; ++i) st[i] = km.state512[i];
        uint64_t w[16];
        w[0] = (uint64_t(layer & 0xFFu) << 56) | (tree >> 8);
        w[1] = ((tree & 0xFFul) << 56) | (uint64_t(typ & 0xFFu) << 48) |
               (uint64_t(keypair) << 16) | (uint64_t(height) >> 16);
        uint64_t carry = (uint64_t(height & 0xFFFFu) << 48) | (uint64_t(index) << 16);
        uint idx = 2;
        for (uint i = 0; i < NW / 2; ++i) {
            uint64_t v = (uint64_t(left[2 * i]) << 32) | uint64_t(left[2 * i + 1]);
            w[idx++] = carry | (v >> 48);
            carry = v << 16;
        }
        for (uint i = 0; i < NW / 2; ++i) {
            uint64_t v = (uint64_t(right[2 * i]) << 32) | uint64_t(right[2 * i + 1]);
            w[idx++] = carry | (v >> 48);
            carry = v << 16;
        }
        w[idx++] = carry | 0x00008000ul;
        while (idx < 15) {
            w[idx++] = 0ul;
        }
        w[15] = uint64_t((150u + 8u * NW) * 8u);
        sha512_compress(st, w);
        for (uint i = 0; i < NW / 2; ++i) {
            out[2 * i]     = uint32_t(st[i] >> 32);
            out[2 * i + 1] = uint32_t(st[i]);
        }
    }
}

// Streaming T_l (WOTS_PK or FORS_ROOTS) for SHA-256 (NW == 4)
struct TlenStream256 {
    uint32_t st[8];
    uint32_t blk[16];
    uint32_t carry;
    uint32_t w_idx;
    uint32_t total_bits;

    void init(const thread uint32_t seed_st[8], uint32_t layer, uint64_t tree,
              uint32_t typ, uint32_t keypair, uint32_t count_nodes) {
        for (uint i = 0; i < 8; ++i) st[i] = seed_st[i];
        adrs_to_w256(layer, tree, typ, keypair, 0u, 0u,
                     blk[0], blk[1], blk[2], blk[3], blk[4], carry);
        w_idx = 5u;
        total_bits = (64u + 22u + count_nodes * 16u) * 8u;
    }

    inline void push_word(uint32_t v) {
        blk[w_idx++] = carry | (v >> 16);
        carry = v << 16;
        if (w_idx == 16u) {
            sha256_compress(st, blk);
            w_idx = 0u;
        }
    }

    void finish(thread uint32_t out[4]) {
        blk[w_idx++] = carry | 0x00008000u;
        if (w_idx == 16u) {
            sha256_compress(st, blk);
            w_idx = 0u;
        }
        if (w_idx > 14u) {
            while (w_idx < 16u) blk[w_idx++] = 0u;
            sha256_compress(st, blk);
            w_idx = 0u;
        }
        while (w_idx < 14u) blk[w_idx++] = 0u;
        blk[14] = 0u;
        blk[15] = total_bits;
        sha256_compress(st, blk);
        for (uint i = 0; i < 4; ++i) out[i] = st[i];
    }
};

// Streaming T_l (WOTS_PK or FORS_ROOTS) for SHA-512 (NW == 6 or 8)
struct TlenStream512 {
    uint64_t st[8];
    uint64_t blk[16];
    uint64_t carry;
    uint32_t w_idx;
    uint64_t total_bits;

    void init(const device uint64_t seed_st[8], uint32_t layer, uint64_t tree,
              uint32_t typ, uint32_t keypair, uint32_t count_nodes, uint32_t n_bytes) {
        for (uint i = 0; i < 8; ++i) st[i] = seed_st[i];
        blk[0] = (uint64_t(layer & 0xFFu) << 56) | (tree >> 8);
        blk[1] = ((tree & 0xFFul) << 56) | (uint64_t(typ & 0xFFu) << 48) |
                 (uint64_t(keypair) << 16);
        carry = 0ul;
        w_idx = 2u;
        total_bits = uint64_t(128u + 22u + count_nodes * n_bytes) * 8ul;
    }

    inline void push_word64(uint64_t v) {
        blk[w_idx++] = carry | (v >> 48);
        carry = v << 16;
        if (w_idx == 16u) {
            sha512_compress(st, blk);
            w_idx = 0u;
        }
    }

    template <uint NW>
    void finish(thread uint32_t out[NW]) {
        blk[w_idx++] = carry | 0x00008000ul;
        if (w_idx == 16u) {
            sha512_compress(st, blk);
            w_idx = 0u;
        }
        if (w_idx > 14u) {
            while (w_idx < 16u) blk[w_idx++] = 0ul;
            sha512_compress(st, blk);
            w_idx = 0u;
        }
        while (w_idx < 14u) blk[w_idx++] = 0ul;
        blk[14] = 0ul;
        blk[15] = total_bits;
        sha512_compress(st, blk);
        for (uint i = 0; i < NW / 2; ++i) {
            out[2 * i]     = uint32_t(st[i] >> 32);
            out[2 * i + 1] = uint32_t(st[i]);
        }
    }
};

// Runs one WOTS+ chain: PRF + `steps` iterations of F.
template <uint NW>
inline void run_wots_chain(
    const thread uint32_t seed_st[8],
    const thread uint32_t sk_seed[NW],
    uint32_t layer,
    uint64_t tree,
    uint32_t keypair,
    uint32_t chain,
    uint32_t steps,
    thread uint32_t val[NW]
) {
    uint32_t w0, w1, w2, w3, w4, w5_hi;
    // PRF: typ = WOTS_PRF, word2 = chain, word3 = 0
    adrs_to_w256(layer, tree, ADRS_WOTS_PRF, keypair, chain, 0u, w0, w1, w2, w3, w4, w5_hi);
    thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4, 0u, sk_seed, val);
    if (steps == 0u) {
        return;
    }

    // Switch type from WOTS_PRF (5) to WOTS_HASH (0): clear byte 9 (bits 16..23 of w2)
    w2 &= 0xFF00FFFFu;
    for (uint32_t s = 0u; s < steps; ++s) {
        thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4, s << 16, val, val);
    }
}

// ============================================================================
// Kernel 1: wots_chains (1 thread per WOTS+ chain: massive GPU parallelism!)
// ============================================================================

template <uint NW>
inline void wots_chains_impl(
    const device KeyMaterial *keys,
    const device XmssTreeDesc *trees,
    device uint32_t *out_chain_tips,
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
    uint32_t seed_st[8];
    uint32_t sk_seed[NW];
    for (uint i = 0; i < 8; ++i) seed_st[i] = keys[desc.key_idx].state256[i];
    for (uint i = 0; i < NW; ++i) sk_seed[i] = keys[desc.key_idx].sk_seed[i];

    uint32_t tip[NW];
    run_wots_chain<NW>(seed_st, sk_seed, desc.layer, desc.tree, leaf_idx, chain, 15u, tip);

    uint32_t out_off = gid * NW;
    for (uint i = 0; i < NW; ++i) {
        out_chain_tips[out_off + i] = tip[i];
    }
}

// ============================================================================
// Kernel 2: wots_tlen (1 thread per WOTS+ leaf, compresses chain tips -> leaf)
// ============================================================================

template <uint NW>
inline void wots_tlen_impl(
    const device KeyMaterial *keys,
    const device XmssTreeDesc *trees,
    const device uint32_t *chain_tips,
    device uint32_t *out_leaves,
    constant XmssParams &p,
    uint32_t gid
) {
    uint32_t total_leaves = p.num_trees * p.leaves_per_tree;
    if (gid >= total_leaves) return;

    uint32_t leaf_idx = gid % p.leaves_per_tree;
    uint32_t tree_idx = gid / p.leaves_per_tree;
    XmssTreeDesc desc = trees[tree_idx];
    uint32_t tip_base = gid * p.wots_len * NW;

    uint32_t leaf[NW];
    if (NW == 4) {
        uint32_t seed_st[8];
        for (uint i = 0; i < 8; ++i) seed_st[i] = keys[desc.key_idx].state256[i];
        TlenStream256 s;
        s.init(seed_st, desc.layer, desc.tree, ADRS_WOTS_PK, leaf_idx, p.wots_len);
        for (uint32_t c = 0; c < p.wots_len; ++c) {
            uint32_t off = tip_base + c * 4u;
            s.push_word(chain_tips[off]);
            s.push_word(chain_tips[off + 1u]);
            s.push_word(chain_tips[off + 2u]);
            s.push_word(chain_tips[off + 3u]);
        }
        uint32_t out4[4];
        s.finish(out4);
        for (uint i = 0; i < 4u; ++i) leaf[i] = out4[i];
    } else {
        TlenStream512 s;
        s.init(keys[desc.key_idx].state512, desc.layer, desc.tree, ADRS_WOTS_PK,
               leaf_idx, p.wots_len, NW * 4u);
        for (uint32_t c = 0; c < p.wots_len; ++c) {
            uint32_t off = tip_base + c * NW;
            for (uint i = 0; i < NW / 2; ++i) {
                uint64_t v = (uint64_t(chain_tips[off + 2 * i]) << 32) |
                              uint64_t(chain_tips[off + 2 * i + 1]);
                s.push_word64(v);
            }
        }
        s.finish<NW>(leaf);
    }

    uint32_t out_off = gid * NW;
    for (uint i = 0; i < NW; ++i) {
        out_leaves[out_off + i] = leaf[i];
    }
}

// ============================================================================
// Kernel 3: xmss_leaves_streaming (1 thread per WOTS+ leaf, zero temp buffer!)
// ============================================================================

template <uint NW>
inline void xmss_leaves_streaming_impl(
    const device KeyMaterial *keys,
    const device XmssTreeDesc *trees,
    device uint32_t *out_leaves,
    constant XmssParams &p,
    uint32_t gid
) {
    uint32_t total_leaves = p.num_trees * p.leaves_per_tree;
    if (gid >= total_leaves) return;

    uint32_t leaf_idx = gid % p.leaves_per_tree;
    uint32_t tree_idx = gid / p.leaves_per_tree;
    XmssTreeDesc desc = trees[tree_idx];

    uint32_t seed_st[8];
    uint32_t sk_seed[NW];
    for (uint i = 0; i < 8; ++i) seed_st[i] = keys[desc.key_idx].state256[i];
    for (uint i = 0; i < NW; ++i) sk_seed[i] = keys[desc.key_idx].sk_seed[i];

    uint32_t leaf[NW];
    if (NW == 4) {
        TlenStream256 s;
        s.init(seed_st, desc.layer, desc.tree, ADRS_WOTS_PK, leaf_idx, p.wots_len);
        for (uint32_t c = 0; c < p.wots_len; ++c) {
            uint32_t tip[NW];
            run_wots_chain<NW>(seed_st, sk_seed, desc.layer, desc.tree, leaf_idx, c, 15u, tip);
            s.push_word(tip[0]);
            s.push_word(tip[1]);
            s.push_word(tip[2]);
            s.push_word(tip[3]);
        }
        uint32_t out4[4];
        s.finish(out4);
        for (uint i = 0; i < 4u; ++i) leaf[i] = out4[i];
    } else {
        TlenStream512 s;
        s.init(keys[desc.key_idx].state512, desc.layer, desc.tree, ADRS_WOTS_PK,
               leaf_idx, p.wots_len, NW * 4u);
        for (uint32_t c = 0; c < p.wots_len; ++c) {
            uint32_t tip[NW];
            run_wots_chain<NW>(seed_st, sk_seed, desc.layer, desc.tree, leaf_idx, c, 15u, tip);
            for (uint i = 0; i < NW / 2; ++i) {
                uint64_t v = (uint64_t(tip[2 * i]) << 32) | uint64_t(tip[2 * i + 1]);
                s.push_word64(v);
            }
        }
        s.finish<NW>(leaf);
    }

    uint32_t out_off = gid * NW;
    for (uint i = 0; i < NW; ++i) {
        out_leaves[out_off + i] = leaf[i];
    }
}

// ============================================================================
// Kernel 4: xmss_reduce (1 threadgroup of 2^(hp-1) threads per XMSS tree)
// ============================================================================

template <uint NW>
inline void xmss_reduce_impl(
    const device KeyMaterial *keys,
    const device XmssTreeDesc *trees,
    const device uint32_t *leaves,
    device uint32_t *out_roots,
    device uint8_t *out_sigs,
    constant XmssParams &p,
    threadgroup uint32_t *tg_nodes,
    uint32_t tg_id,
    uint32_t tid
) {
    if (tg_id >= p.num_trees) return;

    XmssTreeDesc desc = trees[tg_id];
    const device KeyMaterial &km = keys[desc.key_idx];
    uint32_t leaf_base = tg_id * p.leaves_per_tree;
    uint32_t half_leaves = p.leaves_per_tree >> 1;
    bool has_auth = (desc.target_leaf != 0xFFFFFFFFu);

    // Level 0 authentication sibling (from global leaves)
    if (has_auth && tid == 0u) {
        uint32_t sib0 = desc.target_leaf ^ 1u;
        uint32_t sib_off = (leaf_base + sib0) * NW;
        uint32_t node[NW];
        for (uint i = 0; i < NW; ++i) node[i] = leaves[sib_off + i];
        write_node_bytes<NW>(out_sigs + desc.auth_byte_off, node);
    }

    // Level 1: hash pairs of leaves directly into tg_nodes[0..half_leaves-1]
    {
        uint32_t left[NW], right[NW], parent[NW];
        uint32_t l_off = (leaf_base + 2u * tid) * NW;
        uint32_t r_off = (leaf_base + 2u * tid + 1u) * NW;
        for (uint i = 0; i < NW; ++i) {
            left[i] = leaves[l_off + i];
            right[i] = leaves[r_off + i];
        }
        thash_pair_words<NW>(km, desc.layer, desc.tree, ADRS_TREE, 0u, 1u, tid, left, right, parent);
        for (uint i = 0; i < NW; ++i) {
            tg_nodes[tid * NW + i] = parent[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Levels 2..=hp
    uint32_t cur_cnt = half_leaves >> 1;
    for (uint32_t lvl = 2u; lvl <= p.hp; ++lvl) {
        if (has_auth) {
            uint32_t sib = (desc.target_leaf >> (lvl - 1u)) ^ 1u;
            if (tid == sib) {
                write_node_bytes_tg<NW>(out_sigs + desc.auth_byte_off + (lvl - 1u) * NW * 4u,
                                        tg_nodes + tid * NW);
            }
        }
        uint32_t parent[NW];
        if (tid < cur_cnt) {
            uint32_t left[NW], right[NW];
            for (uint i = 0; i < NW; ++i) {
                left[i] = tg_nodes[(2u * tid) * NW + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NW + i];
            }
            thash_pair_words<NW>(km, desc.layer, desc.tree, ADRS_TREE, 0u, lvl, tid, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NW; ++i) {
                tg_nodes[tid * NW + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        cur_cnt >>= 1;
    }

    if (tid == 0u) {
        uint32_t out_off = tg_id * NW;
        for (uint i = 0; i < NW; ++i) {
            out_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// Kernel 5: fors_pass1 (1 threadgroup of 2^(s1-1) threads per height-s1 FORS subtree)
// Each thread computes 2 adjacent leaves AND their level-1 parent in registers!
// ============================================================================

template <uint NW>
inline void fors_pass1_impl(
    const device KeyMaterial *keys,
    const device ForsJobDesc *jobs,
    device uint32_t *out_sub_roots,
    device uint8_t *out_sigs,
    constant ForsParams &p,
    threadgroup uint32_t *tg_nodes,
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
    const device KeyMaterial &km = keys[job.key_idx];

    uint32_t seed_st[8];
    uint32_t sk_seed[NW];
    for (uint i = 0; i < 8; ++i) seed_st[i] = km.state256[i];
    for (uint i = 0; i < NW; ++i) sk_seed[i] = km.sk_seed[i];

    uint32_t leaf0_in_tree = (st_local << p.s1) + (2u * tid);
    uint32_t leaf1_in_tree = leaf0_in_tree + 1u;
    uint32_t leaf0_word3 = (tree_i << p.a) + leaf0_in_tree;
    uint32_t leaf1_word3 = leaf0_word3 + 1u;
    uint32_t target = job.indices[tree_i];
    uint32_t n_bytes = NW * 4u;
    uint32_t fors_tree_sig_off = job.sig_byte_off + n_bytes + tree_i * (1u + p.a) * n_bytes;

    // Left leaf (2*tid): PRF then F
    uint32_t w0, w1, w2, w3, w4, w5_hi;
    adrs_to_w256(0u, job.idx_tree, ADRS_FORS_PRF, job.idx_leaf, 0u, leaf0_word3,
                 w0, w1, w2, w3, w4, w5_hi);
    uint32_t sk0[NW], leaf0[NW];
    thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4, w5_hi, sk_seed, sk0);
    uint32_t w2_tree = (w2 & 0xFF00FFFFu) | (ADRS_FORS_TREE << 16);
    thash_short_words<NW>(seed_st, w0, w1, w2_tree, w3, w4, w5_hi, sk0, leaf0);

    // Right leaf (2*tid + 1): PRF then F (only word3 increments by 1)
    uint32_t w4_r = leaf1_word3 >> 16;
    uint32_t w5_r = leaf1_word3 << 16;
    uint32_t sk1[NW], leaf1[NW];
    thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4_r, w5_r, sk_seed, sk1);
    thash_short_words<NW>(seed_st, w0, w1, w2_tree, w3, w4_r, w5_r, sk1, leaf1);

    // Level 0 secret & authentication sibling (no barrier needed!)
    if (leaf0_in_tree == target) {
        write_node_bytes<NW>(out_sigs + fors_tree_sig_off, sk0);
        write_node_bytes<NW>(out_sigs + fors_tree_sig_off + n_bytes, leaf1);
    } else if (leaf1_in_tree == target) {
        write_node_bytes<NW>(out_sigs + fors_tree_sig_off, sk1);
        write_node_bytes<NW>(out_sigs + fors_tree_sig_off + n_bytes, leaf0);
    }

    // Level 1 parent hash: 100% of threads active!
    {
        uint32_t parent1[NW];
        uint32_t node1_word3 = (tree_i << (p.a - 1u)) + (st_local << (p.s1 - 1u)) + tid;
        thash_pair_words<NW>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                             1u, node1_word3, leaf0, leaf1, parent1);
        for (uint i = 0; i < NW; ++i) {
            tg_nodes[tid * NW + i] = parent1[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    bool in_subtree = ((target >> p.s1) == st_local);

    // Reduce remaining levels 2..=s1 inside threadgroup memory
    for (uint32_t lvl = 2u; lvl <= p.s1; ++lvl) {
        uint32_t cur_cnt = 1u << (p.s1 - lvl);
        if (in_subtree) {
            uint32_t sib_in_tree = (target >> (lvl - 1u)) ^ 1u;
            uint32_t mask = (1u << (p.s1 - lvl + 1u)) - 1u;
            uint32_t sib_local = sib_in_tree & mask;
            if (tid == sib_local) {
                write_node_bytes_tg<NW>(out_sigs + fors_tree_sig_off + lvl * n_bytes,
                                        tg_nodes + tid * NW);
            }
        }
        uint32_t parent[NW];
        if (tid < cur_cnt) {
            uint32_t left[NW], right[NW];
            for (uint i = 0; i < NW; ++i) {
                left[i] = tg_nodes[(2u * tid) * NW + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NW + i];
            }
            uint32_t node_word3 = (tree_i << (p.a - lvl)) + (st_local << (p.s1 - lvl)) + tid;
            thash_pair_words<NW>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                                 lvl, node_word3, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NW; ++i) {
                tg_nodes[tid * NW + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0u) {
        uint32_t out_off = ((sig_idx * p.k + tree_i) * p.subtrees_per_tree + st_local) * NW;
        for (uint i = 0; i < NW; ++i) {
            out_sub_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// Kernel 6: fors_pass2 (1 threadgroup of 2^(s2-1) threads per FORS tree, s2 > 0)
// ============================================================================

template <uint NW>
inline void fors_pass2_impl(
    const device KeyMaterial *keys,
    const device ForsJobDesc *jobs,
    const device uint32_t *in_sub_roots,
    device uint32_t *out_fors_roots,
    device uint8_t *out_sigs,
    constant ForsParams &p,
    threadgroup uint32_t *tg_nodes,
    uint32_t tg_id,
    uint32_t tid
) {
    uint32_t total_trees = p.num_sigs * p.k;
    if (tg_id >= total_trees) return;

    uint32_t tree_i = tg_id % p.k;
    uint32_t sig_idx = tg_id / p.k;
    const device ForsJobDesc &job = jobs[sig_idx];
    const device KeyMaterial &km = keys[job.key_idx];

    uint32_t target = job.indices[tree_i];
    uint32_t n_bytes = NW * 4u;
    uint32_t fors_tree_sig_off = job.sig_byte_off + n_bytes + tree_i * (1u + p.a) * n_bytes;

    // Step 1 (lvl = s1 + 1): each thread reads 2 sub-roots and hashes directly into tg_nodes[tid]
    {
        uint32_t l_off = (tg_id * p.subtrees_per_tree + 2u * tid) * NW;
        uint32_t r_off = l_off + NW;
        uint32_t left[NW], right[NW], parent1[NW];
        for (uint i = 0; i < NW; ++i) {
            left[i] = in_sub_roots[l_off + i];
            right[i] = in_sub_roots[r_off + i];
        }
        uint32_t lvl1 = p.s1 + 1u;
        uint32_t sib1 = (target >> p.s1) ^ 1u;
        if (2u * tid == sib1) {
            write_node_bytes<NW>(out_sigs + fors_tree_sig_off + lvl1 * n_bytes, left);
        } else if (2u * tid + 1u == sib1) {
            write_node_bytes<NW>(out_sigs + fors_tree_sig_off + lvl1 * n_bytes, right);
        }
        uint32_t node1_word3 = (tree_i << (p.a - lvl1)) + tid;
        thash_pair_words<NW>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                             lvl1, node1_word3, left, right, parent1);
        for (uint i = 0; i < NW; ++i) {
            tg_nodes[tid * NW + i] = parent1[i];
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint32_t step = 2u; step <= p.s2; ++step) {
        uint32_t lvl = p.s1 + step;
        uint32_t cur_cnt = 1u << (p.s2 - step);
        uint32_t sib = (target >> (lvl - 1u)) ^ 1u;
        if (tid == sib) {
            write_node_bytes_tg<NW>(out_sigs + fors_tree_sig_off + lvl * n_bytes,
                                    tg_nodes + tid * NW);
        }
        uint32_t parent[NW];
        if (tid < cur_cnt) {
            uint32_t left[NW], right[NW];
            for (uint i = 0; i < NW; ++i) {
                left[i] = tg_nodes[(2u * tid) * NW + i];
                right[i] = tg_nodes[(2u * tid + 1u) * NW + i];
            }
            uint32_t node_word3 = (tree_i << (p.a - lvl)) + tid;
            thash_pair_words<NW>(km, 0u, job.idx_tree, ADRS_FORS_TREE, job.idx_leaf,
                                 lvl, node_word3, left, right, parent);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < cur_cnt) {
            for (uint i = 0; i < NW; ++i) {
                tg_nodes[tid * NW + i] = parent[i];
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0u) {
        uint32_t out_off = tg_id * NW;
        for (uint i = 0; i < NW; ++i) {
            out_fors_roots[out_off + i] = tg_nodes[i];
        }
    }
}

// ============================================================================
// Kernel 7: fors_pk (1 thread per signature: T_k over k FORS tree roots)
// ============================================================================

template <uint NW>
inline void fors_pk_impl(
    const device KeyMaterial *keys,
    const device ForsJobDesc *jobs,
    const device uint32_t *fors_roots,
    device uint32_t *out_pk_fors,
    constant ForsParams &p,
    uint32_t sig_idx
) {
    if (sig_idx >= p.num_sigs) return;

    const device ForsJobDesc &job = jobs[sig_idx];
    const device KeyMaterial &km = keys[job.key_idx];
    uint32_t root_base = sig_idx * p.k * NW;

    uint32_t pk[NW];
    if (NW == 4) {
        uint32_t seed_st[8];
        for (uint i = 0; i < 8; ++i) seed_st[i] = km.state256[i];
        TlenStream256 s;
        s.init(seed_st, 0u, job.idx_tree, ADRS_FORS_ROOTS, job.idx_leaf, p.k);
        for (uint32_t i = 0; i < p.k; ++i) {
            uint32_t off = root_base + i * 4u;
            s.push_word(fors_roots[off]);
            s.push_word(fors_roots[off + 1u]);
            s.push_word(fors_roots[off + 2u]);
            s.push_word(fors_roots[off + 3u]);
        }
        uint32_t out4[4];
        s.finish(out4);
        for (uint i = 0; i < 4u; ++i) pk[i] = out4[i];
    } else {
        TlenStream512 s;
        s.init(km.state512, 0u, job.idx_tree, ADRS_FORS_ROOTS, job.idx_leaf, p.k, NW * 4u);
        for (uint32_t i = 0; i < p.k; ++i) {
            uint32_t off = root_base + i * NW;
            for (uint j = 0; j < NW / 2; ++j) {
                uint64_t v = (uint64_t(fors_roots[off + 2 * j]) << 32) |
                              uint64_t(fors_roots[off + 2 * j + 1]);
                s.push_word64(v);
            }
        }
        s.finish<NW>(pk);
    }

    uint32_t out_off = sig_idx * NW;
    for (uint i = 0; i < NW; ++i) {
        out_pk_fors[out_off + i] = pk[i];
    }
}

// ============================================================================
// Kernel 8: wots_sign (1 thread per WOTS+ chain across all B * d layers!)
// ============================================================================

template <uint NW>
inline uint32_t wots_digit_at(const thread uint32_t msg[NW], uint32_t chain) {
    uint32_t len1 = 8u * NW; // 2 * N = 8 * (N / 4)
    if (chain < len1) {
        uint32_t w = msg[chain >> 3];
        uint32_t nib = chain & 7u;
        return (w >> (28u - 4u * nib)) & 0xFu;
    }
    uint32_t csum = 0u;
    for (uint i = 0; i < NW; ++i) {
        uint32_t w = msg[i];
        csum += 15u - ((w >> 28) & 0xFu);
        csum += 15u - ((w >> 24) & 0xFu);
        csum += 15u - ((w >> 20) & 0xFu);
        csum += 15u - ((w >> 16) & 0xFu);
        csum += 15u - ((w >> 12) & 0xFu);
        csum += 15u - ((w >>  8) & 0xFu);
        csum += 15u - ((w >>  4) & 0xFu);
        csum += 15u - ( w        & 0xFu);
    }
    uint32_t c_idx = chain - len1; // 0, 1, or 2
    return (csum >> (8u - 4u * c_idx)) & 0xFu;
}

template <uint NW>
inline void wots_sign_impl(
    const device KeyMaterial *keys,
    const device WotsSignLayerDesc *layers,
    const device uint32_t *pk_fors,
    const device uint32_t *xmss_roots,
    device uint8_t *out_sigs,
    constant WotsSignParams &p,
    uint32_t gid
) {
    uint32_t total_chains = p.num_layers * p.wots_len;
    if (gid >= total_chains) return;

    uint32_t chain = gid % p.wots_len;
    uint32_t layer_global = gid / p.wots_len;
    WotsSignLayerDesc desc = layers[layer_global];
    const device KeyMaterial &km = keys[desc.key_idx];

    uint32_t msg[NW];
    if (desc.layer == 0u) {
        uint32_t off = desc.sig_idx * NW;
        for (uint i = 0; i < NW; ++i) msg[i] = pk_fors[off + i];
    } else {
        uint32_t off = (desc.sig_idx * p.d + (desc.layer - 1u)) * NW;
        for (uint i = 0; i < NW; ++i) msg[i] = xmss_roots[off + i];
    }

    uint32_t steps = wots_digit_at<NW>(msg, chain);

    uint32_t seed_st[8];
    uint32_t sk_seed[NW];
    for (uint i = 0; i < 8; ++i) seed_st[i] = km.state256[i];
    for (uint i = 0; i < NW; ++i) sk_seed[i] = km.sk_seed[i];

    uint32_t sig_val[NW];
    run_wots_chain<NW>(seed_st, sk_seed, desc.layer, desc.tree, desc.keypair, chain, steps, sig_val);

    write_node_bytes<NW>(out_sigs + desc.wots_byte_off + chain * NW * 4u, sig_val);
}

// ============================================================================
// Concrete Kernel Entry Points for N = 16 (NW=4), N = 24 (NW=6), N = 32 (NW=8)
// ============================================================================

#define DEFINE_KERNELS(SUFFIX, NW)                                                   \
kernel void wots_chains_##SUFFIX(                                                    \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    device uint32_t *out_chain_tips [[buffer(2)]],                                   \
    constant XmssParams &p [[buffer(3)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    wots_chains_impl<NW>(keys, trees, out_chain_tips, p, gid);                       \
}                                                                                    \
                                                                                     \
kernel void wots_tlen_##SUFFIX(                                                      \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    const device uint32_t *chain_tips [[buffer(2)]],                                 \
    device uint32_t *out_leaves [[buffer(3)]],                                       \
    constant XmssParams &p [[buffer(4)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    wots_tlen_impl<NW>(keys, trees, chain_tips, out_leaves, p, gid);                 \
}                                                                                    \
                                                                                     \
kernel void xmss_leaves_streaming_##SUFFIX(                                          \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    device uint32_t *out_leaves [[buffer(2)]],                                       \
    constant XmssParams &p [[buffer(3)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    xmss_leaves_streaming_impl<NW>(keys, trees, out_leaves, p, gid);                 \
}                                                                                    \
                                                                                     \
kernel void xmss_reduce_##SUFFIX(                                                    \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device XmssTreeDesc *trees [[buffer(1)]],                                  \
    const device uint32_t *leaves [[buffer(2)]],                                     \
    device uint32_t *out_roots [[buffer(3)]],                                        \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant XmssParams &p [[buffer(5)]],                                            \
    threadgroup uint32_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    xmss_reduce_impl<NW>(keys, trees, leaves, out_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void fors_pass1_##SUFFIX(                                                     \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    device uint32_t *out_sub_roots [[buffer(2)]],                                    \
    device uint8_t *out_sigs [[buffer(3)]],                                          \
    constant ForsParams &p [[buffer(4)]],                                            \
    threadgroup uint32_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    fors_pass1_impl<NW>(keys, jobs, out_sub_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void fors_pass2_##SUFFIX(                                                     \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    const device uint32_t *in_sub_roots [[buffer(2)]],                               \
    device uint32_t *out_fors_roots [[buffer(3)]],                                   \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant ForsParams &p [[buffer(5)]],                                            \
    threadgroup uint32_t *tg_nodes [[threadgroup(0)]],                               \
    uint32_t tg_id [[threadgroup_position_in_grid]],                                 \
    uint32_t tid [[thread_position_in_threadgroup]]                                  \
) {                                                                                  \
    fors_pass2_impl<NW>(keys, jobs, in_sub_roots, out_fors_roots, out_sigs, p, tg_nodes, tg_id, tid); \
}                                                                                    \
                                                                                     \
kernel void fors_pk_##SUFFIX(                                                        \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device ForsJobDesc *jobs [[buffer(1)]],                                    \
    const device uint32_t *fors_roots [[buffer(2)]],                                 \
    device uint32_t *out_pk_fors [[buffer(3)]],                                      \
    constant ForsParams &p [[buffer(4)]],                                            \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    fors_pk_impl<NW>(keys, jobs, fors_roots, out_pk_fors, p, gid);                   \
}                                                                                    \
                                                                                     \
kernel void wots_sign_##SUFFIX(                                                      \
    const device KeyMaterial *keys [[buffer(0)]],                                    \
    const device WotsSignLayerDesc *layers [[buffer(1)]],                            \
    const device uint32_t *pk_fors [[buffer(2)]],                                    \
    const device uint32_t *xmss_roots [[buffer(3)]],                                 \
    device uint8_t *out_sigs [[buffer(4)]],                                          \
    constant WotsSignParams &p [[buffer(5)]],                                        \
    uint32_t gid [[thread_position_in_grid]]                                         \
) {                                                                                  \
    wots_sign_impl<NW>(keys, layers, pk_fors, xmss_roots, out_sigs, p, gid);         \
}

DEFINE_KERNELS(N16, 4)
DEFINE_KERNELS(N24, 6)
DEFINE_KERNELS(N32, 8)
