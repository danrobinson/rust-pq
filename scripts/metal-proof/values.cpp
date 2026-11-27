// The shader and oracle share only compression/permutation results. Each call
// checks the complete state and block against independently serialized bytes.
#include <stdint.h>
#define thread
#define threadgroup
#define device
#define constant const
typedef unsigned uint;
/* descriptor declarations */
static unsigned arbitrary() {
    unsigned x;
    __CPROVER_havoc_object(&x);
    return x;
}
static uint64_t arbitrary64() {
    uint64_t x;
    __CPROVER_havoc_object(&x);
    return x;
}
#if SHAKE
typedef uint64_t Word;
typedef ShakeKeyMaterial Key;
#else
typedef uint32_t Word;
typedef KeyMaterial Key;
#endif
static Key key;
static unsigned sigNumber, keyIndex, treeIndex, layerCount, layerIndex, globalLeaf, sigBase;
static uint32_t layer, keypair, chain, height, index, typ;
static uint64_t tree;
static unsigned calls;
#if STREAM_NODES
static unsigned tipCount;
static Word streamData[STREAM_NODES * words];
static uint64_t priorState[25];
#endif
static bool pairMode, explicitAddress;
static Word signingMessage[words];
static unsigned expectedDigit;
static Word input[words], rightNode[words], previous[words];

static uint8_t big(uint64_t v, uint n, uint off) { return v >> (8 * (n - 1 - off)); }
static uint8_t nodeByte(const Word *src, uint i) {
    return SHAKE ? uint8_t(src[i / 8] >> (8 * (i % 8))) : big(src[i / 4], 4, i % 4);
}
// Independent FIPS 205 address encodings. The tree address occupies 12
// bytes in uncompressed ADRS, with its top four bytes zero for SLH-DSA.
static uint8_t addressByte(unsigned i) {
    unsigned type = pairMode || explicitAddress ? typ : (calls ? 0 : 5);
    unsigned w2 = pairMode || explicitAddress ? height : chain;
    unsigned w3 = pairMode || explicitAddress ? index : (calls ? calls - 1 : 0);
    if (SHAKE) {
        if (i < 4)
            return big(layer, 4, i);
        if (i < 8)
            return 0;
        if (i < 16)
            return big(tree, 8, i - 8);
        if (i < 20)
            return big(type, 4, i - 16);
        if (i < 24)
            return big(keypair, 4, i - 20);
        if (i < 28)
            return big(w2, 4, i - 24);
        return big(w3, 4, i - 28);
    }
    if (i == 0)
        return layer;
    if (i < 9)
        return big(tree, 8, i - 1);
    if (i == 9)
        return type;
    if (i < 14)
        return big(keypair, 4, i - 10);
    if (i < 18)
        return big(w2, 4, i - 14);
    return big(w3, 4, i - 18);
}
static unsigned payloadLength() {
#if STREAM_NODES
    return (SHAKE ? BYTES + 32 : 22) + STREAM_NODES * BYTES;
#endif
    return (SHAKE ? BYTES + 32 : 22) + BYTES * (pairMode ? 2 : 1);
}
static uint8_t payload(unsigned i) {
#if SHAKE
    if (i < BYTES)
        return nodeByte(key.pk_seed, i);
    i -= BYTES;
#endif
    const unsigned addrLen = SHAKE ? 32 : 22;
    if (i < addrLen)
        return addressByte(i);
    i -= addrLen;
#if STREAM_NODES
    return nodeByte(streamData, i);
#endif
    if (i < BYTES)
        return nodeByte(pairMode || !calls ? input : previous, i);
    return nodeByte(rightNode, i - BYTES);
}
static uint8_t blockByte(unsigned i, unsigned blockLen) {
    unsigned len = payloadLength();
    if (i < len)
        return payload(i);
    if (SHAKE)
        return (i == len ? 31 : 0) ^ (i == (len / 136 + 1) * 136 - 1 ? 128 : 0);
    if (i == len)
        return 128;
    unsigned trailer =
        ((len + 1 + (blockLen == 64 ? 8 : 16) + blockLen - 1) / blockLen) * blockLen - 8;
    if (i < trailer)
        return 0;
    return big((blockLen + len) * 8, 8, i - trailer);
}

#if SHAKE
static void keccak_f1600(uint64_t state[25]) {
    // Arbitrary position is sufficient to compare all 200 input bytes.
#if STREAM_NODES
    for (uint i = 0; i < 200; ++i) {
        uint8_t v = nodeByte(priorState, i);
        if (i < 136)
            v ^= blockByte(calls * 136 + i, 136);
        __CPROVER_assert(nodeByte(state, i) == v, "FIPS streaming SHAKE state");
    }
#else
    unsigned i = arbitrary();
    __CPROVER_assume(i < 200);
    __CPROVER_assert(nodeByte(state, i) == blockByte(i, 136), "FIPS sponge input");
#endif
    for (uint j = 0; j < 25; ++j)
        state[j] = arbitrary64();
#if STREAM_NODES
    for (uint j = 0; j < 25; ++j)
        priorState[j] = state[j];
#endif
    for (uint j = 0; j < words; ++j)
        previous[j] = state[j];
    ++calls;
}
#else
static void sha256_compress_from(const uint32_t seed[8], uint32_t block[16], uint32_t out[8]) {
    uint j = arbitrary();
    __CPROVER_assume(j < 8);
    __CPROVER_assert(seed[j] == key.state256[j], "SHA-256 seed state");
    uint i = arbitrary();
    __CPROVER_assume(i < 64);
    __CPROVER_assert(nodeByte(block, i) == blockByte(i, 64), "FIPS SHA-256 block");
    for (uint k = 0; k < 8; ++k)
        out[k] = arbitrary();
    for (uint k = 0; k < words; ++k)
        previous[k] = out[k];
    ++calls;
}
#if STREAM_NODES
static void sha256_compress(uint32_t state[8], uint32_t block[16]) {
    for (uint j = 0; j < 8; ++j)
        __CPROVER_assert(state[j] == (calls ? priorState[j] : key.state256[j]),
                         "stream SHA-256 chaining state");
    for (uint i = 0; i < 64; ++i)
        __CPROVER_assert(nodeByte(block, i) == blockByte(calls * 64 + i, 64),
                         "FIPS streaming SHA-256 block");
    for (uint j = 0; j < 8; ++j)
        state[j] = priorState[j] = arbitrary();
    for (uint j = 0; j < words; ++j)
        previous[j] = state[j];
    ++calls;
}
#endif
static void sha512_compress(uint64_t state[8], uint64_t block[16]) {
#if STREAM_NODES
    for (uint j = 0; j < 8; ++j)
        __CPROVER_assert(state[j] == (calls ? priorState[j] : key.state512[j]),
                         "stream SHA-512 chaining state");
    for (uint i = 0; i < 128; ++i)
        __CPROVER_assert(big(block[i / 8], 8, i % 8) == blockByte(calls * 128 + i, 128),
                         "FIPS streaming SHA-512 block");
#else
    uint j = arbitrary();
    __CPROVER_assume(j < 8);
    __CPROVER_assert(state[j] == key.state512[j], "SHA-512 seed state");
    uint i = arbitrary();
    __CPROVER_assume(i < 128);
    __CPROVER_assert(big(block[i / 8], 8, i % 8) == blockByte(i, 128), "FIPS SHA-512 block");
#endif
    for (uint k = 0; k < 8; ++k)
        state[k] = arbitrary64();
#if STREAM_NODES
    for (uint k = 0; k < 8; ++k)
        priorState[k] = state[k];
#endif
    for (uint k = 0; k < words; ++k)
        previous[k] = state[k / 2] >> (k % 2 ? 0 : 32);
    ++calls;
}
#endif
/* MSL definitions */

static void init() {
    layer = arbitrary();
    tree = arbitrary64();
    keypair = arbitrary();
    chain = arbitrary();
    __CPROVER_assume(chain < chains);
    height = arbitrary();
    index = arbitrary();
    typ = arbitrary();
    for (uint i = 0; i < words; ++i) {
        key.sk_seed[i] = arbitrary64();
        input[i] = key.sk_seed[i];
        rightNode[i] = arbitrary64();
#if SHAKE
        key.pk_seed[i] = arbitrary64();
#endif
    }
#if !SHAKE
    for (uint i = 0; i < 8; ++i) {
        key.state256[i] = arbitrary();
        key.state512[i] = arbitrary64();
    }
#endif
}

static unsigned digit(const Word *msg, unsigned c) {
    unsigned checksum = 0;
    for (uint i = 0; i < BYTES; ++i) {
        uint b = nodeByte(msg, i);
        checksum += 15 - b / 16;
        checksum += 15 - b % 16;
    }
    if (c < 2 * BYTES) {
        unsigned b = nodeByte(msg, c / 2);
        return c % 2 ? b % 16 : b / 16;
    }
    return (checksum >> (4 * (2 * BYTES + 2 - c))) % 16;
}
static void check_digit() {
    init();
#if SHAKE
    unsigned actual = shake_wots_digit_at<words>(input, chain);
#else
    unsigned actual = wots_digit_at<words>(input, chain);
#endif
    __CPROVER_assert(actual == digit(input, chain), "FIPS message or checksum digit");
}

static void check_chain() {
    init();
    unsigned steps = arbitrary();
    __CPROVER_assume(steps <= 15);
    Word out[words];
#if SHAKE
    shake_run_wots_chain<words>(key.pk_seed, input, layer, tree, keypair, chain, steps, out);
#else
    run_wots_chain<words>(key.state256, input, layer, tree, keypair, chain, steps, out);
#endif
    __CPROVER_assert(calls == 1 + steps, "PRF followed by one F per step");
    unsigned j = arbitrary();
    __CPROVER_assume(j < words);
    __CPROVER_assert(out[j] == previous[j], "final chain word");
}
static void check_pair() {
    init();
    pairMode = true;
    Word out[words];
#if SHAKE
    shake_thash_pair<words>(key, layer, tree, typ, keypair, height, index, input, rightNode, out);
#else
    thash_pair_words<words>(key, layer, tree, typ, keypair, height, index, input, rightNode, out);
#endif
    unsigned j = arbitrary();
    __CPROVER_assume(j < words);
    __CPROVER_assert(calls == 1 && out[j] == previous[j], "pair produces truncated parent");
}
static void check_sign() {
    init();
    sigNumber = arbitrary();
    keyIndex = arbitrary();
    sigBase = arbitrary();
    layerCount = arbitrary();
    __CPROVER_assume(layerCount == 7 || layerCount == 8 || layerCount == 17 || layerCount == 22);
    __CPROVER_assume(layer < layerCount);
    layerIndex = sigNumber * layerCount + layer;
    // The arrays represent slices starting at the symbolic request and layer.
    WotsSignLayerDesc desc = {};
    desc.layer = layer;
    desc.tree = tree;
    desc.keypair = keypair;
    desc.key_idx = keyIndex;
    desc.sig_idx = sigNumber;
    desc.wots_byte_off = sigBase;
    WotsSignParams p = {};
    p.num_layers = (sigNumber + 1) * layerCount;
    p.wots_len = chains;
    p.d = layerCount;
    Word roots[22 * words], fors[words];
    for (uint i = 0; i < words; ++i) {
        fors[i] = arbitrary64();
        if (layer)
            roots[(layer - 1) * words + i] = arbitrary64();
    }
    for (uint i = 0; i < words; ++i)
        signingMessage[i] = layer ? roots[(layer - 1) * words + i] : fors[i];
    expectedDigit = arbitrary();
    __CPROVER_assume(expectedDigit < 16);
    uint8_t out[chains * BYTES];
#if SHAKE
    shake_wots_sign_impl<words>(&key, &desc, fors, roots, out, p, layerIndex * chains + chain);
#else
    wots_sign_impl<words>(&key, &desc, fors, roots, out, p, layerIndex * chains + chain);
#endif
    __CPROVER_assert(calls == 1 + expectedDigit, "WOTS field chain count");
    uint i = arbitrary();
    __CPROVER_assume(i < BYTES);
    __CPROVER_assert(out[chain * BYTES + i] == nodeByte(previous, i), "WOTS field output byte");
}

#if STREAM_NODES
static void check_stream() {
    init();
    pairMode = true;
    height = index = 0;
    __CPROVER_havoc_object(&streamData);
    Word out[words];
#if WOTS_STREAM
    typ = 1;
    treeIndex = arbitrary();
    keyIndex = arbitrary();
    uint leavesPerTree = 1u << (arbitrary() % 10);
    __CPROVER_assume(keypair < leavesPerTree);
    globalLeaf = treeIndex * leavesPerTree + keypair;
    XmssTreeDesc desc = {};
    desc.layer = layer;
    desc.tree = tree;
    desc.key_idx = keyIndex;
    XmssParams p = {};
    p.num_trees = treeIndex + 1;
    p.leaves_per_tree = leavesPerTree;
    p.wots_len = STREAM_NODES;
#if FUSED
#if SHAKE
    shake_xmss_leaves_streaming_impl<words>(&key, &desc, out, p, globalLeaf);
#else
    xmss_leaves_streaming_impl<words>(&key, &desc, out, p, globalLeaf);
#endif
    __CPROVER_assert(tipCount == chains, "all WOTS tips consumed");
#elif TIP_ONLY
    Word tips[chains * words];
#if SHAKE
    shake_wots_chains_impl<words>(&key, &desc, tips, p, globalLeaf * chains + chain);
#else
    wots_chains_impl<words>(&key, &desc, tips, p, globalLeaf * chains + chain);
#endif
    __CPROVER_assert(tipCount == 1, "one chain tip computed");
    for (uint i = 0; i < words; ++i)
        __CPROVER_assert(tips[chain * words + i] == streamData[chain * words + i],
                         "computed tip published");
    return;
#elif SHAKE
    shake_wots_tlen_impl<words>(&key, &desc, streamData, out, p, globalLeaf);
#else
    wots_tlen_impl<words>(&key, &desc, streamData, out, p, globalLeaf);
#endif
#else
    typ = 4;
    layer = 0;
    sigNumber = arbitrary();
    keyIndex = arbitrary();
    ForsJobDesc desc = {};
    desc.idx_tree = tree;
    desc.idx_leaf = keypair;
    desc.key_idx = keyIndex;
    ForsParams p = {};
    p.num_sigs = sigNumber + 1;
    p.k = STREAM_NODES;
#if SHAKE
    shake_fors_pk_impl<words>(&key, &desc, streamData, out, p, sigNumber);
#else
    fors_pk_impl<words>(&key, &desc, streamData, out, p, sigNumber);
#endif
#endif
    unsigned len = payloadLength();
    unsigned blocks =
        SHAKE ? len / 136 + 1 : (BYTES == 16 ? (len + 9 + 63) / 64 : (len + 17 + 127) / 128);
    __CPROVER_assert(calls == blocks, "stream compression count");
    for (uint j = 0; j < words; ++j)
        __CPROVER_assert(out[j] == previous[j], "stream publishes truncated digest");
}
#endif

static void check_short() {
    init();
    explicitAddress = true;
    Word out[words];
#if SHAKE
    Word a, b, c, d;
    adrs_full_lanes(layer, tree, typ, keypair, height, index, a, b, c, d);
    shake_thash_short<words>(key.pk_seed, a, b, c, d, input, out);
#else
    Word a, b, c, d, e, f;
    adrs_to_w256(layer, tree, typ, keypair, height, index, a, b, c, d, e, f);
    thash_short_words<words>(key.state256, a, b, c, d, e, f, input, out);
#endif
    for (uint i = 0; i < words; ++i)
        __CPROVER_assert(out[i] == previous[i] && calls == 1,
                         "short hash truncates one compression");
}
static void check_serialization() {
    init();
    uint8_t first[BYTES], second[BYTES];
#if SHAKE
    write_shake_node_bytes<words>(first, input);
    write_shake_node_bytes_tg<words>(second, input);
#else
    write_node_bytes<words>(first, input);
    write_node_bytes_tg<words>(second, input);
#endif
    for (uint i = 0; i < BYTES; ++i)
        __CPROVER_assert(first[i] == nodeByte(input, i) && second[i] == nodeByte(input, i),
                         "FIPS node serialization");
}
