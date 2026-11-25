// A node word is an arbitrary function of height, absolute node index and
// word number. This represents any table of actual FIPS nodes for the fixed
// key/address, including tables in which unrelated nodes coincide.
extern "C" Word __CPROVER_uninterpreted_node(unsigned, unsigned, unsigned);
#define nodeWord __CPROVER_uninterpreted_node
static uint worker, group, treeNo, sub, target, phase, leafCalls, pairCalls, sigCount;
static uint rootMask, scratchMask;
static const uint subCount = 1u << (A - S1);
static uint firstHeight() { return PASS2 ? S1 : 0; }
static uint lastHeight() { return XMSS ? HP : (PASS2 ? A : S1); }
static uint blockBase() { return XMSS ? 0 : (treeNo << A) + (PASS1 ? (sub << S1) : 0); }
static uint readHeight() { return firstHeight() + (phase + 1) / 2; }
static uint pairHeight() { return firstHeight() + 1 + (phase + 1) / 2; }
static uint atHeight(uint h, uint local) { return (blockBase() >> h) + local; }

static Word initialWord(uint offset) {
    offset -= (XMSS ? treeIndex * (1u << HP) : sigNumber * K * subCount) * words;
    return nodeWord(firstHeight(), offset / words, offset % words);
}
static Word sharedWord(uint offset) {
    return nodeWord(readHeight(), atHeight(readHeight(), offset / words), offset % words);
}
static void storeShared(uint offset, Word value) {
    uint h = firstHeight() + 1 + phase / 2;
    __CPROVER_assert(offset / words == worker, "write own parent");
    __CPROVER_assert(value == nodeWord(h, atHeight(h, worker), offset % words),
                     "computed parent placed in scratch");
    scratchMask |= 1u << (offset % words);
}
static void publishRoot(uint offset, Word value) {
    offset -= group * words;
    __CPROVER_assert(worker == 0 && offset < words, "publish root to its record");
    __CPROVER_assert(value == nodeWord(lastHeight(), atHeight(lastHeight(), 0), offset % words),
                     "publish computed root");
    rootMask |= 1u << (offset % words);
}
static void memoryBarrier() {
    if (!(phase % 2)) {
        uint h = firstHeight() + 1 + phase / 2;
        uint active = (1u << lastHeight()) >> h;
        __CPROVER_assert(scratchMask == (worker < active ? (1u << words) - 1 : 0),
                         "all parent values published at barrier");
        scratchMask = 0;
    }
    ++phase;
}
static void expectedOutput(uint offset, const Word *value) {
    // Decode the actual pointer offset relative to this signature.
    offset -= sigBase;
    uint block = offset / BYTES;
    __CPROVER_assert(offset % BYTES == 0, "whole authentication node");
    uint start = XMSS ? 0 : 1 + treeNo * (1 + A);
    __CPROVER_assert(block >= start && block - start <= (XMSS ? HP - 1 : A),
                     "field in current tree");
    uint slot = block - start;
    bool secret = !XMSS && !slot;
    uint h = XMSS ? slot : slot - 1;
    if (!secret)
        __CPROVER_assert(h < lastHeight() && h >= firstHeight(), "authentication height in pass");
    uint idx =
        secret ? (treeNo << A) + target : ((XMSS ? target : (treeNo << A) + target) >> h) ^ 1u;
    for (uint i = 0; i < words; ++i)
        __CPROVER_assert(value[i] == nodeWord(secret ? ~0u : h, idx, i),
                         "FIPS authentication or secret node value");
    ++sigCount;
}
static void signatureShared(uint offset, uint src) {
    Word value[words];
    for (uint i = 0; i < words; ++i)
        value[i] = sharedWord(src + i);
    expectedOutput(offset, value);
}

static void localPair(const Key &km, uint lyr, uint64_t tr, uint type, uint kp, uint h, uint idx,
                      const Word *left, const Word *right, Word *out) {
    __CPROVER_assert(&km == &key && lyr == (XMSS ? layer : 0) && tr == tree &&
                         type == (XMSS ? 2 : 3) && kp == (XMSS ? 0 : keypair),
                     "FIPS parent domain");
    __CPROVER_assert(h == pairHeight() && idx == atHeight(h, worker),
                     "FIPS parent height and index");
    for (uint i = 0; i < words; ++i) {
        __CPROVER_assert(left[i] == nodeWord(h - 1, 2 * idx, i) &&
                             right[i] == nodeWord(h - 1, 2 * idx + 1, i),
                         "ordered Merkle children");
        out[i] = nodeWord(h, idx, i);
    }
    ++pairCalls;
}

static void leafShort(const Word *seed, const Word *packed, const Word *in, Word *out) {
    bool secret = leafCalls % 2 == 0;
    uint idx = atHeight(0, 2 * worker + leafCalls / 2);
    typ = secret ? 6 : 3;
    height = 0;
    index = idx;
    layer = 0;
    explicitAddress = true;
    uint addrLen = SHAKE ? 32 : 22;
    for (uint i = 0; i < addrLen; ++i)
        __CPROVER_assert(nodeByte(packed, i) == addressByte(i), "FORS PRF or F address");
#if SHAKE
    for (uint i = 0; i < words; ++i)
        __CPROVER_assert(seed[i] == key.pk_seed[i], "FORS public seed");
#else
    __CPROVER_assert(!(packed[5] & 65535), "compressed ADRS carry has zero low half");
    for (uint i = 0; i < 8; ++i)
        __CPROVER_assert(seed[i] == key.state256[i], "FORS public seed");
#endif
    for (uint i = 0; i < words; ++i) {
        __CPROVER_assert(in[i] == (secret ? key.sk_seed[i] : nodeWord(~0u, idx, i)),
                         "FORS secret input");
        out[i] = nodeWord(secret ? ~0u : 0, idx, i);
    }
    ++leafCalls;
}
