static void check_reduction() {
    init();
    worker = arbitrary();
    treeNo = arbitrary();
    sub = arbitrary();
    target = arbitrary();
    __CPROVER_assume(worker < (1u << (lastHeight() - firstHeight() - 1)));
    __CPROVER_assume(treeNo < K && sub < subCount && target < (1u << (XMSS ? HP : A)));
    sigNumber = arbitrary();
    treeIndex = arbitrary();
    keyIndex = arbitrary();
    sigBase = arbitrary();
    XmssParams xp = {};
    xp.num_trees = treeIndex + 1;
    xp.hp = HP;
    xp.leaves_per_tree = 1u << HP;
    XmssTreeDesc desc = {};
    desc.layer = layer;
    desc.tree = tree;
    desc.target_leaf = target;
    desc.key_idx = keyIndex;
    desc.auth_byte_off = sigBase;
    ForsParams fp = {};
    fp.num_sigs = sigNumber + 1;
    fp.k = K;
    fp.a = A;
    fp.s1 = S1;
    fp.s2 = A - S1;
    fp.subtrees_per_tree = subCount;
    ForsJobDesc job = {};
    job.idx_tree = tree;
    job.idx_leaf = keypair;
    job.indices[treeNo] = target;
    job.key_idx = keyIndex;
    job.sig_byte_off = sigBase;
    if (XMSS)
        group = treeIndex;
    else if (PASS1)
        group = (sigNumber * K + treeNo) * subCount + sub;
    else
        group = sigNumber * K + treeNo;
    // Descriptor slots, group indices and signature bases remain symbolic.
    RUN_REDUCER
    uint end = lastHeight(), start = firstHeight();
    __CPROVER_assert(phase == 2 * (end - start) - 1, "reducer passes all levels");
    uint expectedCalls = 0, expectedSigs = 0;
    for (uint h = start; h < end; ++h) {
        if (worker < ((1u << end) >> (h + 1)))
            ++expectedCalls;
        if (PASS1 && (target >> S1) != sub)
            continue;
        uint sibling = (target >> h) ^ 1u;
        if (PASS1)
            sibling %= 1u << (S1 - h);
        uint writer = (h == start && !XMSS) ? sibling / 2 : (h == 0 && XMSS) ? 0 : sibling;
        if (worker == writer)
            ++expectedSigs;
        if (PASS1 && h == 0 && worker == writer)
            ++expectedSigs;
    }
    __CPROVER_assert(pairCalls == expectedCalls && leafCalls == (PASS1 ? 4 : 0),
                     "all required hashes evaluated");
    __CPROVER_assert(sigCount == expectedSigs, "all required signature fields written");
    __CPROVER_assert(rootMask == (worker == 0 ? (1u << words) - 1 : 0), "full root returned");
}
