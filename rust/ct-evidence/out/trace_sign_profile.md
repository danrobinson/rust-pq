### slh_sign_internal: unconditioned profile over random honest keys (m and PK.seed fixed)

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and m fixed)
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 19 (min 15985708271, max 15985708315, spread 44)
- distinct basic-block counts: 18
- distinct call-out (malloc/realloc/free/memcpy) counts: [19891227]
- distinct `thash` call counts: [2186220]
- distinct `sha256` call counts: [2186224]
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

