/* Single-lane contract for the extracted MSL memory effects. The harness
 * instantiates every kernel geometry and leaves lane, group and target symbolic.
 * AST extraction supplies run() between this file and the generated entry. */
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
typedef uint32_t uint;
static uint arbitrary(void) { uint v; __CPROVER_havoc_object(&v); return v; }
#define CHECK(c, msg) __CPROVER_assert((c), msg)
#define assume(c) __CPROVER_assume(c)
#define NW WORDS
#define NL WORDS
#define out_sigs UINT64_C(0)
#define tg_nodes UINT64_C(0)

enum kernels { chains, tlen, streaming, xmss, pass1, pass2, fors_pk, wots_sign };
enum resources { tips, leaves, roots, subroots, forsroots, pkfors };
typedef struct { uint num_trees, leaves_per_tree, wots_len, hp, num_sigs, subtrees_per_tree, k, a, s1, s2, num_layers; } Params;
typedef struct { uint auth_byte_off, target_leaf; } XmssTreeDesc;
typedef struct { uint wots_byte_off; } WotsSignLayerDesc;
typedef struct { uint sig_byte_off, indices[36]; } ForsJobDesc;
static Params p;
static uint tid, gid, tg_id, sig_idx, target, phase, lanes, active_height, watch;
static uint writes, global_mask, signature_count;
static bool admitted, uniform_keygen;
static uint owner_group, tree_number, subtree, descriptor, signature_base;

static XmssTreeDesc get_tree(uint index) {
    CHECK(index == owner_group, "XMSS descriptor belongs to this group");
    return (XmssTreeDesc){signature_base, target};
}
static WotsSignLayerDesc get_layer(uint index) {
    CHECK(index == owner_group / WOTS, "WOTS descriptor belongs to this layer");
    return (WotsSignLayerDesc){signature_base};
}
static uint get_fors_base(uint index) {
    CHECK(index == descriptor, "FORS descriptor belongs to this signature");
    return signature_base;
}
static uint get_fors_index(uint index) {
    CHECK(index == tree_number, "FORS target belongs to this tree");
    return target;
}

static void scratch_write(uint word) {
    CHECK(admitted && phase % 2 == 0, "scratch write phase");
    CHECK(tid < (lanes >> (phase / 2)), "only active parents write");
    CHECK(word / WORDS == tid, "scratch words have a unique writer");
    uint bit = 1u << (word % WORDS);
    CHECK(!(writes & bit), "word written once per level");
    writes |= bit;
}
static void scratch_read(uint64_t word) {
    CHECK(admitted && phase % 2 == 1, "scratch read phase");
    CHECK(word / WORDS < (lanes >> (phase / 2)), "read initialized at preceding barrier");
}
static void barrier(uint site) {
    CHECK(admitted, "inactive group cannot enter barrier");
    CHECK(site == (phase == 0 ? 0u : (phase % 2 ? 1u : 2u)), "identical barrier site order");
    if (phase % 2 == 0) {
        uint expected = tid < (lanes >> (phase / 2)) ? (1u << WORDS)-1u : 0u;
        CHECK(writes == expected, "all words of the active prefix initialized");
    }
    writes = 0;
    ++phase;
}

static void global_write(uint resource, uint word) {
    CHECK(admitted, "inactive group cannot write device memory");
    uint expected_resource = KERNEL == chains ? tips : (KERNEL == tlen || KERNEL == streaming) ? leaves :
        KERNEL == xmss ? roots : KERNEL == pass1 ? subroots : KERNEL == pass2 ? forsroots : pkfors;
    CHECK(resource == expected_resource, "expected device buffer");
    CHECK(tid == 0 && word >= owner_group*WORDS && word-owner_group*WORDS < WORDS, "device node has a unique writer");
    uint bit = 1u << (word-owner_group*WORDS);
    CHECK(!(global_mask & bit), "one publication of each output word");
    global_mask |= bit;
}
#define write_out_chain_tips(i) global_write(tips, i)
#define write_out_leaves(i) global_write(leaves, i)
#define write_out_roots(i) global_write(roots, i)
#define write_out_sub_roots(i) global_write(subroots, i)
#define write_out_fors_roots(i) global_write(forsroots, i)
#define write_out_pk_fors(i) global_write(pkfors, i)

/* Slot is relative to this tree's signature field. For pass1/pass2 the
 * descriptor and tree select the field, and the two passes own disjoint heights. */
static bool owns(uint slot) {
    if (!admitted) return false;
    if (KERNEL == wots_sign) return slot == owner_group % WOTS;
    if (KERNEL == xmss)
        return !uniform_keygen && slot < HP && tid == (slot ? ((target >> slot) ^ 1u) : 0u);
    if (KERNEL == pass1) {
        if (slot > S1 || subtree != (target >> S1)) return false;
        if (slot <= 1) return tid == ((target % (1u << S1)) >> 1);
        return tid == (((target >> (slot-1)) ^ 1u) % (1u << (S1-slot+1)));
    }
    if (KERNEL == pass2) {
        if (slot <= S1 || slot > A) return false;
        uint sibling = (target >> (slot-1)) ^ 1u;
        return tid == (slot == S1+1 ? sibling / 2 : sibling);
    }
    return false;
}
static void sig_write(uint64_t addr) {
    CHECK(admitted, "inactive group cannot write signature");
    uint field = signature_base;
    if (KERNEL == pass1 || KERNEL == pass2) field += N + tree_number*(1u+A)*N;
    uint slot;
    if (KERNEL == wots_sign) slot = owner_group % WOTS;
    else if (KERNEL == xmss) slot = phase ? 1u+phase/2 : 0u;
    else if (KERNEL == pass2) slot = S1 + (phase ? 2u+phase/2 : 1u);
    else slot = phase ? 2u+phase/2 : (uint)(addr != field);
    CHECK(addr == (uint64_t)field + slot*N, "signature offset belongs to its phase");
    CHECK(owns(slot), "signature node has its assigned unique writer");
    if (slot == watch) ++signature_count;
}
static void copy_node(uint64_t addr, uint64_t base) {
    for (uint i = 0; i < WORDS; ++i) scratch_read(base+i);
    sig_write(addr);
}
