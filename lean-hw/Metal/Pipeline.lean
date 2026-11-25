import Spec.Correctness

/-!
# Verification of the Metal GPU SLH-DSA Pipeline

Proves functional equivalence between the Metal GPU compute kernels
(`metal/shaders/slhdsa.metal`, `metal/shaders/slhdsa_shake.metal`, and
host orchestration in `metal/src/lib.rs`) and the FIPS 205 specification
(`Spec.SlhDsa`), for all twelve SHA-2 and SHAKE parameter sets:

1. **Two-phase vs streaming XMSS WOTS+ leaves** (`metal_wots_two_phase_eq_fips`,
   `metal_wots_streaming_eq_fips`, `metal_wots_two_phase_eq_streaming`,
   `metal_wots_sign_eq_fips`).
2. **GPU bottom-up threadgroup Merkle reduction** (`metal_xmss_reduce_eq_fips`).
3. **2-leaf-per-thread two-pass FORS decomposition** (`metal_fors_two_pass_eq_fips`).
4. **Composed GPU keygen and single/batched signing with direct byte-offset
   buffer writes** (`metal_keygen_eq_fips`, `metal_sign_internal_eq_fips`,
   `metal_sign_eq_fips`, `metal_batch_sign_eq_fips`,
   `metal_all_12_params_sign_eq_fips`).
-/

namespace MetalPipeline
open Spec

/-! ## Parameter Set Validity (All 12 SHA-2 and SHAKE Sets) -/

theorem shake_128s_valid : shake_128s.Valid := by constructor <;> decide
theorem shake_128f_valid : shake_128f.Valid := by constructor <;> decide
theorem shake_192s_valid : shake_192s.Valid := by constructor <;> decide
theorem shake_192f_valid : shake_192f.Valid := by constructor <;> decide
theorem shake_256s_valid : shake_256s.Valid := by constructor <;> decide
theorem shake_256f_valid : shake_256f.Valid := by constructor <;> decide

/-- Every valid Table 2 parameter set (both SHA-2 and SHAKE) has
`w = 16`, `len1 = 2*n`, `len2 = 3`, `len = 2*n + 3`. -/
theorem valid_wots_params {p : Params} (hv : p.Valid) :
    p.w = 16 ∧ p.len1 = 2 * p.n ∧ p.len2 = 3 ∧ p.len = 2 * p.n + 3 := by
  have hlgw : p.lgw = 4 := hv.lgw_eq
  have hw : p.w = 16 := by simp [Params.w, hlgw]
  have hlen1 : p.len1 = 2 * p.n := by
    simp [Params.len1, hlgw]
    omega
  have hlen2 : p.len2 = 3 := by
    rcases hv.n_cases with hn | hn | hn <;>
      simp [Params.len2, hlen1, hw, hlgw, hn]
  have hlen : p.len = 2 * p.n + 3 := by
    simp [Params.len, hlen1, hlen2]
  exact ⟨hw, hlen1, hlen2, hlen⟩

/-! ## Arithmetic & Bitwise Helpers -/

private theorem append_foldl_eq {α : Type} (xs : List α) (f : α → Bytes) (acc : Bytes) :
    xs.foldl (fun s x => s ++ f x) acc = acc ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

private theorem xor_one_lt_two_pow {x k : Nat} (hk : 1 ≤ k) (hx : x < 2 ^ k) :
    x ^^^ 1 < 2 ^ k := by
  rw [xor_one_eq]
  have heven : 2 ^ k % 2 = 0 := by
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  split <;> omega

private theorem xor_one_div_two_pow {x d : Nat} (hd : 1 ≤ d) :
    (x ^^^ 1) / 2 ^ d = x / 2 ^ d := by
  rw [xor_one_eq]
  have h2d_pos : 0 < 2 ^ d := Nat.two_pow_pos d
  have h2d_even : 2 ^ d % 2 = 0 := by
    have : 2 ^ d = 2 * 2 ^ (d - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  have hdm := Nat.div_add_mod x (2 ^ d)
  have hmod_lt : x % 2 ^ d < 2 ^ d := Nat.mod_lt x h2d_pos
  set q := x / 2 ^ d
  set r := x % 2 ^ d
  have hmul_even : (2 ^ d * q) % 2 = 0 := by
    rw [Nat.mul_mod, h2d_even]; simp
  split
  · rename_i hx_even
    have hr_even : r % 2 = 0 := by omega
    have hr1_lt : r + 1 < 2 ^ d := by omega
    have hx1 : x + 1 = 2 ^ d * q + (r + 1) := by omega
    rw [hx1, Nat.mul_add_div h2d_pos, Nat.div_eq_of_lt hr1_lt, Nat.add_zero]
  · rename_i hx_odd
    have hr_odd : r % 2 = 1 := by omega
    have hx1 : x - 1 = 2 ^ d * q + (r - 1) := by omega
    rw [hx1, Nat.mul_add_div h2d_pos, Nat.div_eq_of_lt (by omega : r - 1 < 2 ^ d), Nat.add_zero]

private theorem gid_decode_3 {treeIdx leafIdx chain leavesPerTree wotsLen : Nat}
    (hleaf : leafIdx < leavesPerTree) (hchain : chain < wotsLen) :
    let gid := (treeIdx * leavesPerTree + leafIdx) * wotsLen + chain
    gid % wotsLen = chain ∧
    (gid / wotsLen) % leavesPerTree = leafIdx ∧
    (gid / wotsLen) / leavesPerTree = treeIdx := by
  have hw_pos : 0 < wotsLen := by omega
  have hl_pos : 0 < leavesPerTree := by omega
  dsimp only
  have hdiv1 : ((treeIdx * leavesPerTree + leafIdx) * wotsLen + chain) / wotsLen =
      treeIdx * leavesPerTree + leafIdx := by
    rw [Nat.mul_comm _ wotsLen, Nat.mul_add_div hw_pos, Nat.div_eq_of_lt hchain, Nat.add_zero]
  have hmod1 : ((treeIdx * leavesPerTree + leafIdx) * wotsLen + chain) % wotsLen = chain := by
    rw [Nat.mul_comm _ wotsLen, Nat.mul_add_mod, Nat.mod_eq_of_lt hchain]
  have hdiv2 : (treeIdx * leavesPerTree + leafIdx) / leavesPerTree = treeIdx := by
    rw [Nat.mul_comm _ leavesPerTree, Nat.mul_add_div hl_pos, Nat.div_eq_of_lt hleaf, Nat.add_zero]
  have hmod2 : (treeIdx * leavesPerTree + leafIdx) % leavesPerTree = leafIdx := by
    rw [Nat.mul_comm _ leavesPerTree, Nat.mul_add_mod, Nat.mod_eq_of_lt hleaf]
  exact ⟨hmod1, by rw [hdiv1, hmod2], by rw [hdiv1, hdiv2]⟩

private theorem gid_decode_2 {a b stride : Nat} (hb : b < stride) :
    (a * stride + b) % stride = b ∧ (a * stride + b) / stride = a := by
  have hs : 0 < stride := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm a stride, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  · rw [Nat.mul_comm a stride, Nat.mul_add_div hs, Nat.div_eq_of_lt hb, Nat.add_zero]

/-! ## Flat Byte-Buffer Direct-Write Model (`out_sigs`) -/

/-- A single direct write of `val` at byte offset `off` into a flat GPU output buffer. -/
def patchAt (buf : Bytes) (off : Nat) (val : Bytes) : Bytes :=
  buf.take off ++ val ++ buf.drop (off + val.length)

theorem patchAt_length (buf : Bytes) (off : Nat) (val : Bytes)
    (hfit : off + val.length ≤ buf.length) :
    (patchAt buf off val).length = buf.length := by
  simp only [patchAt, List.length_append, List.length_take, List.length_drop]
  omega

/-- Non-overlapping direct writes into a flat GPU output buffer commute, justifying
concurrent execution of FORS, XMSS, and WOTS+ kernels writing to disjoint slices
of `out_sigs`. -/
theorem patchAt_comm (buf : Bytes) (off₁ off₂ : Nat) (v₁ v₂ : Bytes)
    (hdisj : off₁ + v₁.length ≤ off₂) (hfit : off₂ + v₂.length ≤ buf.length) :
    patchAt (patchAt buf off₁ v₁) off₂ v₂ = patchAt (patchAt buf off₂ v₂) off₁ v₁ := by
  have hlen1 : (patchAt buf off₁ v₁).length = buf.length := patchAt_length buf off₁ v₁ (by omega)
  have hlen2 : (patchAt buf off₂ v₂).length = buf.length := patchAt_length buf off₂ v₂ hfit
  have hlenL : (patchAt (patchAt buf off₁ v₁) off₂ v₂).length = buf.length := by
    rw [patchAt_length _ _ _ (by omega), hlen1]
  have hlenR : (patchAt (patchAt buf off₂ v₂) off₁ v₁).length = buf.length := by
    rw [patchAt_length _ _ _ (by omega), hlen2]
  apply List.ext_getElem (by rw [hlenL, hlenR])
  intro i hi1 hi2
  have hi_buf : i < buf.length := by rw [hlenL] at hi1; exact hi1
  have get_patch : ∀ (b : Bytes) (o : Nat) (v : Bytes) (hf : o + v.length ≤ b.length)
      (k : Nat) (hk : k < (patchAt b o v).length),
      (patchAt b o v)[k] =
        if h1 : k < o then b[k]'(by rw [patchAt_length b o v hf] at hk; exact hk)
        else if h2 : k < o + v.length then v[k - o]'(by omega)
        else b[k]'(by rw [patchAt_length b o v hf] at hk; exact hk) := by
    intro b o v hf k hk
    have hk_b : k < b.length := by rw [patchAt_length b o v hf] at hk; exact hk
    simp only [patchAt]
    by_cases h1 : k < o
    · have hl : k < (b.take o ++ v).length := by simp [List.length_take]; omega
      rw [List.getElem_append_left hl, List.getElem_append_left (by simp [List.length_take]; omega),
          List.getElem_take]
      simp [h1]
    · by_cases h2 : k < o + v.length
      · have hl : k < (b.take o ++ v).length := by simp [List.length_take]; omega
        have hge : (b.take o).length ≤ k := by simp [List.length_take]; omega
        rw [List.getElem_append_left hl, List.getElem_append_right hge]
        have htk : (b.take o).length = o := by simp [List.length_take]; omega
        simp [h1, h2, htk]
      · have hge : (b.take o ++ v).length ≤ k := by simp [List.length_take]; omega
        rw [List.getElem_append_right hge, List.getElem_drop]
        have hmin : min o b.length = o := Nat.min_eq_left (by omega)
        have hidx : o + v.length + (k - (o + v.length)) = k := by omega
        simp only [h1, h2, ↓reduceDIte, List.length_append, List.length_take, hmin, hidx]
  rw [get_patch _ off₂ v₂ (by omega) i hi1, get_patch _ off₁ v₁ (by omega) i hi2]
  by_cases c1 : i < off₁
  · have c2 : i < off₂ := by omega
    simp only [c1, c2, ↓reduceDIte]
    rw [get_patch buf off₁ v₁ (by omega) i (by omega), get_patch buf off₂ v₂ hfit i (by omega)]
    simp [c1, c2]
  · by_cases c2 : i < off₁ + v₁.length
    · have c3 : i < off₂ := by omega
      simp only [c1, c2, c3, ↓reduceDIte]
      rw [get_patch buf off₁ v₁ (by omega) i (by omega)]
      simp [c1, c2]
    · by_cases c3 : i < off₂
      · simp only [c1, c2, c3, ↓reduceDIte]
        rw [get_patch buf off₁ v₁ (by omega) i (by omega), get_patch buf off₂ v₂ hfit i (by omega)]
        simp [c1, c2, c3]
      · by_cases c4 : i < off₂ + v₂.length
        · simp only [c1, c2, c3, c4, ↓reduceDIte]
          rw [get_patch buf off₂ v₂ hfit i (by omega)]
          simp [c3, c4]
        · simp only [c1, c2, c3, c4, ↓reduceDIte]
          rw [get_patch buf off₁ v₁ (by omega) i (by omega), get_patch buf off₂ v₂ hfit i (by omega)]
          simp [c1, c2, c3, c4]

/-- Writing a contiguous sequence of `k` chunks of equal length `L` starting at `base`
replaces exactly the `[base .. base + k * L)` slice with their concatenation. -/
def patchChunks (buf : Bytes) (base L : Nat) (chunks : Nat → Bytes) (k : Nat) : Bytes :=
  (List.range k).foldl (fun b i => patchAt b (base + i * L) (chunks i)) buf

theorem patchChunks_eq (buf : Bytes) (base L : Nat) (chunks : Nat → Bytes)
    (hlen : ∀ i, (chunks i).length = L) (k : Nat) (hfit : base + k * L ≤ buf.length) :
    patchChunks buf base L chunks k = patchAt buf base ((List.range k).flatMap chunks) := by
  induction k with
  | zero =>
    simp [patchChunks, patchAt]
  | succ k ih =>
    have hfit_k : base + k * L ≤ buf.length := by rw [Nat.succ_mul] at hfit; omega
    simp only [patchChunks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change patchAt (patchChunks buf base L chunks k) (base + k * L) (chunks k) = _
    rw [ih hfit_k]
    have hflat_len : ((List.range k).flatMap chunks).length = k * L :=
      length_flatMap_const chunks L hlen k
    have hchunk_len : (chunks k).length = L := hlen k
    simp only [patchAt, List.flatMap_append, List.flatMap_singleton, List.length_append,
      hflat_len, hchunk_len]
    have htake1 : (buf.take base ++ (List.range k).flatMap chunks ++ buf.drop (base + k * L)).take
        (base + k * L) = buf.take base ++ (List.range k).flatMap chunks := by
      have hl : (buf.take base ++ (List.range k).flatMap chunks).length = base + k * L := by
        simp [List.length_take, hflat_len]; omega
      rw [List.take_left' hl]
    have hdrop1 : (buf.take base ++ (List.range k).flatMap chunks ++ buf.drop (base + k * L)).drop
        (base + k * L + L) = buf.drop (base + (k * L + L)) := by
      have hl : (buf.take base ++ (List.range k).flatMap chunks).length = base + k * L := by
        simp [List.length_take, hflat_len]; omega
      rw [show base + k * L + L = (base + k * L) + L from rfl, ← List.drop_drop,
          List.drop_left' hl, List.drop_drop, Nat.add_assoc]
    rw [htake1, hdrop1]
    simp only [List.append_assoc]

theorem patchAt_append (buf : Bytes) (off : Nat) (v₁ v₂ : Bytes)
    (hfit : off + v₁.length + v₂.length ≤ buf.length) :
    patchAt (patchAt buf off v₁) (off + v₁.length) v₂ = patchAt buf off (v₁ ++ v₂) := by
  have hl : (buf.take off ++ v₁).length = off + v₁.length := by
    simp [List.length_take]; omega
  simp only [patchAt, List.length_append]
  rw [List.take_left' hl]
  rw [show off + v₁.length + v₂.length = (off + v₁.length) + v₂.length from rfl,
      ← List.drop_drop, List.drop_left' hl, List.drop_drop, Nat.add_assoc]
  simp only [List.append_assoc]

theorem patchAt_full (buf val : Bytes) (h : val.length = buf.length) :
    patchAt buf 0 val = val := by
  simp [patchAt, h]

/-! ## Part 1: Two-Phase vs Streaming XMSS WOTS+ Kernels -/

/-- Shared XMSS tree descriptor (`XmssTreeDesc` in `slhdsa.metal` and `metal/src/lib.rs`). -/
structure XmssTreeDesc where
  tree : Nat
  keyIdx : Nat
  layer : Nat
  targetLeaf : Option Nat
  authByteOff : Nat

/-- Per-chain helper `run_wots_chain` / `shake_run_wots_chain`:
`PRF` with `WOTS_PRF` followed by `steps` iterations of `F` with `WOTS_HASH`. -/
def metalRunWotsChain (p : Params) (skSeed pkSeed : Bytes)
    (layer tree keypair c steps : Nat) : Bytes :=
  let adrs := { { Adrs.zero with layer := layer, tree := tree }.setTypeAndClear WOTS_HASH with
                keypair := keypair }
  let sk := PRF p pkSeed skSeed { wotsSkAdrs adrs with word2 := c }
  chain p sk 0 steps pkSeed { adrs with word2 := c }

/-- Phase 1 (`wots_chains` / `shake_wots_chains`):
1 thread per WOTS+ chain (`gid = (treeIdx * leavesPerTree + leafIdx) * wotsLen + chain`).
Writes the 15-step chain tip to `endpoints[gid]`. -/
def metalWotsChainsKernel (p : Params) (keys : Nat → Bytes × Bytes)
    (trees : Nat → XmssTreeDesc) (gid : Nat) : Bytes :=
  let leavesPerTree := 2 ^ p.hp
  let wotsLen := p.len
  let c := gid % wotsLen
  let leafGlobal := gid / wotsLen
  let leafIdx := leafGlobal % leavesPerTree
  let treeIdx := leafGlobal / leavesPerTree
  let desc := trees treeIdx
  let (skSeed, pkSeed) := keys desc.keyIdx
  metalRunWotsChain p skSeed pkSeed desc.layer desc.tree leafIdx c 15

/-- Phase 2 (`wots_tlen` / `shake_wots_tlen`):
1 thread per leaf (`leafGid = treeIdx * leavesPerTree + leafIdx`).
Streams `endpoints[leafGid * wotsLen .. (leafGid + 1) * wotsLen]` through `T_len`
with `ADRS_WOTS_PK` (`22 + len * N` bytes after `PK.seed || 0^{B-N}` for SHA-2;
`N + 32 + len * N` bytes for SHAKE). -/
def metalWotsTlenKernel (p : Params) (keys : Nat → Bytes × Bytes)
    (trees : Nat → XmssTreeDesc) (endpoints : Nat → Bytes) (leafGid : Nat) : Bytes :=
  let leavesPerTree := 2 ^ p.hp
  let leafIdx := leafGid % leavesPerTree
  let treeIdx := leafGid / leavesPerTree
  let desc := trees treeIdx
  let (_, pkSeed) := keys desc.keyIdx
  let adrs := { { Adrs.zero with layer := desc.layer, tree := desc.tree }.setTypeAndClear WOTS_PK with
                keypair := leafIdx }
  let tips := (List.range p.len).foldl (fun acc c => acc ++ endpoints (leafGid * p.len + c)) []
  T p pkSeed adrs tips

/-- Composed two-phase XMSS leaf computation (`wots_chains` followed by `wots_tlen`). -/
def metalWotsTwoPhaseLeaf (p : Params) (keys : Nat → Bytes × Bytes)
    (trees : Nat → XmssTreeDesc) (leafGid : Nat) : Bytes :=
  metalWotsTlenKernel p keys trees (metalWotsChainsKernel p keys trees) leafGid

/-- Streaming XMSS leaf kernel (`xmss_leaves_streaming` / `shake_xmss_leaves_streaming`):
1 thread per leaf, zero intermediate chain-tips buffer. -/
def metalXmssLeavesStreaming (p : Params) (keys : Nat → Bytes × Bytes)
    (trees : Nat → XmssTreeDesc) (leafGid : Nat) : Bytes :=
  let leavesPerTree := 2 ^ p.hp
  let leafIdx := leafGid % leavesPerTree
  let treeIdx := leafGid / leavesPerTree
  let desc := trees treeIdx
  let (skSeed, pkSeed) := keys desc.keyIdx
  let adrs := { { Adrs.zero with layer := desc.layer, tree := desc.tree }.setTypeAndClear WOTS_PK with
                keypair := leafIdx }
  let tips := (List.range p.len).foldl
    (fun acc c => acc ++ metalRunWotsChain p skSeed pkSeed desc.layer desc.tree leafIdx c 15) []
  T p pkSeed adrs tips

/-- **Theorem 1a (`metal_wots_two_phase_eq_fips`)**:
Two-phase GPU WOTS+ (`wots_chains` + `wots_tlen`) produces exact `Spec.wotsPkGen`
(and `Spec.xmssNode ... 0`) for every valid parameter set (all 12 SHA-2 and SHAKE sets). -/
theorem metal_wots_two_phase_eq_fips (p : Params) (hv : p.Valid)
    (keys : Nat → Bytes × Bytes) (trees : Nat → XmssTreeDesc)
    (treeIdx leafIdx : Nat) (hleaf : leafIdx < 2 ^ p.hp) :
    let desc := trees treeIdx
    let (skSeed, pkSeed) := keys desc.keyIdx
    let treeAdrs : Adrs := { Adrs.zero with layer := desc.layer, tree := desc.tree }
    metalWotsTwoPhaseLeaf p keys trees (treeIdx * 2 ^ p.hp + leafIdx) =
      wotsPkGen p skSeed pkSeed { treeAdrs.setTypeAndClear WOTS_HASH with keypair := leafIdx } := by
  have ⟨hw, _, _, _⟩ := valid_wots_params hv
  have hdec2 := gid_decode_2 (a := treeIdx) (b := leafIdx) (stride := 2 ^ p.hp) hleaf
  dsimp only [metalWotsTwoPhaseLeaf, metalWotsTlenKernel, wotsPkGen]
  rw [hdec2.1, hdec2.2, append_foldl_eq, List.nil_append]
  have hpk : wotsPkAdrs { ({ Adrs.zero with layer := (trees treeIdx).layer, tree := (trees treeIdx).tree }.setTypeAndClear WOTS_HASH) with keypair := leafIdx } =
      { ({ Adrs.zero with layer := (trees treeIdx).layer, tree := (trees treeIdx).tree }.setTypeAndClear WOTS_PK) with keypair := leafIdx } := by
    simp [wotsPkAdrs, Adrs.setTypeAndClear]
  rw [hpk]
  apply congrArg (T p (keys (trees treeIdx).keyIdx).2 _)
  apply flatMap_congr'
  intro c hc
  rw [List.mem_range] at hc
  have hdec3 := gid_decode_3 (treeIdx := treeIdx) (leafIdx := leafIdx) (chain := c)
    (leavesPerTree := 2 ^ p.hp) (wotsLen := p.len) hleaf hc
  dsimp only [metalWotsChainsKernel, metalRunWotsChain]
  rw [hdec3.1, hdec3.2.1, hdec3.2.2, hw]

/-- Streaming XMSS leaf kernel produces exact `Spec.wotsPkGen`. -/
theorem metal_wots_streaming_eq_fips (p : Params) (hv : p.Valid)
    (keys : Nat → Bytes × Bytes) (trees : Nat → XmssTreeDesc)
    (treeIdx leafIdx : Nat) (hleaf : leafIdx < 2 ^ p.hp) :
    let desc := trees treeIdx
    let (skSeed, pkSeed) := keys desc.keyIdx
    let treeAdrs : Adrs := { Adrs.zero with layer := desc.layer, tree := desc.tree }
    metalXmssLeavesStreaming p keys trees (treeIdx * 2 ^ p.hp + leafIdx) =
      wotsPkGen p skSeed pkSeed { treeAdrs.setTypeAndClear WOTS_HASH with keypair := leafIdx } := by
  have ⟨hw, _, _, _⟩ := valid_wots_params hv
  have hdec2 := gid_decode_2 (a := treeIdx) (b := leafIdx) (stride := 2 ^ p.hp) hleaf
  dsimp only [metalXmssLeavesStreaming, wotsPkGen]
  rw [hdec2.1, hdec2.2, append_foldl_eq, List.nil_append]
  have hpk : wotsPkAdrs { ({ Adrs.zero with layer := (trees treeIdx).layer, tree := (trees treeIdx).tree }.setTypeAndClear WOTS_HASH) with keypair := leafIdx } =
      { ({ Adrs.zero with layer := (trees treeIdx).layer, tree := (trees treeIdx).tree }.setTypeAndClear WOTS_PK) with keypair := leafIdx } := by
    simp [wotsPkAdrs, Adrs.setTypeAndClear]
  rw [hpk]
  apply congrArg (T p (keys (trees treeIdx).keyIdx).2 _)
  apply flatMap_congr'
  intro c _
  dsimp only [metalRunWotsChain]
  rw [hw]

/-- Two-phase and streaming XMSS leaf kernels are bit-for-bit identical. -/
theorem metal_wots_two_phase_eq_streaming (p : Params) (hv : p.Valid)
    (keys : Nat → Bytes × Bytes) (trees : Nat → XmssTreeDesc) (leafGid : Nat) :
    metalWotsTwoPhaseLeaf p keys trees leafGid =
      metalXmssLeavesStreaming p keys trees leafGid := by
  have hpos : 0 < 2 ^ p.hp := Nat.two_pow_pos p.hp
  have hlt : leafGid % 2 ^ p.hp < 2 ^ p.hp := Nat.mod_lt leafGid hpos
  have heq : (leafGid / 2 ^ p.hp) * 2 ^ p.hp + leafGid % 2 ^ p.hp = leafGid := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod leafGid (2 ^ p.hp)
  rw [← heq, metal_wots_two_phase_eq_fips p hv keys trees _ _ hlt,
      metal_wots_streaming_eq_fips p hv keys trees _ _ hlt]

/-- Parallel per-chain WOTS+ signing kernel (`wots_sign` / `shake_wots_sign`):
thread `gid = layerGlobal * wotsLen + c` computes chain `c` with `digits[c]` steps. -/
def metalWotsSignChain (p : Params) (skSeed pkSeed msg : Bytes)
    (layer tree keypair c : Nat) : Bytes :=
  let digits := wotsDigits p msg
  metalRunWotsChain p skSeed pkSeed layer tree keypair c digits[c]!

/-- Assembling all `p.len` parallel chains from `wots_sign` equals `Spec.wotsSign`. -/
theorem metal_wots_sign_eq_fips (p : Params) (skSeed pkSeed msg : Bytes)
    (layer tree keypair : Nat) :
    let treeAdrs : Adrs := { Adrs.zero with layer := layer, tree := tree }
    (List.range p.len).flatMap (metalWotsSignChain p skSeed pkSeed msg layer tree keypair) =
      wotsSign p msg skSeed pkSeed { treeAdrs.setTypeAndClear WOTS_HASH with keypair := keypair } := by
  dsimp only [wotsSign]
  apply flatMap_congr'
  intro c _
  rfl

/-! ## Part 2: GPU Bottom-Up Threadgroup Merkle Reduction (`xmss_reduce`) -/

/-- One barrier-separated parallel reduction step in threadgroup memory:
every thread `tid < curCnt` reads `tg(2*tid)` and `tg(2*tid + 1)`, hashes into a
private register, synchronizes at barrier 1, writes `tg(tid)`, and synchronizes at
barrier 2. Threads `tid ≥ curCnt` leave `tg(tid)` untouched. -/
def tgReduceStep (hash : Nat → Bytes → Bytes → Bytes) (curCnt : Nat)
    (tg : Nat → Bytes) : Nat → Bytes :=
  fun tid => if tid < curCnt then hash tid (tg (2 * tid)) (tg (2 * tid + 1)) else tg tid

/-- State of threadgroup memory `tg_nodes` in `xmss_reduce` / `shake_xmss_reduce`
after completing level `lvl` (`0 ≤ lvl ≤ hp`). -/
def metalXmssReduceState (p : Params) (pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes) : Nat → (Nat → Bytes)
  | 0 => leaves
  | lvl + 1 =>
    let curCnt := 2 ^ (p.hp - (lvl + 1))
    let hFn := fun tid l r =>
      H p pkSeed { treeAdrs.setTypeAndClear TREE with word2 := lvl + 1, word3 := tid } (l ++ r)
    tgReduceStep hFn curCnt (metalXmssReduceState p pkSeed treeAdrs leaves lvl)

/-- Authentication sibling written by `xmss_reduce` at height `h ∈ 0..hp`:
- `h = 0`: `tid == 0` reads `leaves[targetLeaf ^^^ 1]`
- `h ≥ 1` (emitted at loop iteration `lvl = h + 1`): thread `tid == (targetLeaf >>> h) ^^^ 1`
  reads `tg_nodes[tid]` from the state at level `h`. -/
def metalXmssReduceAuthNode (p : Params) (pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes) (targetLeaf h : Nat) : Bytes :=
  let sib := (targetLeaf >>> h) ^^^ 1
  metalXmssReduceState p pkSeed treeAdrs leaves h sib

/-- Root output written by thread 0 after `lvl = p.hp`. -/
def metalXmssReduceRoot (p : Params) (pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes) : Bytes :=
  metalXmssReduceState p pkSeed treeAdrs leaves p.hp 0

/-- Complete auth-path byte string written by `xmss_reduce` to `auth_byte_off`. -/
def metalXmssReduceAuth (p : Params) (pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes) (targetLeaf : Nat) : Bytes :=
  (List.range p.hp).flatMap (metalXmssReduceAuthNode p pkSeed treeAdrs leaves targetLeaf)

/-- Level-by-level invariant: after level `lvl ≤ p.hp`, every active slot `i < 2^(p.hp - lvl)`
holds exact `Spec.xmssNode p skSeed i lvl pkSeed treeAdrs`. -/
theorem metal_xmss_reduce_level_eq_fips (p : Params) (skSeed pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes)
    (hleaves : ∀ i < 2 ^ p.hp, leaves i = xmssNode p skSeed i 0 pkSeed treeAdrs) :
    ∀ lvl ≤ p.hp, ∀ i < 2 ^ (p.hp - lvl),
      metalXmssReduceState p pkSeed treeAdrs leaves lvl i = xmssNode p skSeed i lvl pkSeed treeAdrs := by
  intro lvl
  induction lvl with
  | zero =>
    intro _ i hi
    simpa [metalXmssReduceState] using hleaves i hi
  | succ lvl ih =>
    intro hlvl i hi
    simp only [metalXmssReduceState, tgReduceStep, hi, ↓reduceIte]
    have hpow : 2 ^ (p.hp - lvl) = 2 * 2 ^ (p.hp - (lvl + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h2i : 2 * i < 2 ^ (p.hp - lvl) := by omega
    have h2i1 : 2 * i + 1 < 2 ^ (p.hp - lvl) := by omega
    rw [ih (by omega) (2 * i) h2i, ih (by omega) (2 * i + 1) h2i1]
    rfl

/-- Every auth sibling extracted at height `h` (`1 ≤ h < p.hp`) is owned by a live thread
`tid < 2^(p.hp - 1)` in the `xmss_reduce` threadgroup. -/
theorem metal_xmss_reduce_auth_in_bounds (p : Params) (targetLeaf h : Nat)
    (htarget : targetLeaf < 2 ^ p.hp) (hh : h < p.hp) :
    ((targetLeaf >>> h) ^^^ 1) < 2 ^ (p.hp - h) ∧
    (1 ≤ h → ((targetLeaf >>> h) ^^^ 1) < 2 ^ (p.hp - 1)) := by
  have hdiv : targetLeaf >>> h < 2 ^ (p.hp - h) := by
    rw [Nat.shiftRight_eq_div_pow]
    have hmul : 2 ^ p.hp = 2 ^ (p.hp - h) * 2 ^ h := by rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h), ← hmul]
    exact htarget
  have h1 : ((targetLeaf >>> h) ^^^ 1) < 2 ^ (p.hp - h) := xor_one_lt_two_pow (by omega) hdiv
  refine ⟨h1, fun hh1 => ?_⟩
  have hle : 2 ^ (p.hp - h) ≤ 2 ^ (p.hp - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Theorem 2 (`metal_xmss_reduce_eq_fips`)**:
Iterative bottom-up pairwise `H` reduction in threadgroup memory computes:
1. exact `Spec.xmssNode p skSeed i lvl pkSeed treeAdrs` at every level `0..=hp`,
2. exact root `Spec.xmssNode p skSeed 0 p.hp pkSeed treeAdrs` at level `hp`, and
3. exact authentication path `(targetLeaf >>> h) ^^^ 1` for `h ∈ 0..hp`! -/
theorem metal_xmss_reduce_eq_fips (p : Params) (skSeed pkSeed : Bytes) (treeAdrs : Adrs)
    (leaves : Nat → Bytes)
    (hleaves : ∀ i < 2 ^ p.hp, leaves i = xmssNode p skSeed i 0 pkSeed treeAdrs)
    (targetLeaf : Nat) (htarget : targetLeaf < 2 ^ p.hp) :
    (∀ lvl ≤ p.hp, ∀ i < 2 ^ (p.hp - lvl),
      metalXmssReduceState p pkSeed treeAdrs leaves lvl i = xmssNode p skSeed i lvl pkSeed treeAdrs) ∧
    metalXmssReduceRoot p pkSeed treeAdrs leaves = xmssNode p skSeed 0 p.hp pkSeed treeAdrs ∧
    metalXmssReduceAuth p pkSeed treeAdrs leaves targetLeaf =
      (List.range p.hp).flatMap (fun h => xmssNode p skSeed ((targetLeaf / 2 ^ h) ^^^ 1) h pkSeed treeAdrs) := by
  have hlevels := metal_xmss_reduce_level_eq_fips p skSeed pkSeed treeAdrs leaves hleaves
  refine ⟨hlevels, ?_, ?_⟩
  · simpa [metalXmssReduceRoot] using hlevels p.hp (le_refl _) 0 (by simp)
  · unfold metalXmssReduceAuth
    apply flatMap_congr'
    intro h hh
    rw [List.mem_range] at hh
    have hlt := (metal_xmss_reduce_auth_in_bounds p targetLeaf h htarget hh).1
    unfold metalXmssReduceAuthNode
    rw [hlevels h (by omega) _ hlt, Nat.shiftRight_eq_div_pow]

/-! ## Part 3: 2-Leaf-Per-Thread Two-Pass FORS Decomposition (`fors_pass1` + `fors_pass2` + `fors_pk`) -/

/-- The split policy used in `metal/src/lib.rs`:
`s1 = if p.a ≤ 8 then p.a else 7`, `s2 = p.a - s1`. -/
def forsSplit (p : Params) : Nat × Nat :=
  let s1 := if p.a ≤ 8 then p.a else 7
  (s1, p.a - s1)

theorem forsSplit_valid {p : Params} (hv : p.Valid) :
    1 ≤ (forsSplit p).1 ∧ (forsSplit p).1 + (forsSplit p).2 = p.a := by
  have ha1 := hv.a_pos
  have ha2 := hv.a_le
  unfold forsSplit
  by_cases h : p.a ≤ 8 <;> simp [h] <;> omega

/-- Threadgroup reduction inside a single height-`s1` FORS subtree `(treeIdx, stLocal)`
in `fors_pass1` / `shake_fors_pass1`. -/
def metalForsPass1State (p : Params) (s1 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx stLocal : Nat) : Nat → (Nat → Bytes)
  | 0 => fun localLeaf =>
      let word3 := (treeIdx <<< p.a) + (stLocal <<< s1) + localLeaf
      let sk := forsSkGen p skSeed pkSeed adrs word3
      F p pkSeed { adrs with word2 := 0, word3 := word3 } sk
  | lvl + 1 =>
      let curCnt := 2 ^ (s1 - (lvl + 1))
      let hFn := fun tid l r =>
        let word3 := (treeIdx <<< (p.a - (lvl + 1))) + (stLocal <<< (s1 - (lvl + 1))) + tid
        H p pkSeed { adrs with word2 := lvl + 1, word3 := word3 } (l ++ r)
      tgReduceStep hFn curCnt (metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal lvl)

/-- Subtree root written by thread 0 at the end of `fors_pass1` to `out_sub_roots`. -/
def metalForsPass1SubRoot (p : Params) (s1 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx stLocal : Nat) : Bytes :=
  metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal s1 0

/-- Secret value `sk` emitted by the unique thread in `fors_pass1` owning `target`. -/
def metalForsPass1Secret (p : Params) (s1 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx target : Nat) : Bytes :=
  let stLocal := target >>> s1
  let tid := (target % 2 ^ s1) / 2
  let leaf0InTree := (stLocal <<< s1) + 2 * tid
  let leaf0Word3 := (treeIdx <<< p.a) + leaf0InTree
  let leaf1Word3 := leaf0Word3 + 1
  if leaf0InTree = target then forsSkGen p skSeed pkSeed adrs leaf0Word3
  else forsSkGen p skSeed pkSeed adrs leaf1Word3

/-- Authentication node emitted by `fors_pass1` for height `h < s1`. -/
def metalForsPass1AuthNode (p : Params) (s1 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx target h : Nat) : Bytes :=
  let stLocal := target >>> s1
  if h = 0 then
    let tid := (target % 2 ^ s1) / 2
    let leaf0InTree := (stLocal <<< s1) + 2 * tid
    if leaf0InTree = target then
      metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal 0 (2 * tid + 1)
    else
      metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal 0 (2 * tid)
  else
    let sibInTree := (target >>> h) ^^^ 1
    let mask := (1 <<< (s1 - h)) - 1
    let sibLocal := sibInTree &&& mask
    metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal h sibLocal

/-- Threadgroup reduction of the `2^s2` subtree roots in `fors_pass2` / `shake_fors_pass2`
(when `s2 > 0`; when `s2 = 0`, `step = 0` directly returns `subRoots 0`). -/
def metalForsPass2State (p : Params) (s1 s2 : Nat) (pkSeed : Bytes) (adrs : Adrs)
    (treeIdx : Nat) (subRoots : Nat → Bytes) : Nat → (Nat → Bytes)
  | 0 => subRoots
  | step + 1 =>
      let lvl := s1 + (step + 1)
      let curCnt := 2 ^ (s2 - (step + 1))
      let hFn := fun tid l r =>
        let word3 := (treeIdx <<< (p.a - lvl)) + tid
        H p pkSeed { adrs with word2 := lvl, word3 := word3 } (l ++ r)
      tgReduceStep hFn curCnt (metalForsPass2State p s1 s2 pkSeed adrs treeIdx subRoots step)

/-- Final FORS tree root for tree `treeIdx` after `fors_pass1` (+ `fors_pass2` if `s2 > 0`). -/
def metalForsTreeRoot (p : Params) (s1 s2 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx : Nat) : Bytes :=
  let subRoots := metalForsPass1SubRoot p s1 skSeed pkSeed adrs treeIdx
  metalForsPass2State p s1 s2 pkSeed adrs treeIdx subRoots s2 0

/-- Authentication node emitted by `fors_pass2` for height `h` (`s1 ≤ h < a`). -/
def metalForsPass2AuthNode (p : Params) (s1 s2 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx target h : Nat) : Bytes :=
  let subRoots := metalForsPass1SubRoot p s1 skSeed pkSeed adrs treeIdx
  let sib := (target >>> h) ^^^ 1
  metalForsPass2State p s1 s2 pkSeed adrs treeIdx subRoots (h - s1) sib

/-- Combined authentication node at height `h ∈ 0..p.a` emitted by `fors_pass1` (`h < s1`)
and `fors_pass2` (`s1 ≤ h < p.a`). -/
def metalForsAuthNode (p : Params) (s1 s2 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx target h : Nat) : Bytes :=
  if h < s1 then metalForsPass1AuthNode p s1 skSeed pkSeed adrs treeIdx target h
  else metalForsPass2AuthNode p s1 s2 skSeed pkSeed adrs treeIdx target h

/-- Complete FORS signature emitted by `fors_pass1` + `fors_pass2` across all `p.k` trees. -/
def metalForsSig (p : Params) (s1 s2 : Nat) (md skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let indices := base2b md p.a p.k
  (List.range p.k).flatMap fun i =>
    let target := indices[i]!
    metalForsPass1Secret p s1 skSeed pkSeed adrs i target ++
      (List.range p.a).flatMap (metalForsAuthNode p s1 s2 skSeed pkSeed adrs i target)

/-- `fors_pk` / `shake_fors_pk`: compresses the `p.k` FORS tree roots with `T_k` and `FORS_ROOTS`. -/
def metalForsPk (p : Params) (s1 s2 : Nat) (skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let roots := (List.range p.k).flatMap (metalForsTreeRoot p s1 s2 skSeed pkSeed adrs)
  T p pkSeed { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair } roots

/-- Level-by-level invariant for `fors_pass1`. -/
theorem metal_fors_pass1_level_eq_fips (p : Params) (s1 s2 : Nat)
    (hsplit : s1 + s2 = p.a) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx stLocal : Nat) :
    ∀ lvl ≤ s1, ∀ i < 2 ^ (s1 - lvl),
      metalForsPass1State p s1 skSeed pkSeed adrs treeIdx stLocal lvl i =
        forsNode p skSeed (treeIdx * 2 ^ (p.a - lvl) + stLocal * 2 ^ (s1 - lvl) + i) lvl pkSeed adrs := by
  intro lvl
  induction lvl with
  | zero =>
    intro _ i _
    simp [metalForsPass1State, forsNode, Nat.shiftLeft_eq]
  | succ lvl ih =>
    intro hlvl i hi
    simp only [metalForsPass1State, tgReduceStep, hi, ↓reduceIte]
    have hpow_s1 : 2 ^ (s1 - lvl) = 2 * 2 ^ (s1 - (lvl + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hpow_a : 2 ^ (p.a - lvl) = 2 * 2 ^ (p.a - (lvl + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h2i : 2 * i < 2 ^ (s1 - lvl) := by omega
    have h2i1 : 2 * i + 1 < 2 ^ (s1 - lvl) := by omega
    rw [ih (by omega) (2 * i) h2i, ih (by omega) (2 * i + 1) h2i1]
    simp only [forsNode, Nat.shiftLeft_eq]
    have hidx : 2 * (treeIdx * 2 ^ (p.a - (lvl + 1)) + stLocal * 2 ^ (s1 - (lvl + 1)) + i) =
        treeIdx * 2 ^ (p.a - lvl) + stLocal * 2 ^ (s1 - lvl) + 2 * i := by
      rw [hpow_a, hpow_s1]; ring
    rw [hidx]
    simp only [Nat.add_assoc]

/-- Subtree root computed by `fors_pass1` equals `Spec.forsNode` at height `s1`. -/
theorem metal_fors_pass1_subroot_eq_fips (p : Params) (s1 s2 : Nat)
    (hsplit : s1 + s2 = p.a) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx stLocal : Nat) :
    metalForsPass1SubRoot p s1 skSeed pkSeed adrs treeIdx stLocal =
      forsNode p skSeed (treeIdx * 2 ^ s2 + stLocal) s1 pkSeed adrs := by
  have h := metal_fors_pass1_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx stLocal s1 (le_refl _) 0 (by simp)
  simpa [metalForsPass1SubRoot, show p.a - s1 = s2 by omega] using h

/-- Level-by-level invariant for `fors_pass2`. -/
theorem metal_fors_pass2_level_eq_fips (p : Params) (s1 s2 : Nat)
    (hsplit : s1 + s2 = p.a) (skSeed pkSeed : Bytes) (adrs : Adrs) (treeIdx : Nat) :
    ∀ step ≤ s2, ∀ i < 2 ^ (s2 - step),
      metalForsPass2State p s1 s2 pkSeed adrs treeIdx
        (metalForsPass1SubRoot p s1 skSeed pkSeed adrs treeIdx) step i =
      forsNode p skSeed (treeIdx * 2 ^ (p.a - (s1 + step)) + i) (s1 + step) pkSeed adrs := by
  intro step
  induction step with
  | zero =>
    intro _ i _
    simpa [metalForsPass2State, show p.a - s1 = s2 by omega] using
      metal_fors_pass1_subroot_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx i
  | succ step ih =>
    intro hstep i hi
    simp only [metalForsPass2State, tgReduceStep, hi, ↓reduceIte]
    have hpow_s2 : 2 ^ (s2 - step) = 2 * 2 ^ (s2 - (step + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hpow_a : 2 ^ (p.a - (s1 + step)) = 2 * 2 ^ (p.a - (s1 + step + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h2i : 2 * i < 2 ^ (s2 - step) := by omega
    have h2i1 : 2 * i + 1 < 2 ^ (s2 - step) := by omega
    rw [ih (by omega) (2 * i) h2i, ih (by omega) (2 * i + 1) h2i1]
    have hlvl : s1 + (step + 1) = (s1 + step) + 1 := by omega
    rw [hlvl]
    simp only [forsNode, Nat.shiftLeft_eq]
    have hidx : 2 * (treeIdx * 2 ^ (p.a - (s1 + step + 1)) + i) =
        treeIdx * 2 ^ (p.a - (s1 + step)) + 2 * i := by
      rw [hpow_a]; ring
    rw [hidx]
    simp only [Nat.add_assoc]

/-- Tree root computed by `fors_pass1` + `fors_pass2` equals `Spec.forsNode p sk treeIdx p.a pk adrs`. -/
theorem metal_fors_tree_root_eq_fips (p : Params) (s1 s2 : Nat)
    (hsplit : s1 + s2 = p.a) (skSeed pkSeed : Bytes) (adrs : Adrs) (treeIdx : Nat) :
    metalForsTreeRoot p s1 s2 skSeed pkSeed adrs treeIdx =
      forsNode p skSeed treeIdx p.a pkSeed adrs := by
  have h := metal_fors_pass2_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx s2 (le_refl _) 0 (by simp)
  simpa [metalForsTreeRoot, hsplit] using h

/-- The 2-leaf-per-thread secret selection in `fors_pass1` emits exact `Spec.forsSkGen`. -/
theorem metal_fors_pass1_secret_eq_fips (p : Params) (s1 : Nat)
    (skSeed pkSeed : Bytes) (adrs : Adrs) (treeIdx target : Nat) :
    metalForsPass1Secret p s1 skSeed pkSeed adrs treeIdx target =
      forsSkGen p skSeed pkSeed adrs (treeIdx * 2 ^ p.a + target) := by
  unfold metalForsPass1Secret
  dsimp only
  have hdm : (target >>> s1) <<< s1 + target % 2 ^ s1 = target := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact Nat.div_add_mod target (2 ^ s1)
  have h2div := Nat.div_add_mod (target % 2 ^ s1) 2
  have hsh : treeIdx <<< p.a = treeIdx * 2 ^ p.a := Nat.shiftLeft_eq _ _
  split
  · rename_i heq
    rw [heq, hsh]
  · rename_i hne
    have hodd : target % 2 ^ s1 % 2 = 1 := by omega
    have hl1 : (target >>> s1) <<< s1 + 2 * (target % 2 ^ s1 / 2) + 1 = target := by omega
    rw [hsh, Nat.add_assoc, hl1]

/-- Every authentication node `h ∈ 0..p.a` emitted by `fors_pass1` (`h < s1`) and `fors_pass2`
(`s1 ≤ h < p.a`) equals the exact FIPS 205 FORS sibling node. -/
theorem metal_fors_auth_node_eq_fips (p : Params) (s1 s2 : Nat) (hs1 : 1 ≤ s1)
    (hsplit : s1 + s2 = p.a) (skSeed pkSeed : Bytes) (adrs : Adrs)
    (treeIdx target h : Nat) (htarget : target < 2 ^ p.a) (hh : h < p.a) :
    metalForsAuthNode p s1 s2 skSeed pkSeed adrs treeIdx target h =
      forsNode p skSeed (treeIdx * 2 ^ (p.a - h) + ((target / 2 ^ h) ^^^ 1)) h pkSeed adrs := by
  unfold metalForsAuthNode
  by_cases hlt : h < s1
  · simp only [hlt, ↓reduceIte]
    unfold metalForsPass1AuthNode
    dsimp only
    by_cases h0 : h = 0
    · subst h0
      simp only [↓reduceIte, Nat.sub_zero, Nat.pow_zero, Nat.div_one]
      have hdm : (target >>> s1) <<< s1 + target % 2 ^ s1 = target := by
        rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
        exact Nat.div_add_mod target (2 ^ s1)
      have h2div := Nat.div_add_mod (target % 2 ^ s1) 2
      have h2s1_even : 2 ^ s1 % 2 = 0 := by
        have : 2 ^ s1 = 2 * 2 ^ (s1 - 1) := by rw [← Nat.pow_succ']; congr 1; omega
        omega
      have hmul_even : (2 ^ s1 * (target / 2 ^ s1)) % 2 = 0 := by
        rw [Nat.mul_mod, h2s1_even]; simp
      have hmod2 : (target % 2 ^ s1) % 2 = target % 2 := by
        have : target = 2 ^ s1 * (target / 2 ^ s1) + target % 2 ^ s1 := (Nat.div_add_mod _ _).symm
        omega
      have hlt0 : 2 * (target % 2 ^ s1 / 2) < 2 ^ s1 := by
        have := Nat.mod_lt target (Nat.two_pow_pos s1); omega
      have hlt1 : 2 * (target % 2 ^ s1 / 2) + 1 < 2 ^ s1 := by
        have := Nat.mod_lt target (Nat.two_pow_pos s1); omega
      have hst : (target >>> s1) * 2 ^ s1 = (target >>> s1) <<< s1 := (Nat.shiftLeft_eq _ _).symm
      split
      · rename_i heq
        rw [metal_fors_pass1_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx (target >>> s1) 0 (by omega) _ hlt1]
        have heven : target % 2 = 0 := by omega
        have hxor : target ^^^ 1 = target + 1 := by rw [xor_one_eq]; simp [heven]
        rw [hxor, Nat.sub_zero, Nat.sub_zero, hst]
        congr 1; omega
      · rename_i hne
        rw [metal_fors_pass1_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx (target >>> s1) 0 (by omega) _ hlt0]
        have hodd : target % 2 = 1 := by omega
        have hxor : target ^^^ 1 = target - 1 := by rw [xor_one_eq]; simp [hodd]
        rw [hxor, Nat.sub_zero, Nat.sub_zero, hst]
        congr 1; omega
    · simp only [h0, ↓reduceIte]
      have hmask : ((1 <<< (s1 - h)) - 1) = 2 ^ (s1 - h) - 1 := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
      have hmod_lt : ((target >>> h) ^^^ 1) % 2 ^ (s1 - h) < 2 ^ (s1 - h) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      rw [metal_fors_pass1_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx (target >>> s1) h (by omega) _ hmod_lt]
      congr 1
      rw [Nat.add_assoc]
      congr 1
      have hdiv_st : ((target >>> h) ^^^ 1) / 2 ^ (s1 - h) = target >>> s1 := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
            xor_one_div_two_pow (by omega : 1 ≤ s1 - h), Nat.div_div_eq_div_mul, ← Nat.pow_add]
        congr 2; omega
      rw [← hdiv_st, Nat.mul_comm, Nat.div_add_mod, Nat.shiftRight_eq_div_pow]
  · simp only [hlt, ↓reduceIte]
    unfold metalForsPass2AuthNode
    dsimp only
    have hdiv_lt : target >>> h < 2 ^ (s2 - (h - s1)) := by
      rw [Nat.shiftRight_eq_div_pow]
      have hmul : 2 ^ p.a = 2 ^ (s2 - (h - s1)) * 2 ^ h := by rw [← Nat.pow_add]; congr 1; omega
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h), ← hmul]
      exact htarget
    have hsib_lt : (target >>> h) ^^^ 1 < 2 ^ (s2 - (h - s1)) :=
      xor_one_lt_two_pow (by omega) hdiv_lt
    rw [metal_fors_pass2_level_eq_fips p s1 s2 hsplit skSeed pkSeed adrs treeIdx (h - s1) (by omega) _ hsib_lt]
    have hadd : s1 + (h - s1) = h := by omega
    rw [hadd, Nat.shiftRight_eq_div_pow]

/-- **Theorem 3 (`metal_fors_two_pass_eq_fips`)**:
The 2-leaf-per-thread two-pass FORS decomposition (`fors_pass1` + `fors_pass2` + `fors_pk`)
produces:
1. the exact FIPS 205 `Spec.forsSign` signature bytes, AND
2. the exact FIPS 205 `Spec.forsPkFromSig` public key! -/
theorem metal_fors_two_pass_eq_fips (p : Params) (hv : p.Valid)
    (s1 s2 : Nat) (hs1 : 1 ≤ s1) (hsplit : s1 + s2 = p.a)
    (md skSeed pkSeed : Bytes) (adrs : Adrs) :
    metalForsSig p s1 s2 md skSeed pkSeed adrs = forsSign p md skSeed pkSeed adrs ∧
    metalForsPk p s1 s2 skSeed pkSeed adrs =
      forsPkFromSig p (forsSign p md skSeed pkSeed adrs) md pkSeed adrs := by
  constructor
  · unfold metalForsSig forsSign
    apply flatMap_congr'
    intro i hi
    rw [List.mem_range] at hi
    have htarget : (base2b md p.a p.k)[i]! < 2 ^ p.a := base2b_getElem!_lt md p.a p.k i hi
    dsimp only
    rw [metal_fors_pass1_secret_eq_fips p s1 skSeed pkSeed adrs i _]
    apply congrArg (_ ++ ·)
    apply flatMap_congr'
    intro h hh
    rw [List.mem_range] at hh
    exact metal_fors_auth_node_eq_fips p s1 s2 hs1 hsplit skSeed pkSeed adrs i _ h htarget hh
  · rw [fors_correct p hv md skSeed pkSeed adrs]
    unfold metalForsPk
    apply congrArg (T p pkSeed _)
    apply flatMap_congr'
    intro i _
    exact metal_fors_tree_root_eq_fips p s1 s2 hsplit skSeed pkSeed adrs i

/-! ## Part 4: Composed GPU Keygen & Single/Batched Signer -/

/-- XMSS leaf computation mode selected by `MetalSigner::use_two_phase`. -/
inductive XmssMode where
  | twoPhase
  | streaming
deriving Repr, DecidableEq

/-- Unified XMSS leaf dispatch selecting either two-phase (`wots_chains` + `wots_tlen`)
or streaming (`xmss_leaves_streaming`). -/
def metalXmssLeaves (mode : XmssMode) (p : Params) (keys : Nat → Bytes × Bytes)
    (trees : Nat → XmssTreeDesc) (leafGid : Nat) : Bytes :=
  match mode with
  | .twoPhase => metalWotsTwoPhaseLeaf p keys trees leafGid
  | .streaming => metalXmssLeavesStreaming p keys trees leafGid

theorem metalXmssLeaves_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (keys : Nat → Bytes × Bytes) (trees : Nat → XmssTreeDesc)
    (treeIdx leafIdx : Nat) (hleaf : leafIdx < 2 ^ p.hp) :
    let desc := trees treeIdx
    let (skSeed, pkSeed) := keys desc.keyIdx
    let treeAdrs : Adrs := { Adrs.zero with layer := desc.layer, tree := desc.tree }
    metalXmssLeaves mode p keys trees (treeIdx * 2 ^ p.hp + leafIdx) =
      xmssNode p skSeed leafIdx 0 pkSeed treeAdrs := by
  cases mode with
  | twoPhase => exact metal_wots_two_phase_eq_fips p hv keys trees treeIdx leafIdx hleaf
  | streaming => exact metal_wots_streaming_eq_fips p hv keys trees treeIdx leafIdx hleaf

/-- Hypertree layer coordinates `(tree_j, leaf_j)` built by the CPU host loop in
`sign_internal_batch_family` (`metal/src/lib.rs` lines 988–1011). -/
def htLoc (hp t l : Nat) : Nat → Nat × Nat
  | 0 => (t, l)
  | j + 1 =>
    let tree := (htLoc hp t l j).1
    (tree >>> hp, tree % 2 ^ hp)

/-- Input message signed by WOTS+ at hypertree layer `j` in `wots_sign`:
layer 0 reads `pk_fors[sig_idx]`, layer `j > 0` reads `xmss_roots[sig_idx * d + (j - 1)]`. -/
def metalLayerMsg (pkFors : Bytes) (xmssRoots : Nat → Bytes) : Nat → Bytes
  | 0 => pkFors
  | j + 1 => xmssRoots j

/-- Composed GPU keygen (`keygen_internal_batch_family`) for a single keypair. -/
def metalKeygenInternal (mode : XmssMode) (p : Params) (skSeed skPrf pkSeed : Bytes) :
    Bytes × Bytes :=
  let keys : Nat → Bytes × Bytes := fun _ => (skSeed, pkSeed)
  let trees : Nat → XmssTreeDesc := fun _ =>
    { tree := 0, keyIdx := 0, layer := p.d - 1, targetLeaf := none, authByteOff := 0 }
  let leaves := fun i => metalXmssLeaves mode p keys trees i
  let topAdrs : Adrs := { Adrs.zero with layer := p.d - 1, tree := 0 }
  let pkRoot := metalXmssReduceRoot p pkSeed topAdrs leaves
  (skSeed ++ skPrf ++ pkSeed ++ pkRoot, pkSeed ++ pkRoot)

/-- **Theorem 4a (`metal_keygen_eq_fips`)**:
The composed GPU keygen pipeline (both two-phase and streaming XMSS modes) produces
exact FIPS 205 `Spec.slhKeygenInternal` for every valid parameter set. -/
theorem metal_keygen_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (skSeed skPrf pkSeed : Bytes) :
    metalKeygenInternal mode p skSeed skPrf pkSeed =
      slhKeygenInternal p skSeed skPrf pkSeed := by
  unfold metalKeygenInternal slhKeygenInternal
  dsimp only
  have hleaves : ∀ i < 2 ^ p.hp,
      metalXmssLeaves mode p (fun _ => (skSeed, pkSeed))
        (fun _ => { tree := 0, keyIdx := 0, layer := p.d - 1, targetLeaf := none, authByteOff := 0 }) i =
      xmssNode p skSeed i 0 pkSeed { Adrs.zero with layer := p.d - 1, tree := 0 } := by
    intro i hi
    simpa using metalXmssLeaves_eq_fips mode p hv (fun _ => (skSeed, pkSeed))
      (fun _ => { tree := 0, keyIdx := 0, layer := p.d - 1, targetLeaf := none, authByteOff := 0 }) 0 i hi
  have hroot := (metal_xmss_reduce_eq_fips p skSeed pkSeed { Adrs.zero with layer := p.d - 1, tree := 0 }
    _ hleaves 0 (Nat.two_pow_pos _)).2.1
  have hadrs : ({ Adrs.zero with layer := p.d - 1, tree := 0 } : Adrs) = { Adrs.zero with layer := p.d - 1 } := rfl
  rw [hroot, hadrs]

/-- Batch GPU keygen (`keygen_internal_batch_family`) over `batch : List (Bytes × Bytes × Bytes)`
executing all `B` top trees in a single command buffer. -/
def metalBatchKeygenInternal (mode : XmssMode) (p : Params)
    (batch : List (Bytes × Bytes × Bytes)) : List (Bytes × Bytes) :=
  let keys : Nat → Bytes × Bytes := fun i =>
    let item := batch[i]!
    (item.1, item.2.2)
  let trees : Nat → XmssTreeDesc := fun i =>
    { tree := 0, keyIdx := i, layer := p.d - 1, targetLeaf := none, authByteOff := 0 }
  let topAdrs : Adrs := { Adrs.zero with layer := p.d - 1, tree := 0 }
  (List.range batch.length).map fun i =>
    let (skSeed, skPrf, pkSeed) := batch[i]!
    let leaves := fun l => metalXmssLeaves mode p keys trees (i * 2 ^ p.hp + l)
    let pkRoot := metalXmssReduceRoot p pkSeed topAdrs leaves
    (skSeed ++ skPrf ++ pkSeed ++ pkRoot, pkSeed ++ pkRoot)

theorem metal_batch_keygen_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (batch : List (Bytes × Bytes × Bytes)) :
    metalBatchKeygenInternal mode p batch =
      batch.map (fun (skSeed, skPrf, pkSeed) => slhKeygenInternal p skSeed skPrf pkSeed) := by
  unfold metalBatchKeygenInternal
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range]
  have hi : i < batch.length := by simpa using hi2
  have hget : batch[i]! = batch[i] := by simp [hi]
  rcases hbi : batch[i] with ⟨skSeed, skPrf, pkSeed⟩
  rw [hbi] at hget
  rw [hget]
  dsimp only [slhKeygenInternal]
  have hleaves : ∀ l < 2 ^ p.hp,
      metalXmssLeaves mode p (fun k => let item := batch[k]!; (item.1, item.2.2))
        (fun k => { tree := 0, keyIdx := k, layer := p.d - 1, targetLeaf := none, authByteOff := 0 })
        (i * 2 ^ p.hp + l) =
      xmssNode p skSeed l 0 pkSeed { Adrs.zero with layer := p.d - 1, tree := 0 } := by
    intro l hl
    have h := metalXmssLeaves_eq_fips mode p hv (fun k => let item := batch[k]!; (item.1, item.2.2))
      (fun k => { tree := 0, keyIdx := k, layer := p.d - 1, targetLeaf := none, authByteOff := 0 }) i l hl
    dsimp only at h
    rw [hget] at h
    exact h
  have hroot := (metal_xmss_reduce_eq_fips p skSeed pkSeed { Adrs.zero with layer := p.d - 1, tree := 0 }
    _ hleaves 0 (Nat.two_pow_pos _)).2.1
  have hadrs : ({ Adrs.zero with layer := p.d - 1, tree := 0 } : Adrs) = { Adrs.zero with layer := p.d - 1 } := rfl
  rw [hroot, hadrs]

/-- Direct byte-offset writes of a single signature at offset `sigOff` inside `out_sigs`,
modeling the exact buffer writes performed by CPU (`R`), `fors_pass1` + `fors_pass2`
(FORS secret + auth nodes), `xmss_reduce` (layer auth paths), and `wots_sign`
(layer WOTS+ signatures). -/
def metalWriteSingleSig (mode : XmssMode) (p : Params) (buf : Bytes) (sigOff : Nat)
    (msg sk addrnd : Bytes) : Bytes :=
  let skSeed := block p sk 0
  let skPrf := block p sk 1
  let pkSeed := block p sk 2
  let pkRoot := block p sk 3
  let r := PRFmsg p skPrf addrnd msg
  let digest := Hmsg p r pkSeed pkRoot msg
  let md := digest.take p.mdBytes
  let idxTree := digestTree p digest
  let idxLeaf := digestLeaf p digest
  let (s1, s2) := forsSplit p
  let forsAdrs := { { Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let indices := base2b md p.a p.k
  -- Stage 0 (CPU): write R at [sigOff .. sigOff + N)
  let b0 := patchAt buf sigOff r
  -- Stage 1+2 (GPU FORS pass 1 + pass 2): write FORS tree i at sigOff + N + i*(1+a)*N
  let b1 := (List.range p.k).foldl (fun b treeIdx =>
    let treeOff := sigOff + p.n + treeIdx * (1 + p.a) * p.n
    let target := indices[treeIdx]!
    let b' := patchAt b treeOff (metalForsPass1Secret p s1 skSeed pkSeed forsAdrs treeIdx target)
    patchChunks b' (treeOff + p.n) p.n
      (metalForsAuthNode p s1 s2 skSeed pkSeed forsAdrs treeIdx target) p.a) b0
  -- Stage 1+2+3 (GPU XMSS leaves + reduce): compute roots and write auth paths
  let keys : Nat → Bytes × Bytes := fun _ => (skSeed, pkSeed)
  let trees : Nat → XmssTreeDesc := fun j =>
    let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
    let layerOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
    { tree := tree, keyIdx := 0, layer := j, targetLeaf := some leaf,
      authByteOff := layerOff + p.len * p.n }
  let xmssRoots := fun j =>
    let (tree, _) := htLoc p.hp idxTree idxLeaf j
    let leaves := fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l)
    metalXmssReduceRoot p pkSeed { Adrs.zero with layer := j, tree := tree } leaves
  let b2 := (List.range p.d).foldl (fun b j =>
    let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
    let layerOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
    let authOff := layerOff + p.len * p.n
    let leaves := fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l)
    patchChunks b authOff p.n
      (metalXmssReduceAuthNode p pkSeed { Adrs.zero with layer := j, tree := tree } leaves leaf) p.hp) b1
  -- Stage 3 (GPU fors_pk): compress k FORS roots into pk_fors
  let pkFors := metalForsPk p s1 s2 skSeed pkSeed forsAdrs
  -- Final Stage (GPU wots_sign): write WOTS+ chains for all d layers at layerOff + c*N
  (List.range p.d).foldl (fun b j =>
    let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
    let layerOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
    let layerMsg := metalLayerMsg pkFors xmssRoots j
    patchChunks b layerOff p.n (metalWotsSignChain p skSeed pkSeed layerMsg j tree leaf) p.len) b2

/-- Hypertree layer decomposition: signing layer `j` with the precomputed root of layer `j-1`
matches `Spec.htSign`. -/
theorem ht_layers_eq_spec (p : Params) (hv : p.Valid) (pkFors skSeed pkSeed : Bytes)
    (idxTree idxLeaf : Nat) (hleaf : idxLeaf < 2 ^ p.hp) :
    let xmssRoots := fun j =>
      xmssNode p skSeed 0 p.hp pkSeed { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
    (List.range p.d).flatMap (fun j =>
      let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
      xmssSign p (metalLayerMsg pkFors xmssRoots j) skSeed leaf pkSeed
        { Adrs.zero with layer := j, tree := tree }) =
    htSign p pkFors skSeed pkSeed idxTree idxLeaf := by
  dsimp only
  let xmssRoots := fun j =>
    xmssNode p skSeed 0 p.hp pkSeed { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
  let layerSig := fun j =>
    let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
    xmssSign p (metalLayerMsg pkFors xmssRoots j) skSeed leaf pkSeed
      { Adrs.zero with layer := j, tree := tree }
  suffices inv : ∀ c,
      (List.range c).foldl (htLayer p skSeed pkSeed) ([], pkFors, idxTree, idxLeaf) =
        ((List.range c).flatMap layerSig, metalLayerMsg pkFors xmssRoots c,
          htLoc p.hp idxTree idxLeaf c) ∧
      (htLoc p.hp idxTree idxLeaf c).2 < 2 ^ p.hp by
    exact (congrArg Prod.fst (inv p.d).1).symm
  intro c
  induction c with
  | zero => exact ⟨rfl, hleaf⟩
  | succ c ih =>
    rw [List.range_succ, List.foldl_append, ih.1]
    simp only [List.foldl_cons, List.foldl_nil, htLayer]
    rw [xmss_correct p hv _ _ _ _ _ ih.2]
    refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    simp only [List.flatMap_append, List.flatMap_singleton,
      layerSig, metalLayerMsg, xmssRoots, htLoc]

/-- Writing a single signature into `out_sigs` at `sigOff` produces `patchAt buf sigOff (slhSignInternal ...)`. -/
theorem metalWriteSingleSig_eq_patch (mode : XmssMode) (p : Params) (hv : p.Valid)
    (buf : Bytes) (sigOff : Nat) (msg sk addrnd : Bytes)
    (hfit : sigOff + p.sigBytes ≤ buf.length) :
    metalWriteSingleSig mode p buf sigOff msg sk addrnd =
      patchAt buf sigOff (slhSignInternal p msg sk addrnd) := by
  have hsig_parts := sigBytes_parts p hv
  have ⟨hs1, hsplit⟩ := forsSplit_valid hv
  unfold metalWriteSingleSig slhSignInternal
  dsimp only
  set skSeed := block p sk 0
  set skPrf := block p sk 1
  set pkSeed := block p sk 2
  set pkRoot := block p sk 3
  set r := PRFmsg p skPrf addrnd msg
  set digest := Hmsg p r pkSeed pkRoot msg
  set md := digest.take p.mdBytes
  set idxTree := digestTree p digest
  set idxLeaf := digestLeaf p digest
  set s1 := (forsSplit p).1
  set s2 := (forsSplit p).2
  set forsAdrs := { { Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  set indices := base2b md p.a p.k
  have hr_len : r.length = p.n := PRFmsg_length p hv _ _ _
  have hleaf0 : idxLeaf < 2 ^ p.hp := digestLeaf_lt p hv digest
  have hloc_lt : ∀ j, (htLoc p.hp idxTree idxLeaf j).2 < 2 ^ p.hp := by
    intro j
    cases j with
    | zero => exact hleaf0
    | succ j => exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- Step 1: FORS fold writes exactly forsSign at sigOff + p.n
  have hfors_piece_eq : ∀ treeIdx < p.k,
      metalForsPass1Secret p s1 skSeed pkSeed forsAdrs treeIdx indices[treeIdx]! ++
        (List.range p.a).flatMap (metalForsAuthNode p s1 s2 skSeed pkSeed forsAdrs treeIdx indices[treeIdx]!) =
      forsPiece p skSeed pkSeed forsAdrs indices treeIdx := by
    intro treeIdx hti
    have htarget : indices[treeIdx]! < 2 ^ p.a := base2b_getElem!_lt md p.a p.k treeIdx hti
    unfold forsPiece
    rw [metal_fors_pass1_secret_eq_fips p s1 skSeed pkSeed forsAdrs treeIdx _]
    apply congrArg (_ ++ ·)
    apply flatMap_congr'
    intro h hh
    rw [List.mem_range] at hh
    exact metal_fors_auth_node_eq_fips p s1 s2 hs1 hsplit skSeed pkSeed forsAdrs treeIdx _ h htarget hh
  have hfors_fold : ∀ c ≤ p.k,
      (List.range c).foldl (fun b treeIdx =>
        let treeOff := sigOff + p.n + treeIdx * (1 + p.a) * p.n
        let target := indices[treeIdx]!
        let b' := patchAt b treeOff (metalForsPass1Secret p s1 skSeed pkSeed forsAdrs treeIdx target)
        patchChunks b' (treeOff + p.n) p.n
          (metalForsAuthNode p s1 s2 skSeed pkSeed forsAdrs treeIdx target) p.a) (patchAt buf sigOff r) =
      patchAt buf sigOff (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices)) := by
    intro c
    induction c with
    | zero => intro _; simp
    | succ c ih =>
      intro hc
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hprev_len : ((List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices)).length =
          c * (1 + p.a) * p.n := by
        rw [length_flatMap_const _ _ (forsPiece_length p hv skSeed pkSeed forsAdrs indices) c]; ring
      have hsec_len : (metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!).length = p.n := by
        rw [metal_fors_pass1_secret_eq_fips p s1]; exact PRF_length p hv _ _ _
      have hauth_len : ∀ h, (metalForsAuthNode p s1 s2 skSeed pkSeed forsAdrs c indices[c]! h).length = p.n := by
        intro h
        by_cases hh : h < p.a
        · rw [metal_fors_auth_node_eq_fips p s1 s2 hs1 hsplit skSeed pkSeed forsAdrs c _ h
            (base2b_getElem!_lt md p.a p.k c (by omega)) hh]
          exact forsNode_length p hv _ _ _ _ _
        · unfold metalForsAuthNode
          split
          · omega
          · unfold metalForsPass2AuthNode
            have hgen : ∀ st idx,
                (metalForsPass2State p s1 s2 pkSeed forsAdrs c
                  (metalForsPass1SubRoot p s1 skSeed pkSeed forsAdrs c) st idx).length = p.n := by
              intro st
              induction st with
              | zero =>
                intro idx
                simpa [metalForsPass2State] using
                  (by rw [metal_fors_pass1_subroot_eq_fips p s1 s2 hsplit]; exact forsNode_length p hv _ _ _ _ _)
              | succ st ihst =>
                intro idx
                simp only [metalForsPass2State, tgReduceStep]
                split
                · exact H_length p hv _ _ _
                · exact ihst idx
            exact hgen (h - s1) _
      have hbound_tree : sigOff + p.n + (c + 1) * (1 + p.a) * p.n ≤ buf.length := by
        have hcle : (c + 1) * (1 + p.a) * p.n ≤ p.forsSigBytes := by
          unfold Params.forsSigBytes
          have : (c + 1) * (1 + p.a) ≤ p.k * (1 + p.a) := Nat.mul_le_mul_right _ hc
          exact Nat.mul_le_mul_right _ this
        omega
      have hstep_sum : c * (1 + p.a) * p.n + p.n + p.a * p.n = (c + 1) * (1 + p.a) * p.n := by ring
      have hlen_prefix : (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices)).length =
          p.n + c * (1 + p.a) * p.n := by
        rw [List.length_append, hr_len, hprev_len]
      have hoff_eq : sigOff + (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices)).length =
          sigOff + p.n + c * (1 + p.a) * p.n := by
        rw [hlen_prefix]; omega
      have h1 : patchAt (patchAt buf sigOff (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices)))
          (sigOff + p.n + c * (1 + p.a) * p.n)
          (metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!) =
        patchAt buf sigOff (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices) ++
          metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!) := by
        rw [← hoff_eq, patchAt_append buf sigOff _ _ (by rw [hlen_prefix, hsec_len]; omega)]
      rw [h1]
      have hlen_mid : (patchAt buf sigOff (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices) ++
          metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!)).length = buf.length := by
        apply patchAt_length
        rw [List.length_append, hlen_prefix, hsec_len]; omega
      have hfit_auth : sigOff + p.n + c * (1 + p.a) * p.n + p.n + p.a * p.n ≤
          (patchAt buf sigOff (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices) ++
            metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!)).length := by
        rw [hlen_mid]; omega
      rw [patchChunks_eq _ _ p.n _ hauth_len p.a hfit_auth]
      have hoff2 : sigOff + (r ++ (List.range c).flatMap (forsPiece p skSeed pkSeed forsAdrs indices) ++
          metalForsPass1Secret p s1 skSeed pkSeed forsAdrs c indices[c]!).length =
          sigOff + p.n + c * (1 + p.a) * p.n + p.n := by
        rw [List.length_append, hlen_prefix, hsec_len]; omega
      rw [← hoff2, patchAt_append buf sigOff _ _ (by
        rw [hoff2, length_flatMap_const _ _ hauth_len]; omega)]
      rw [List.flatMap_append, List.flatMap_singleton, ← hfors_piece_eq c (by omega)]
      simp only [List.append_assoc]
  rw [hfors_fold p.k (le_refl _)]
  have hfors_eq : (List.range p.k).flatMap (forsPiece p skSeed pkSeed forsAdrs indices) =
      forsSign p md skSeed pkSeed forsAdrs := rfl
  rw [hfors_eq]
  -- Step 2: XMSS leaves, roots, and auth paths for every layer j < p.d
  set keys : Nat → Bytes × Bytes := fun _ => (skSeed, pkSeed)
  set trees : Nat → XmssTreeDesc := fun j =>
    let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
    let layerOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
    { tree := tree, keyIdx := 0, layer := j, targetLeaf := some leaf,
      authByteOff := layerOff + p.len * p.n }
  have hxmss_leaves : ∀ j l, l < 2 ^ p.hp →
      metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l) =
        xmssNode p skSeed l 0 pkSeed { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 } := by
    intro j l hl
    simpa [keys, trees] using metalXmssLeaves_eq_fips mode p hv keys trees j l hl
  have hxmss_root : ∀ j,
      (let (tree, _) := htLoc p.hp idxTree idxLeaf j
       metalXmssReduceRoot p pkSeed { Adrs.zero with layer := j, tree := tree }
         (fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l))) =
      xmssNode p skSeed 0 p.hp pkSeed { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 } := by
    intro j
    exact (metal_xmss_reduce_eq_fips p skSeed pkSeed
      { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
      _ (hxmss_leaves j) (htLoc p.hp idxTree idxLeaf j).2 (hloc_lt j)).2.1
  have hxmss_auth : ∀ j,
      (List.range p.hp).flatMap (metalXmssReduceAuthNode p pkSeed
        { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
        (fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l))
        (htLoc p.hp idxTree idxLeaf j).2) =
      (List.range p.hp).flatMap (fun h =>
        xmssNode p skSeed (((htLoc p.hp idxTree idxLeaf j).2 / 2 ^ h) ^^^ 1) h pkSeed
          { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }) := by
    intro j
    exact (metal_xmss_reduce_eq_fips p skSeed pkSeed
      { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
      _ (hxmss_leaves j) (htLoc p.hp idxTree idxLeaf j).2 (hloc_lt j)).2.2
  have hxmss_auth_node_len : ∀ j h,
      (metalXmssReduceAuthNode p pkSeed
        { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
        (fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l))
        (htLoc p.hp idxTree idxLeaf j).2 h).length = p.n := by
    intro j h
    unfold metalXmssReduceAuthNode
    have hgen : ∀ lvl idx,
        (metalXmssReduceState p pkSeed
          { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
          (fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l)) lvl idx).length = p.n := by
      intro lvl
      induction lvl with
      | zero =>
        intro idx
        simp only [metalXmssReduceState]
        have hpos : 0 < 2 ^ p.hp := Nat.two_pow_pos p.hp
        have hlt : (j * 2 ^ p.hp + idx) % 2 ^ p.hp < 2 ^ p.hp := Nat.mod_lt _ hpos
        have heq : ((j * 2 ^ p.hp + idx) / 2 ^ p.hp) * 2 ^ p.hp + (j * 2 ^ p.hp + idx) % 2 ^ p.hp =
            j * 2 ^ p.hp + idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
        rw [← heq, metalXmssLeaves_eq_fips mode p hv keys trees _ _ hlt]
        exact xmssNode_length p hv _ _ _ _ _
      | succ lvl ihlvl =>
        intro idx
        simp only [metalXmssReduceState, tgReduceStep]
        split
        · exact H_length p hv _ _ _
        · exact ihlvl idx
    exact hgen h _
  -- Step 3: Simplify pkFors and xmssRoots
  have hpkFors : metalForsPk p s1 s2 skSeed pkSeed forsAdrs =
      forsPkFromSig p (forsSign p md skSeed pkSeed forsAdrs) md pkSeed forsAdrs :=
    (metal_fors_two_pass_eq_fips p hv s1 s2 hs1 hsplit md skSeed pkSeed forsAdrs).2
  set specRoots : Nat → Bytes := fun j =>
    xmssNode p skSeed 0 p.hp pkSeed { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }
  have hroots_eq : (fun j =>
      let (tree, _) := htLoc p.hp idxTree idxLeaf j
      metalXmssReduceRoot p pkSeed { Adrs.zero with layer := j, tree := tree }
        (fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l))) = specRoots := by
    funext j; exact hxmss_root j
  -- Step 4: Commute auth-path writes with WOTS+ writes per layer
  set baseBuf := patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs)
  have hbase_len : baseBuf.length = buf.length := by
    apply patchAt_length
    rw [List.length_append, hr_len, forsSign_length p hv]; omega
  set layerOff := fun j => sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
  set authVal := fun j =>
    (List.range p.hp).flatMap (fun h =>
      xmssNode p skSeed (((htLoc p.hp idxTree idxLeaf j).2 / 2 ^ h) ^^^ 1) h pkSeed
        { Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 })
  set wotsVal := fun j =>
    wotsSign p (metalLayerMsg (forsPkFromSig p (forsSign p md skSeed pkSeed forsAdrs) md pkSeed forsAdrs) specRoots j)
      skSeed pkSeed
      { ({ Adrs.zero with layer := j, tree := (htLoc p.hp idxTree idxLeaf j).1 }.setTypeAndClear WOTS_HASH) with
        keypair := (htLoc p.hp idxTree idxLeaf j).2 }
  have hauth_len : ∀ j, (authVal j).length = p.hp * p.n := fun j =>
    length_flatMap_const _ _ (fun _ => xmssNode_length p hv _ _ _ _ _) _
  have hwots_len : ∀ j, (wotsVal j).length = p.len * p.n := fun j =>
    wotsSign_length p hv _ _ _ _
  have hxmss_eq_sum : p.xmssSigBytes = p.len * p.n + p.hp * p.n := by
    simp [Params.xmssSigBytes, Nat.add_mul]
  have hauth_fold_eq : ∀ c ≤ p.d,
      (List.range c).foldl (fun b j =>
        let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
        let lOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
        let aOff := lOff + p.len * p.n
        let leaves := fun l => metalXmssLeaves mode p keys trees (j * 2 ^ p.hp + l)
        patchChunks b aOff p.n
          (metalXmssReduceAuthNode p pkSeed { Adrs.zero with layer := j, tree := tree } leaves leaf) p.hp) baseBuf =
      (List.range c).foldl (fun b j => patchAt b (layerOff j + p.len * p.n) (authVal j)) baseBuf ∧
      ((List.range c).foldl (fun b j => patchAt b (layerOff j + p.len * p.n) (authVal j)) baseBuf).length = buf.length := by
    intro c
    induction c with
    | zero => intro _; exact ⟨rfl, hbase_len⟩
    | succ c ih =>
      intro hc
      obtain ⟨heq_c, hlen_c⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, heq_c]
      simp only [List.foldl_cons, List.foldl_nil]
      have hfit_a : layerOff c + p.len * p.n + p.hp * p.n ≤
          ((List.range c).foldl (fun b j => patchAt b (layerOff j + p.len * p.n) (authVal j)) baseBuf).length := by
        rw [hlen_c]
        have hcle : (c + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ hc
        have : layerOff c + p.len * p.n + p.hp * p.n = sigOff + p.n + p.forsSigBytes + (c + 1) * p.xmssSigBytes := by
          dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
        omega
      have hpch := patchChunks_eq _ (layerOff c + p.len * p.n) p.n
        (metalXmssReduceAuthNode p pkSeed
          { Adrs.zero with layer := c, tree := (htLoc p.hp idxTree idxLeaf c).1 }
          (fun l => metalXmssLeaves mode p keys trees (c * 2 ^ p.hp + l))
          (htLoc p.hp idxTree idxLeaf c).2)
        (hxmss_auth_node_len c) p.hp hfit_a
      rw [hpch, hxmss_auth c]
      refine ⟨?_, ?_⟩
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, authVal]
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [patchAt_length _ _ _ (by rw [hauth_len]; exact hfit_a), hlen_c]
  obtain ⟨hauth_f, hauth_flen⟩ := hauth_fold_eq p.d (le_refl _)
  rw [hauth_f]
  set afterAuth := (List.range p.d).foldl (fun b j => patchAt b (layerOff j + p.len * p.n) (authVal j)) baseBuf
  have hwots_chain_len : ∀ j c,
      (metalWotsSignChain p skSeed pkSeed
        (metalLayerMsg (metalForsPk p s1 s2 skSeed pkSeed forsAdrs)
          (fun k => let (tree, _) := htLoc p.hp idxTree idxLeaf k
            metalXmssReduceRoot p pkSeed { Adrs.zero with layer := k, tree := tree }
              (fun l => metalXmssLeaves mode p keys trees (k * 2 ^ p.hp + l))) j)
        j (htLoc p.hp idxTree idxLeaf j).1 (htLoc p.hp idxTree idxLeaf j).2 c).length = p.n := by
    intro j c
    unfold metalWotsSignChain metalRunWotsChain
    exact chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _
  have hwots_fold_eq : ∀ c ≤ p.d,
      (List.range c).foldl (fun b j =>
        let (tree, leaf) := htLoc p.hp idxTree idxLeaf j
        let lOff := sigOff + p.n + p.forsSigBytes + j * p.xmssSigBytes
        let lMsg := metalLayerMsg (metalForsPk p s1 s2 skSeed pkSeed forsAdrs)
          (fun k => let (tree, _) := htLoc p.hp idxTree idxLeaf k
            metalXmssReduceRoot p pkSeed { Adrs.zero with layer := k, tree := tree }
              (fun l => metalXmssLeaves mode p keys trees (k * 2 ^ p.hp + l))) j
        patchChunks b lOff p.n (metalWotsSignChain p skSeed pkSeed lMsg j tree leaf) p.len) afterAuth =
      (List.range c).foldl (fun b j => patchAt b (layerOff j) (wotsVal j)) afterAuth ∧
      ((List.range c).foldl (fun b j => patchAt b (layerOff j) (wotsVal j)) afterAuth).length = buf.length := by
    intro c
    induction c with
    | zero => intro _; exact ⟨rfl, hauth_flen⟩
    | succ c ih =>
      intro hc
      obtain ⟨heq_c, hlen_c⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, heq_c]
      simp only [List.foldl_cons, List.foldl_nil]
      have hfit_w : layerOff c + p.len * p.n ≤
          ((List.range c).foldl (fun b j => patchAt b (layerOff j) (wotsVal j)) afterAuth).length := by
        rw [hlen_c]
        have hcle : (c + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ hc
        have : layerOff c + p.len * p.n + p.hp * p.n = sigOff + p.n + p.forsSigBytes + (c + 1) * p.xmssSigBytes := by
          dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
        omega
      rw [patchChunks_eq _ (layerOff c) p.n _ (hwots_chain_len c) p.len hfit_w]
      rw [metal_wots_sign_eq_fips, hpkFors, hroots_eq]
      refine ⟨?_, ?_⟩
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, wotsVal]
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [patchAt_length _ _ _ (by rw [hwots_len]; exact hfit_w), hlen_c]
  rw [(hwots_fold_eq p.d (le_refl _)).1]
  have hcomm_above : ∀ (b : Bytes) (k lo len : Nat), b.length = buf.length → k < lo → lo + len ≤ p.d →
      patchAt ((List.range len).foldl (fun acc t => patchAt acc (layerOff (lo + t) + p.len * p.n) (authVal (lo + t))) b)
        (layerOff k) (wotsVal k) =
      (List.range len).foldl (fun acc t => patchAt acc (layerOff (lo + t) + p.len * p.n) (authVal (lo + t)))
        (patchAt b (layerOff k) (wotsVal k)) := by
    intro b k lo len hbl hkl hbound
    induction len with
    | zero => rfl
    | succ len ih =>
      have hlen_l : ((List.range len).foldl (fun acc t => patchAt acc (layerOff (lo + t) + p.len * p.n) (authVal (lo + t))) b).length =
          buf.length := by
        clear ih
        induction len with
        | zero => exact hbl
        | succ l' ih' =>
          rw [List.range_succ, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          have hl := ih' (by omega)
          rw [patchAt_length _ _ _ (by
            rw [hl, hauth_len]
            have hle : (lo + l' + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ (by omega)
            have : layerOff (lo + l') + p.len * p.n + p.hp * p.n =
                sigOff + p.n + p.forsSigBytes + (lo + l' + 1) * p.xmssSigBytes := by
              dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
            omega), hl]
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hdisj : layerOff k + (wotsVal k).length ≤ layerOff (lo + len) + p.len * p.n := by
        rw [hwots_len]
        have hle : k * p.xmssSigBytes ≤ (lo + len) * p.xmssSigBytes := Nat.mul_le_mul_right _ (by omega)
        dsimp only [layerOff]; omega
      have hfit_a : layerOff (lo + len) + p.len * p.n + (authVal (lo + len)).length ≤
          ((List.range len).foldl (fun acc t => patchAt acc (layerOff (lo + t) + p.len * p.n) (authVal (lo + t))) b).length := by
        rw [hlen_l, hauth_len]
        have hle : (lo + len + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ (by omega)
        have : layerOff (lo + len) + p.len * p.n + p.hp * p.n =
            sigOff + p.n + p.forsSigBytes + (lo + len + 1) * p.xmssSigBytes := by
          dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
        omega
      rw [← patchAt_comm _ _ _ _ _ hdisj hfit_a, ih (by omega)]
  have hcombine : ∀ c ≤ p.d,
      (List.range c).foldl (fun b j => patchAt b (layerOff j) (wotsVal j))
        ((List.range p.d).foldl (fun b j => patchAt b (layerOff j + p.len * p.n) (authVal j)) baseBuf) =
      (List.range (p.d - c)).foldl (fun b t => patchAt b (layerOff (c + t) + p.len * p.n) (authVal (c + t)))
        (patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j))) := by
    intro c
    induction c with
    | zero =>
      intro _
      simp [baseBuf]
    | succ c ih =>
      intro hc
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hsplit_rem : p.d - c = 1 + (p.d - (c + 1)) := by omega
      rw [hsplit_rem, List.range_add, List.foldl_append]
      simp only [List.range_one, List.foldl_cons, List.foldl_nil, Nat.add_zero, List.foldl_map]
      have hmid_len : (patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j))).length = buf.length := by
        apply patchAt_length
        rw [List.length_append, List.length_append, hr_len, forsSign_length p hv,
            length_flatMap_const _ p.xmssSigBytes (fun j => by rw [List.length_append, hwots_len, hauth_len, hxmss_eq_sum])]
        have hcle : c * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ (by omega)
        omega
      have hcur_auth_len : (patchAt (patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j)))
          (layerOff c + p.len * p.n) (authVal c)).length = buf.length := by
        rw [patchAt_length _ _ _ (by
          rw [hmid_len, hauth_len]
          have hcle : (c + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ hc
          have : layerOff c + p.len * p.n + p.hp * p.n =
              sigOff + p.n + p.forsSigBytes + (c + 1) * p.xmssSigBytes := by
            dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
          omega), hmid_len]
      have hnorm : (fun acc t => patchAt acc (layerOff (c + (1 + t)) + p.len * p.n) (authVal (c + (1 + t)))) =
          (fun acc t => patchAt acc (layerOff ((c + 1) + t) + p.len * p.n) (authVal ((c + 1) + t))) := by
        funext acc t; rw [show c + (1 + t) = c + 1 + t by omega]
      rw [hnorm, hcomm_above _ c (c + 1) (p.d - (c + 1)) hcur_auth_len (by omega) (by omega)]
      congr 1
      have hdisj_wa : layerOff c + (wotsVal c).length ≤ layerOff c + p.len * p.n := by
        rw [hwots_len]
      have hfit_ac : layerOff c + p.len * p.n + (authVal c).length ≤
          (patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
            (List.range c).flatMap (fun j => wotsVal j ++ authVal j))).length := by
        rw [hmid_len, hauth_len]
        have hcle : (c + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ hc
        have : layerOff c + p.len * p.n + p.hp * p.n =
            sigOff + p.n + p.forsSigBytes + (c + 1) * p.xmssSigBytes := by
          dsimp only [layerOff]; rw [Nat.succ_mul, hxmss_eq_sum]; ring
        omega
      rw [← patchAt_comm _ _ _ _ _ hdisj_wa hfit_ac]
      have hpre_len : (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j)).length =
          p.n + p.forsSigBytes + c * p.xmssSigBytes := by
        rw [List.length_append, List.length_append, hr_len, forsSign_length p hv,
            length_flatMap_const _ p.xmssSigBytes (fun j => by rw [List.length_append, hwots_len, hauth_len, hxmss_eq_sum])]
      have hoff_w : sigOff + (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j)).length = layerOff c := by
        rw [hpre_len]; dsimp only [layerOff]; omega
      have hfit_tot : sigOff + p.n + p.forsSigBytes + c * p.xmssSigBytes + p.len * p.n + p.hp * p.n ≤ buf.length := by
        have hcle : (c + 1) * p.xmssSigBytes ≤ p.d * p.xmssSigBytes := Nat.mul_le_mul_right _ hc
        have hstep_c : c * p.xmssSigBytes + p.len * p.n + p.hp * p.n = (c + 1) * p.xmssSigBytes := by
          rw [Nat.succ_mul, hxmss_eq_sum]; ring
        omega
      have hstep1 : patchAt (patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j))) (layerOff c) (wotsVal c) =
        patchAt buf sigOff (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j) ++ wotsVal c) := by
        rw [← hoff_w, patchAt_append buf sigOff _ _ (by rw [hpre_len, hwots_len]; omega)]
      rw [hstep1]
      have hoff_a : sigOff + (r ++ forsSign p md skSeed pkSeed forsAdrs ++
          (List.range c).flatMap (fun j => wotsVal j ++ authVal j) ++ wotsVal c).length =
          layerOff c + p.len * p.n := by
        rw [List.length_append, hpre_len, hwots_len]; dsimp only [layerOff]; omega
      rw [← hoff_a, patchAt_append buf sigOff _ _ (by rw [hoff_a, hauth_len]; dsimp only [layerOff]; omega)]
      rw [List.flatMap_append, List.flatMap_singleton]
      simp only [List.append_assoc]
  rw [hcombine p.d (le_refl _)]
  simp only [Nat.sub_self, List.range_zero, List.foldl_nil]
  have hht : (List.range p.d).flatMap (fun j => wotsVal j ++ authVal j) =
      htSign p (forsPkFromSig p (forsSign p md skSeed pkSeed forsAdrs) md pkSeed forsAdrs)
        skSeed pkSeed idxTree idxLeaf := by
    rw [← ht_layers_eq_spec p hv _ skSeed pkSeed idxTree idxLeaf hleaf0]
    apply flatMap_congr'
    intro j _
    rfl
  rw [hht]

/-- Composed single-signature internal GPU signing (`sign_internal_batch_family` with `B = 1`). -/
def metalSignInternal (mode : XmssMode) (p : Params) (msg sk addrnd : Bytes) : Bytes :=
  let initBuf : Bytes := List.replicate p.sigBytes 0
  metalWriteSingleSig mode p initBuf 0 msg sk addrnd

/-- **Theorem 4b (`metal_sign_internal_eq_fips`)**:
Single-invocation GPU internal signing (both two-phase and streaming XMSS modes)
produces the exact FIPS 205 `Spec.slhSignInternal` byte string! -/
theorem metal_sign_internal_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (msg sk addrnd : Bytes) :
    metalSignInternal mode p msg sk addrnd = slhSignInternal p msg sk addrnd := by
  unfold metalSignInternal
  rw [metalWriteSingleSig_eq_patch mode p hv _ 0 msg sk addrnd (by simp)]
  exact patchAt_full _ _ (by simp [slhSignInternal_length p hv])

/-- Composed pure-mode GPU signing (`sign` / `shake_sign`, Algorithm 22). -/
def metalSign (mode : XmssMode) (p : Params) (msg ctx sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none else some (metalSignInternal mode p (withContext msg ctx) sk addrnd)

/-- **Theorem 4c (`metal_sign_eq_fips`)**:
Single-invocation GPU pure signing (`sign` / `shake_sign`) produces the exact FIPS 205
`Spec.slhSign` result across all 12 parameter sets (both two-phase and streaming modes). -/
theorem metal_sign_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (msg ctx sk addrnd : Bytes) :
    metalSign mode p msg ctx sk addrnd = slhSign p msg ctx sk addrnd := by
  simp only [metalSign, slhSign, metal_sign_internal_eq_fips mode p hv]

/-- A single signing request in a GPU batch (`SignInternalReq` / `SignReq`). -/
structure BatchSignReq where
  msg : Bytes
  ctx : Bytes
  sk : Bytes
  addrnd : Bytes
deriving Inhabited

/-- Batched GPU internal signing (`sign_internal_batch_family` for any `B ≥ 0`, including `B ≥ 1`):
writes all `B` signatures into a single flat `out_sigs` buffer of size `B * sigBytes`
at offsets `sig_idx * sigBytes`, then slices `[sig_idx * sigBytes .. (sig_idx + 1) * sigBytes]`. -/
def metalBatchSignInternal (mode : XmssMode) (p : Params) (reqs : List BatchSignReq) : List Bytes :=
  let initBuf : Bytes := List.replicate (reqs.length * p.sigBytes) 0
  let outSigs := (List.range reqs.length).foldl (fun buf sigIdx =>
    let req := reqs[sigIdx]!
    metalWriteSingleSig mode p buf (sigIdx * p.sigBytes) req.msg req.sk req.addrnd) initBuf
  (List.range reqs.length).map fun sigIdx =>
    (outSigs.drop (sigIdx * p.sigBytes)).take p.sigBytes

/-- Batched GPU pure signing (`sign_batch_family` for any `B ≥ 1`):
rejects the batch if any request has `ctx.length > 255`, otherwise frames each message
with `withContext` and runs `metalBatchSignInternal`. -/
def metalBatchSign (mode : XmssMode) (p : Params) (reqs : List BatchSignReq) : Option (List Bytes) :=
  if reqs.any (fun r => decide (r.ctx.length > 255)) then none
  else
    let framed := reqs.map fun r => { r with msg := withContext r.msg r.ctx }
    some (metalBatchSignInternal mode p framed)

/-- Internal batch signing in a shared `B * sigBytes` buffer produces the exact list of
FIPS 205 `Spec.slhSignInternal` signatures. -/
theorem metal_batch_sign_internal_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (reqs : List BatchSignReq) :
    metalBatchSignInternal mode p reqs =
      reqs.map (fun r => slhSignInternal p r.msg r.sk r.addrnd) := by
  unfold metalBatchSignInternal
  set initBuf : Bytes := List.replicate (reqs.length * p.sigBytes) 0
  set sigOf : Nat → Bytes := fun i =>
    let req := reqs[i]!
    slhSignInternal p req.msg req.sk req.addrnd
  have hsig_len : ∀ i, (sigOf i).length = p.sigBytes := fun i =>
    slhSignInternal_length p hv _ _ _
  have hfold : ∀ c ≤ reqs.length,
      (List.range c).foldl (fun buf sigIdx =>
        let req := reqs[sigIdx]!
        metalWriteSingleSig mode p buf (sigIdx * p.sigBytes) req.msg req.sk req.addrnd) initBuf =
      patchAt initBuf 0 ((List.range c).flatMap sigOf) := by
    intro c
    induction c with
    | zero => intro _; simp [patchAt]
    | succ c ih =>
      intro hc
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hflat_len : ((List.range c).flatMap sigOf).length = c * p.sigBytes :=
        length_flatMap_const sigOf p.sigBytes hsig_len c
      have hbuf_len : (patchAt initBuf 0 ((List.range c).flatMap sigOf)).length =
          reqs.length * p.sigBytes := by
        rw [patchAt_length initBuf 0 _ (by
          simp only [initBuf, List.length_replicate, Nat.zero_add, hflat_len]
          exact Nat.mul_le_mul_right _ (by omega))]
        simp [initBuf]
      have hfit : c * p.sigBytes + p.sigBytes ≤ (patchAt initBuf 0 ((List.range c).flatMap sigOf)).length := by
        rw [hbuf_len]
        have : c * p.sigBytes + p.sigBytes = (c + 1) * p.sigBytes := by rw [Nat.succ_mul]
        rw [this]
        exact Nat.mul_le_mul_right _ hc
      rw [metalWriteSingleSig_eq_patch mode p hv _ (c * p.sigBytes) _ _ _ hfit]
      have hzero : 0 + ((List.range c).flatMap sigOf).length = c * p.sigBytes := by
        rw [Nat.zero_add, hflat_len]
      rw [← hzero, patchAt_append initBuf 0 _ _ (by
        simp only [initBuf, List.length_replicate, Nat.zero_add, hflat_len, slhSignInternal_length p hv]
        have : c * p.sigBytes + p.sigBytes = (c + 1) * p.sigBytes := by rw [Nat.succ_mul]
        rw [this]
        exact Nat.mul_le_mul_right _ hc)]
      rw [List.flatMap_append, List.flatMap_singleton]
  dsimp only
  rw [hfold reqs.length (le_refl _)]
  have hfull : patchAt initBuf 0 ((List.range reqs.length).flatMap sigOf) =
      (List.range reqs.length).flatMap sigOf :=
    patchAt_full initBuf _ (by
      simp [initBuf, length_flatMap_const sigOf p.sigBytes hsig_len])
  rw [hfull]
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range]
  have hi : i < reqs.length := by simpa using hi2
  have hpiece := flatMap_piece sigOf p.sigBytes hsig_len reqs.length i 0 p.sigBytes hi (by omega)
  simp only [Nat.add_zero, List.drop_zero, List.take_of_length_le (le_of_eq (hsig_len i))] at hpiece
  rw [hpiece]
  simp [sigOf, hi]

/-- **Theorem 4d (`metal_batch_sign_eq_fips`)**:
Batched pure-mode GPU signing (`sign_batch` / `shake_sign_batch`, any `B ≥ 0` including `B ≥ 1`,
both two-phase and streaming XMSS modes) equals exact FIPS 205 `Spec.slhSign` element-wise. -/
theorem metal_batch_sign_eq_fips (mode : XmssMode) (p : Params) (hv : p.Valid)
    (reqs : List BatchSignReq) :
    metalBatchSign mode p reqs =
      reqs.mapM (fun r => slhSign p r.msg r.ctx r.sk r.addrnd) := by
  unfold metalBatchSign
  by_cases hany : reqs.any (fun r => decide (r.ctx.length > 255)) = true
  · simp only [hany, ↓reduceIte]
    rw [List.any_eq_true] at hany
    obtain ⟨r, hr_mem, hr_gt⟩ := hany
    rw [decide_eq_true_eq] at hr_gt
    have hnone : ∀ l : List BatchSignReq, (∃ x ∈ l, x.ctx.length > 255) →
        l.mapM (fun r => slhSign p r.msg r.ctx r.sk r.addrnd) = none := by
      intro l
      induction l with
      | nil => intro ⟨_, hx, _⟩; simp at hx
      | cons x xs ih =>
        intro ⟨y, hy, hgt⟩
        rw [List.mapM_cons]
        by_cases hx : x.ctx.length > 255
        · have hhead : slhSign p x.msg x.ctx x.sk x.addrnd = none := by simp [slhSign, hx]
          rw [hhead]; rfl
        · have hhead : slhSign p x.msg x.ctx x.sk x.addrnd =
              some (slhSignInternal p (withContext x.msg x.ctx) x.sk x.addrnd) := by simp [slhSign, hx]
          rw [hhead]
          rcases List.mem_cons.mp hy with rfl | hy'
          · omega
          · rw [ih ⟨y, hy', hgt⟩]; rfl
    exact (hnone reqs ⟨r, hr_mem, hr_gt⟩).symm
  · simp only [hany, Bool.false_eq_true, ↓reduceIte]
    rw [metal_batch_sign_internal_eq_fips mode p hv]
    have hall : ∀ r ∈ reqs, ¬ r.ctx.length > 255 := by
      intro r hr hgt
      apply hany
      rw [List.any_eq_true]
      exact ⟨r, hr, decide_eq_true hgt⟩
    have hmapM : ∀ l : List BatchSignReq, (∀ r ∈ l, ¬ r.ctx.length > 255) →
        l.mapM (fun r => slhSign p r.msg r.ctx r.sk r.addrnd) =
          some (l.map (fun r => slhSignInternal p (withContext r.msg r.ctx) r.sk r.addrnd)) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro h
        have hx := h x (by simp)
        have hxs : ∀ r ∈ xs, ¬ r.ctx.length > 255 := fun r hr => h r (by simp [hr])
        rw [List.mapM_cons, ih hxs]
        have hhead : slhSign p x.msg x.ctx x.sk x.addrnd =
            some (slhSignInternal p (withContext x.msg x.ctx) x.sk x.addrnd) := by simp [slhSign, hx]
        rw [hhead]; rfl
    rw [hmapM reqs hall, List.map_map]
    rfl

/-! ## Instantiation Across All 12 FIPS 205 Parameter Sets -/

/-- All twelve FIPS 205 parameter sets (6 SHA-2 + 6 SHAKE) supported by the Metal backend. -/
def all12Params : List Params :=
  [ sha2_128s, sha2_128f, sha2_192s, sha2_192f, sha2_256s, sha2_256f
  , shake_128s, shake_128f, shake_192s, shake_192f, shake_256s, shake_256f ]

theorem metal_all_12_params_valid : ∀ p ∈ all12Params, p.Valid := by
  intro p hp
  simp only [all12Params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sha2_128s_valid
  · exact sha2_128f_valid
  · exact sha2_192s_valid
  · exact sha2_192f_valid
  · exact sha2_256s_valid
  · exact sha2_256f_valid
  · exact shake_128s_valid
  · exact shake_128f_valid
  · exact shake_192s_valid
  · exact shake_192f_valid
  · exact shake_256s_valid
  · exact shake_256f_valid

/-- Summary headline theorem: for every one of the 12 FIPS 205 parameter sets and both
XMSS execution modes (two-phase and streaming), GPU keygen, single signing, and
batched signing equal FIPS 205 `Spec.slhKeygenInternal` and `Spec.slhSign`. -/
theorem metal_all_12_params_sign_eq_fips (p : Params) (hp : p ∈ all12Params) (mode : XmssMode) :
    (∀ skSeed skPrf pkSeed,
      metalKeygenInternal mode p skSeed skPrf pkSeed = slhKeygenInternal p skSeed skPrf pkSeed) ∧
    (∀ msg ctx sk addrnd,
      metalSign mode p msg ctx sk addrnd = slhSign p msg ctx sk addrnd) ∧
    (∀ reqs,
      metalBatchSign mode p reqs = reqs.mapM (fun r => slhSign p r.msg r.ctx r.sk r.addrnd)) := by
  have hv := metal_all_12_params_valid p hp
  exact ⟨metal_keygen_eq_fips mode p hv,
         metal_sign_eq_fips mode p hv,
         metal_batch_sign_eq_fips mode p hv⟩

end MetalPipeline
