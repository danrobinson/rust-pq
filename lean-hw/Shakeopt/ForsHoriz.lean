import Spec.SlhDsa
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Horizontal 8-Way FORS TreeHash and Active-Lane FORS Recovery

Proves correctness of the three SHAKE FORS kernels in `rust/src/shake/fors_batch.rs`:
1. `fors_subtree_horiz`: bottom-up 8-way horizontal TreeHash stack (both the `len[h] == 16`
   carry-pop loop and the final `len[h] / 2` tail reduction loop) equals `Spec.forsNode`
   for all `height >= 3`.
2. `fors_batch::sign`: batched `FORS_PRF` secrets, cross-tree heights `0..=2` batching,
   and heights `3..a` via `fors_subtree_horiz` (plus the width-generic fallback) equal
   FIPS 205 Algorithm 16 (`Spec.forsSign`).
3. `fors_batch::recover`: active-lane in-place climbing across `k` trees in batches of
   `WIDTH` + `FORS_ROOTS` sponge equals FIPS 205 Algorithm 17 (`Spec.forsPkFromSig`).
-/

namespace Shakeopt.ForsHoriz

open Spec

/-! ## Common Bit-Arithmetic and Batching Helpers -/

private theorem base2bGo_lt (x : Bytes) (b : Nat) :
    ∀ out inp bits total, ∀ d ∈ base2bGo x b out inp bits total, d < 2 ^ b
  | 0, _, _, _, _, hd => by simp [base2bGo] at hd
  | out + 1, inp, bits, total, d, hd => by
    simp only [base2bGo, List.mem_cons] at hd
    rcases hd with rfl | hrest
    · exact Nat.mod_lt _ (Nat.two_pow_pos b)
    · exact base2bGo_lt x b out _ _ _ d hrest

theorem base2b_lt (x : Bytes) (b outLen : Nat) {d : Nat} (hd : d ∈ base2b x b outLen) :
    d < 2 ^ b :=
  base2bGo_lt x b outLen 0 0 0 d hd

private theorem base2bGo_length (x : Bytes) (b : Nat) :
    ∀ out inp bits total, (base2bGo x b out inp bits total).length = out
  | 0, _, _, _ => rfl
  | out + 1, inp, bits, total => by
    simp [base2bGo, base2bGo_length]

theorem base2b_length (x : Bytes) (b outLen : Nat) :
    (base2b x b outLen).length = outLen :=
  base2bGo_length x b outLen 0 0 0

private theorem xor_one_add_even (q r : Nat) : (2 * q + r) ^^^ 1 = 2 * q + (r ^^^ 1) := by
  have h1 : ∀ a : Nat, a ^^^ 1 = if a % 2 = 0 then a + 1 else a - 1 := by
    intro a
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      by_cases h : a % 2 = 0
      · simp [h, Nat.add_mod]
      · have hodd : a % 2 = 1 := by omega
        have hsub : (a - 1) % 2 = 0 := by omega
        simp [hodd, hsub]
    | succ k =>
      simp only [Nat.testBit_xor, show Nat.testBit 1 (k + 1) = false by simp [Nat.testBit_succ],
        Bool.xor_false]
      by_cases h : a % 2 = 0
      · simp only [h, ↓reduceIte, Nat.testBit_succ, show (a + 1) / 2 = a / 2 by omega]
      · simp only [h, ↓reduceIte, Nat.testBit_succ, show (a - 1) / 2 = a / 2 by omega]
  rw [h1 (2 * q + r), h1 r]
  have hmod : (2 * q + r) % 2 = r % 2 := by omega
  rw [hmod]
  split_ifs <;> omega

/-- Shifting `tree * 2^a + sel` right by `j < a` and flipping bit 0 matches
    FIPS 205 Algorithm 16's `tree * 2^(a - j) + ((sel / 2^j) ^^^ 1)`. -/
theorem fors_sibling_index (tree a sel j : Nat) (hj : j < a) :
    ((tree * 2 ^ a + sel) / 2 ^ j) ^^^ 1 = tree * 2 ^ (a - j) + ((sel / 2 ^ j) ^^^ 1) := by
  have hpow : 2 ^ a = 2 ^ j * 2 ^ (a - j) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hj)]
  have hdiv : (tree * 2 ^ a + sel) / 2 ^ j = tree * 2 ^ (a - j) + sel / 2 ^ j := by
    rw [hpow, show tree * (2 ^ j * 2 ^ (a - j)) = 2 ^ j * (tree * 2 ^ (a - j)) by ring,
      Nat.mul_add_div (Nat.two_pow_pos j)]
  rw [hdiv]
  have heven : tree * 2 ^ (a - j) = 2 * (tree * 2 ^ (a - j - 1)) := by
    have hge : a - j = (a - j - 1) + 1 := by omega
    conv_lhs => rw [hge, Nat.pow_succ]
    ring
  rw [heven, xor_one_add_even]

/-- Parity of `(tree * 2^a + sel) / 2^lvl` equals parity of `sel / 2^lvl` when `lvl < a`. -/
theorem fors_climb_parity (tree a sel lvl : Nat) (hl : lvl < a) :
    ((tree * 2 ^ a + sel) / 2 ^ lvl) % 2 = (sel / 2 ^ lvl) % 2 := by
  have hpow : 2 ^ a = 2 ^ lvl * 2 ^ (a - lvl) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hl)]
  rw [hpow, show tree * (2 ^ lvl * 2 ^ (a - lvl)) = 2 ^ lvl * (tree * 2 ^ (a - lvl)) by ring,
    Nat.mul_add_div (Nat.two_pow_pos lvl)]
  have hge : a - lvl = (a - lvl - 1) + 1 := by omega
  rw [hge, Nat.pow_succ, show tree * (2 ^ (a - lvl - 1) * 2) = 2 * (tree * 2 ^ (a - lvl - 1)) by ring]
  omega

/-- Chunking `0..total` into active batches of size `min (total - i) width` visits every
    element in exact ascending order. -/
def batchChunksGo (width total : Nat) (hw : 0 < width) (f : Nat → α) (i : Nat) : List α :=
  if _h : i < total then
    let active := min (total - i) width
    (List.range active).map (fun lane => f (i + lane)) ++ batchChunksGo width total hw f (i + active)
  else []
termination_by total - i
decreasing_by
  have : 0 < min (total - i) width := Nat.lt_min.mpr ⟨by omega, hw⟩
  omega

def batchChunks (width total : Nat) (hw : 0 < width) (f : Nat → α) : List α :=
  batchChunksGo width total hw f 0

theorem batchChunksGo_eq (width total : Nat) (hw : 0 < width) (f : Nat → α) (i : Nat)
    (hi : i ≤ total) :
    batchChunksGo width total hw f i = (List.range (total - i)).map (fun k => f (i + k)) := by
  unfold batchChunksGo
  split_ifs with h
  · dsimp only
    set active := min (total - i) width
    have hact_le : active ≤ total - i := Nat.min_le_left _ _
    have hact_pos : 0 < active := Nat.lt_min.mpr ⟨by omega, hw⟩
    rw [batchChunksGo_eq width total hw f (i + active) (by omega)]
    have hsplit : total - i = active + (total - (i + active)) := by omega
    rw [hsplit, List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp [Nat.add_assoc]
  · have : total - i = 0 := by omega
    simp [this]
termination_by total - i

theorem batchChunks_eq (width total : Nat) (hw : 0 < width) (f : Nat → α) :
    batchChunks width total hw f = (List.range total).map f := by
  simpa [batchChunks] using batchChunksGo_eq width total hw f 0 (Nat.zero_le _)

/-! ## Part 1: Horizontal 8-Way FORS TreeHash (`fors_subtree_horiz`) -/

/-- Stack state of `fors_subtree_horiz` (`buf[0..=z]` and `next_idx[0..=z]`). -/
structure StackState where
  buf : Nat → List Bytes
  nextIdx : Nat → Nat

/-- Initial stack state before processing any 8-leaf blocks. -/
def initStack (nodeIndex z : Nat) : StackState where
  buf := fun _ => []
  nextIdx := fun h => nodeIndex * 2 ^ (z - h)

/-- Inner `for h in 0..z` carry-pop loop: while `len[h] >= 16`, hashes 8 sibling pairs
    at level `h` into 8 parent nodes at level `h + 1` and advances `next_idx[h + 1] += 8`. -/
def popLoop (p : Params) (pk : Bytes) (adrs : Adrs) (z h : Nat) (st : StackState) : StackState :=
  if h < z then
    if (st.buf h).length < 16 then st
    else
      let base := st.nextIdx (h + 1)
      let parents := (List.range 8).map fun k =>
        H p pk { adrs with word2 := h + 1, word3 := base + k }
          ((st.buf h)[2 * k]! ++ (st.buf h)[2 * k + 1]!)
      let st' : StackState := {
        buf := fun lvl =>
          if lvl = h then []
          else if lvl = h + 1 then st.buf (h + 1) ++ parents
          else st.buf lvl
        nextIdx := fun lvl =>
          if lvl = h + 1 then base + 8 else st.nextIdx lvl
      }
      popLoop p pk adrs z (h + 1) st'
  else st
termination_by z - h

/-- One iteration `b` of the outer `for b in 0..blocks` loop: computes 8 fused FORS
    leaves and pushes them into `buf[0]`, then runs `popLoop`. -/
def pushBlock (p : Params) (sk pk : Bytes) (adrs : Adrs) (nodeIndex z b : Nat)
    (st : StackState) : StackState :=
  let firstLeaf := nodeIndex * 2 ^ z
  let leaves := (List.range 8).map fun lane =>
    forsNode p sk (firstLeaf + b * 8 + lane) 0 pk adrs
  let st0 : StackState := {
    buf := fun lvl => if lvl = 0 then st.buf 0 ++ leaves else st.buf lvl
    nextIdx := st.nextIdx
  }
  popLoop p pk adrs z 0 st0

/-- Outer loop over `m` blocks of 8 leaves (`0 ..< m`). -/
def mainLoop (p : Params) (sk pk : Bytes) (adrs : Adrs) (nodeIndex z : Nat) :
    Nat → StackState
  | 0 => initStack nodeIndex z
  | m + 1 => pushBlock p sk pk adrs nodeIndex z m (mainLoop p sk pk adrs nodeIndex z m)

/-- One iteration of the final `for h in 0..z` tail reduction loop (handles both
    `count == 0`, `count == 1` via `thash_pair`, and `count >= 2` via `pair_active`). -/
def tailStep (p : Params) (pk : Bytes) (adrs : Adrs) (st : StackState) (h : Nat) : StackState :=
  let count := (st.buf h).length / 2
  if count = 0 then st
  else
    let base := st.nextIdx (h + 1)
    let parents :=
      if count = 1 then
        [H p pk { adrs with word2 := h + 1, word3 := base }
          ((st.buf h)[0]! ++ (st.buf h)[1]!)]
      else
        (List.range count).map fun k =>
          H p pk { adrs with word2 := h + 1, word3 := base + k }
            ((st.buf h)[2 * k]! ++ (st.buf h)[2 * k + 1]!)
    {
      buf := fun lvl =>
        if lvl = h then []
        else if lvl = h + 1 then st.buf (h + 1) ++ parents
        else st.buf lvl
      nextIdx := fun lvl =>
        if lvl = h + 1 then base + count else st.nextIdx lvl
    }

/-- Final tail reduction loop over `h ∈ 0..z`. -/
def tailLoop (p : Params) (pk : Bytes) (adrs : Adrs) (z : Nat) (st : StackState) : StackState :=
  (List.range z).foldl (tailStep p pk adrs) st

/-- Complete model of `fors_batch::fors_subtree_horiz` for `z >= 3`. -/
def forsSubtreeHoriz (p : Params) (sk pk : Bytes) (adrs : Adrs) (nodeIndex z : Nat) : Bytes :=
  let st := mainLoop p sk pk adrs nodeIndex z (2 ^ (z - 3))
  ((tailLoop p pk adrs z st).buf z).headD []

/-- Total number of nodes produced at height `h` after `m` blocks of 8 leaves. -/
private def produced (nodeIndex z m h : Nat) : Nat :=
  nodeIndex * 2 ^ (z - h) + 8 * (m / 2 ^ h)

/-- Exact binary-carry stack invariant after `m` blocks (`0 ≤ m ≤ 2^(z - 3)`). -/
private def StackInv (p : Params) (sk pk : Bytes) (adrs : Adrs) (nodeIndex z m : Nat)
    (st : StackState) : Prop :=
  ∀ h ≤ z,
    let prod := produced nodeIndex z m h
    (st.buf h).length = 8 * ((m / 2 ^ h) % 2) ∧
    (1 ≤ h → st.nextIdx h = prod) ∧
    (∀ k < (st.buf h).length,
      (st.buf h)[k]! = forsNode p sk (prod - (st.buf h).length + k) h pk adrs)

/-- Intermediate carry invariant inside `popLoop` at level `h`: levels `< h` are already
    updated to `m + 1` (and empty), level `h` holds its previous `8 * ((m / 2^h) % 2)` nodes
    plus 8 newly carried nodes, and levels `> h` still hold state `m`. -/
private def CarryInv (p : Params) (sk pk : Bytes) (adrs : Adrs) (nodeIndex z m h : Nat)
    (st : StackState) : Prop :=
  h ≤ z ∧
  2 ^ h ∣ m + 1 ∧
  (∀ lvl < h,
    (st.buf lvl) = [] ∧
    (1 ≤ lvl → st.nextIdx lvl = produced nodeIndex z (m + 1) lvl)) ∧
  ((st.buf h).length = 8 * ((m / 2 ^ h) % 2) + 8 ∧
    (1 ≤ h → st.nextIdx h = produced nodeIndex z (m + 1) h) ∧
    (∀ k < (st.buf h).length,
      (st.buf h)[k]! =
        forsNode p sk (produced nodeIndex z (m + 1) h - (st.buf h).length + k) h pk adrs)) ∧
  (∀ lvl, h < lvl → lvl ≤ z →
    let prod := produced nodeIndex z m lvl
    (st.buf lvl).length = 8 * ((m / 2 ^ lvl) % 2) ∧
    st.nextIdx lvl = prod ∧
    (∀ k < (st.buf lvl).length,
      (st.buf lvl)[k]! = forsNode p sk (prod - (st.buf lvl).length + k) lvl pk adrs))

private theorem div_succ_of_dvd {m h : Nat} (hdvd : 2 ^ h ∣ m + 1) :
    (m + 1) / 2 ^ h = m / 2 ^ h + 1 := by
  rcases hdvd with ⟨q, hq⟩
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  cases q with
  | zero => omega
  | succ q' =>
    have hm : m = q' * 2 ^ h + (2 ^ h - 1) := by
      have : m + 1 = 2 ^ h * q' + 2 ^ h := by rw [hq, Nat.mul_succ]
      rw [Nat.mul_comm] at this
      omega
    have h1 : (m + 1) / 2 ^ h = q' + 1 := by
      rw [hq, Nat.mul_div_right _ hpos]
    have h2 : m / 2 ^ h = q' := by
      rw [hm, Nat.mul_comm q' (2 ^ h), Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    omega

private theorem div_succ_higher_eq {m h lvl : Nat} (hdvd : 2 ^ h ∣ m + 1)
    (heven : (m / 2 ^ h) % 2 = 0) (hlt : h < lvl) :
    (m + 1) / 2 ^ lvl = m / 2 ^ lvl := by
  have hstep : (m + 1) / 2 ^ (h + 1) = m / 2 ^ (h + 1) := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      div_succ_of_dvd hdvd]
    omega
  have hdiff : lvl = (h + 1) + (lvl - (h + 1)) := by omega
  rw [hdiff, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hstep]

private theorem dvd_next_of_odd {m h : Nat} (hdvd : 2 ^ h ∣ m + 1)
    (hodd : (m / 2 ^ h) % 2 ≠ 0) :
    2 ^ (h + 1) ∣ m + 1 := by
  rcases hdvd with ⟨q, hq⟩
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  have hq_div : (m + 1) / 2 ^ h = q := by rw [hq, Nat.mul_div_right _ hpos]
  have hq_even : q % 2 = 0 := by
    have := div_succ_of_dvd (m := m) (h := h) ⟨q, hq⟩
    omega
  refine ⟨q / 2, ?_⟩
  rw [Nat.pow_succ, Nat.mul_assoc, hq]
  congr 1
  omega

private theorem popLoop_preserves (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (nodeIndex z m : Nat) (hz : 3 ≤ z) (hm : m < 2 ^ (z - 3))
    (h : Nat) (st : StackState) (hcarry : CarryInv p sk pk adrs nodeIndex z m h st) :
    StackInv p sk pk adrs nodeIndex z (m + 1) (popLoop p pk adrs z h st) := by
  rcases hcarry with ⟨hle, hdvd, hbelow, ⟨hlen, hidx_h, hbuf_h⟩, habove⟩
  -- Prove h < z because 2^h ∣ m + 1 ≤ 2^(z - 3) < 2^z.
  have hle_top : 2 ^ h ≤ 2 ^ (z - 3) := by
    have hpos : 0 < m + 1 := Nat.succ_pos m
    exact Nat.le_trans (Nat.le_of_dvd hpos hdvd) hm
  have hlt_z3 : h ≤ z - 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle_top
  have hlt_z : h < z := by omega
  unfold popLoop
  simp only [hlt_z, ↓reduceIte]
  by_cases hmod : (m / 2 ^ h) % 2 = 0
  · -- Length at level h is 8 < 16: popLoop terminates immediately!
    have hlen8 : (st.buf h).length = 8 := by omega
    simp only [hlen8, show (8 : Nat) < 16 by decide, ↓reduceIte]
    intro lvl hlvl
    by_cases hlt : lvl < h
    · obtain ⟨hnil, hni⟩ := hbelow lvl hlt
      have hdvd_lvl : 2 ^ (lvl + 1) ∣ m + 1 :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
      have hzero : ((m + 1) / 2 ^ lvl) % 2 = 0 := by
        rcases hdvd_lvl with ⟨q, hq⟩
        rw [hq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_right _ (Nat.two_pow_pos lvl)]
        omega
      refine ⟨by simp [hnil, hzero], hni, fun k hk => by simp [hnil] at hk⟩
    · by_cases heq : lvl = h
      · subst heq
        have hmod1 : ((m + 1) / 2 ^ lvl) % 2 = 1 := by
          rw [div_succ_of_dvd hdvd]; omega
        exact ⟨by omega, hidx_h, hbuf_h⟩
      · have hgt : h < lvl := by omega
        obtain ⟨hl, hni, hb⟩ := habove lvl hgt hlvl
        have hdiv_eq : (m + 1) / 2 ^ lvl = m / 2 ^ lvl :=
          div_succ_higher_eq hdvd hmod hgt
        have hprod_eq : produced nodeIndex z (m + 1) lvl = produced nodeIndex z m lvl := by
          simp [produced, hdiv_eq]
        refine ⟨by rw [hdiv_eq]; exact hl, fun _ => by rw [hprod_eq]; exact hni, ?_⟩
        rw [hprod_eq]
        exact hb
  · -- Length at level h is 16: pop 16 nodes into 8 parents at level h + 1 and carry!
    have hlen16 : (st.buf h).length = 16 := by omega
    have hnot16 : ¬ (st.buf h).length < 16 := by omega
    simp only [hnot16, ↓reduceIte]
    have hdvd_next : 2 ^ (h + 1) ∣ m + 1 := dvd_next_of_odd hdvd hmod
    have hsucc_le : h + 1 ≤ z := by omega
    obtain ⟨hl_next, hni_next, hb_next⟩ := habove (h + 1) (Nat.lt_succ_self h) hsucc_le
    apply popLoop_preserves p sk pk adrs nodeIndex z m hz hm (h + 1) _
    refine ⟨hsucc_le, hdvd_next, ?_, ?_, ?_⟩
    · -- Below h + 1
      intro lvl hlvl
      by_cases heq : lvl = h
      · subst heq
        simp only [↓reduceIte, show lvl ≠ lvl + 1 by omega, true_and]
        exact hidx_h
      · have hlt : lvl < h := by omega
        have hne1 : lvl ≠ h + 1 := by omega
        simp only [heq, hne1, ↓reduceIte]
        exact hbelow lvl hlt
    · -- At level h + 1
      have hne : h + 1 ≠ h := by omega
      simp only [hne, ↓reduceIte]
      have hprod_next : produced nodeIndex z (m + 1) (h + 1) =
          produced nodeIndex z m (h + 1) + 8 := by
        simp only [produced, div_succ_of_dvd hdvd_next]
        ring
      have hprod_h : produced nodeIndex z (m + 1) h =
          2 * produced nodeIndex z (m + 1) (h + 1) := by
        simp only [produced]
        have hsub : z - h = (z - (h + 1)) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        have hdiv2 : (m + 1) / 2 ^ h = 2 * ((m + 1) / 2 ^ (h + 1)) := by
          rcases hdvd_next with ⟨q, hq⟩
          have h1 : (m + 1) / 2 ^ (h + 1) = q := by
            rw [hq, Nat.mul_div_right _ (Nat.two_pow_pos (h + 1))]
          have h2 : (m + 1) / 2 ^ h = 2 * q := by
            rw [hq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_right _ (Nat.two_pow_pos h)]
          rw [h1, h2]
        rw [hdiv2]
        ring
      refine ⟨?_, ?_, ?_⟩
      · simp [hl_next]
      · intro _; rw [hni_next, hprod_next]
      · intro k hk
        simp only [List.length_append, List.length_map, List.length_range] at hk
        have hle_prod : (st.buf (h + 1)).length ≤ produced nodeIndex z m (h + 1) := by
          rw [hl_next]
          simp only [produced]
          have := Nat.mod_le (m / 2 ^ (h + 1)) 2
          omega
        by_cases hk_old : k < (st.buf (h + 1)).length
        · rw [getElem!_pos (st.buf (h + 1) ++ _) k (by simp; omega), List.getElem_append_left hk_old]
          have hget := hb_next k hk_old
          rw [getElem!_pos (st.buf (h + 1)) k hk_old] at hget
          rw [hget]
          congr 1
          simp only [List.length_append, List.length_map, List.length_range]
          rw [hprod_next]
          omega
        · have hk_new : k - (st.buf (h + 1)).length < 8 := by omega
          rw [getElem!_pos (st.buf (h + 1) ++ _) k (by simp; omega),
            List.getElem_append_right (Nat.le_of_not_lt hk_old)]
          simp only [List.getElem_map, List.getElem_range]
          set j := k - (st.buf (h + 1)).length
          have h2j : 2 * j < (st.buf h).length := by omega
          have h2j1 : 2 * j + 1 < (st.buf h).length := by omega
          rw [hbuf_h (2 * j) h2j, hbuf_h (2 * j + 1) h2j1, hlen16, hni_next]
          have hidx_eq : produced nodeIndex z m (h + 1) + j =
              produced nodeIndex z (m + 1) (h + 1) - ((st.buf (h + 1)).length + 8) + k := by
            rw [hprod_next]; omega
          have hleft : produced nodeIndex z (m + 1) h - 16 + 2 * j =
              2 * (produced nodeIndex z m (h + 1) + j) := by
            rw [hprod_h, hprod_next]; omega
          have hright : produced nodeIndex z (m + 1) h - 16 + (2 * j + 1) =
              2 * (produced nodeIndex z m (h + 1) + j) + 1 := by
            rw [hprod_h, hprod_next]; omega
          rw [hleft, hright]
          simp only [List.length_append, List.length_map, List.length_range]
          rw [← hidx_eq]
          rfl
    · -- Above h + 1
      intro lvl hgt hlvl
      have hne1 : lvl ≠ h := by omega
      have hne2 : lvl ≠ h + 1 := by omega
      simp only [hne1, hne2, ↓reduceIte]
      exact habove lvl (by omega) hlvl
termination_by z - h

private theorem mainLoop_inv (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (nodeIndex z : Nat) (hz : 3 ≤ z) :
    ∀ m ≤ 2 ^ (z - 3), StackInv p sk pk adrs nodeIndex z m (mainLoop p sk pk adrs nodeIndex z m)
  | 0, _ => by
    intro h _
    simp [mainLoop, initStack, produced]
  | m + 1, hm => by
    have ih := mainLoop_inv p sk pk adrs nodeIndex z hz m (by omega)
    unfold mainLoop pushBlock
    apply popLoop_preserves p sk pk adrs nodeIndex z m hz (by omega) 0 _
    refine ⟨Nat.zero_le z, Nat.one_dvd _, fun _ h => by omega, ?_, ?_⟩
    · obtain ⟨hl0, _, hb0⟩ := ih 0 (Nat.zero_le z)
      simp only [↓reduceIte]
      refine ⟨by simp [hl0], fun h0 => by omega, ?_⟩
      intro k hk
      simp only [List.length_append, List.length_map, List.length_range] at hk
      have hprod0 : produced nodeIndex z (m + 1) 0 = produced nodeIndex z m 0 + 8 := by
        simp [produced]; ring
      have hle_prod0 : ((mainLoop p sk pk adrs nodeIndex z m).buf 0).length ≤ produced nodeIndex z m 0 := by
        rw [hl0]; simp only [produced, Nat.pow_zero, Nat.div_one]
        have := Nat.mod_le m 2; omega
      by_cases hk_old : k < ((mainLoop p sk pk adrs nodeIndex z m).buf 0).length
      · rw [getElem!_pos ((mainLoop p sk pk adrs nodeIndex z m).buf 0 ++ _) k (by simp; omega),
          List.getElem_append_left hk_old]
        have hget := hb0 k hk_old
        rw [getElem!_pos ((mainLoop p sk pk adrs nodeIndex z m).buf 0) k hk_old] at hget
        rw [hget]
        congr 1
        simp only [List.length_append, List.length_map, List.length_range]
        rw [hprod0]; omega
      · rw [getElem!_pos ((mainLoop p sk pk adrs nodeIndex z m).buf 0 ++ _) k (by simp; omega),
          List.getElem_append_right (Nat.le_of_not_lt hk_old)]
        simp only [List.getElem_map, List.getElem_range]
        congr 1
        simp only [List.length_append, List.length_map, List.length_range, produced, Nat.sub_zero,
          Nat.pow_zero, Nat.div_one]
        omega
    · intro lvl hgt hlvl
      have hne : lvl ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      obtain ⟨hl, hni, hb⟩ := ih lvl hlvl
      exact ⟨hl, hni (by omega), hb⟩

private theorem tailLoop_skip_prefix (p : Params) (pk : Bytes) (adrs : Adrs)
    (st : StackState) (n : Nat) (hempty : ∀ h < n, (st.buf h).length = 0) :
    (List.range n).foldl (tailStep p pk adrs) st = st := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (fun h hh => hempty h (by omega))]
    simp [tailStep, hempty n (Nat.lt_succ_self n)]

/-- **Headline Theorem (FORS Horizontal TreeHash)**:
    For every `height >= 3`, `fors_subtree_horiz` computes the exact FIPS 205 Algorithm 15
    subtree root `Spec.forsNode p sk nodeIndex height pk adrs`. -/
theorem fors_subtree_horiz_eq (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (nodeIndex z : Nat) (hz : 3 ≤ z) :
    forsSubtreeHoriz p sk pk adrs nodeIndex z = forsNode p sk nodeIndex z pk adrs := by
  unfold forsSubtreeHoriz tailLoop
  dsimp only
  set st := mainLoop p sk pk adrs nodeIndex z (2 ^ (z - 3))
  have hinv := mainLoop_inv p sk pk adrs nodeIndex z hz (2 ^ (z - 3)) (Nat.le_refl _)
  have hsplit : z = (z - 3) + 3 := by omega
  have hrange : List.range z = List.range (z - 3) ++ [z - 3, z - 2, z - 1] := by
    have : List.range ((z - 3) + 3) = List.range (z - 3) ++ [z - 3, z - 2, z - 1] := by
      simp [List.range_succ, List.append_assoc]
      omega
    simpa [← hsplit] using this
  rw [hrange, List.foldl_append]
  -- 1. Levels 0 ..< z - 3 are all empty so tailStep is a no-op on them.
  have hempty_lo : ∀ h < z - 3, (st.buf h).length = 0 := by
    intro h hh
    have hlen := (hinv h (by omega)).1
    have hpow : 2 ^ (z - 3) = 2 ^ h * 2 ^ (z - 3 - h) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hh)]
    have hge1 : z - 3 - h = (z - 3 - h - 1) + 1 := by omega
    have hmod0 : 2 ^ (z - 3) / 2 ^ h % 2 = 0 := by
      rw [hpow, Nat.mul_div_right _ (Nat.two_pow_pos h), hge1, Nat.pow_succ]
      omega
    simpa [st, hmod0] using hlen
  rw [tailLoop_skip_prefix p pk adrs st (z - 3) hempty_lo]
  -- Extract exact contents at levels z-3, z-2, z-1, z from hinv.
  have h3 := hinv (z - 3) (by omega)
  have h2 := hinv (z - 2) (by omega)
  have h1 := hinv (z - 1) (by omega)
  have h0 := hinv z (Nat.le_refl z)
  have hdiv3 : 2 ^ (z - 3) / 2 ^ (z - 3) = 1 := Nat.div_self (Nat.two_pow_pos _)
  have hdiv2 : 2 ^ (z - 3) / 2 ^ (z - 2) = 0 :=
    Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hdiv1 : 2 ^ (z - 3) / 2 ^ (z - 1) = 0 :=
    Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hdiv0 : 2 ^ (z - 3) / 2 ^ z = 0 :=
    Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hlen3 : (st.buf (z - 3)).length = 8 := by simpa [hdiv3] using h3.1
  have hbuf3 : ∀ k < 8, (st.buf (z - 3))[k]! = forsNode p sk (8 * nodeIndex + k) (z - 3) pk adrs := by
    intro k hk
    have hb : (st.buf (z - 3))[k]! =
        forsNode p sk (produced nodeIndex z (2 ^ (z - 3)) (z - 3) - (st.buf (z - 3)).length + k) (z - 3) pk adrs :=
      h3.2.2 k (by omega)
    rw [hlen3] at hb
    simp only [produced, hdiv3, show z - (z - 3) = 3 by omega, show (2 : Nat) ^ 3 = 8 by decide] at hb
    convert hb using 2; omega
  have hlen2 : (st.buf (z - 2)).length = 0 := by simpa [hdiv2] using h2.1
  have hnil2 : st.buf (z - 2) = [] := List.eq_nil_of_length_eq_zero hlen2
  have hidx2 : st.nextIdx (z - 2) = 4 * nodeIndex := by
    have hni : st.nextIdx (z - 2) = produced nodeIndex z (2 ^ (z - 3)) (z - 2) := h2.2.1 (by omega)
    simp only [produced, hdiv2, show z - (z - 2) = 2 by omega, show (2 : Nat) ^ 2 = 4 by decide] at hni
    omega
  have hlen1 : (st.buf (z - 1)).length = 0 := by simpa [hdiv1] using h1.1
  have hnil1 : st.buf (z - 1) = [] := List.eq_nil_of_length_eq_zero hlen1
  have hidx1 : st.nextIdx (z - 1) = 2 * nodeIndex := by
    have hni : st.nextIdx (z - 1) = produced nodeIndex z (2 ^ (z - 3)) (z - 1) := h1.2.1 (by omega)
    simp only [produced, hdiv1, show z - (z - 1) = 1 by omega, Nat.pow_one] at hni
    omega
  have hlen0 : (st.buf z).length = 0 := by simpa [hdiv0] using h0.1
  have hnil0 : st.buf z = [] := List.eq_nil_of_length_eq_zero hlen0
  have hidx0 : st.nextIdx z = nodeIndex := by
    have hni : st.nextIdx z = produced nodeIndex z (2 ^ (z - 3)) z := h0.2.1 (by omega)
    simp only [produced, hdiv0, Nat.sub_self, Nat.pow_zero] at hni
    omega
  -- 2. Execute the 3 tail steps: count = 4 (z-3 -> z-2), count = 2 (z-2 -> z-1), count = 1 (z-1 -> z).
  simp only [List.foldl_cons, List.foldl_nil]
  -- Step 1: h = z - 3 (count = 4, pair_active branch)
  have hstep1 :
      let st1 := tailStep p pk adrs st (z - 3)
      st1.buf (z - 2) = (List.range 4).map (fun k => forsNode p sk (4 * nodeIndex + k) (z - 2) pk adrs) ∧
      st1.buf (z - 1) = [] ∧ st1.buf z = [] ∧
      st1.nextIdx (z - 1) = 2 * nodeIndex ∧ st1.nextIdx z = nodeIndex := by
    simp only [tailStep, hlen3, show (8 : Nat) / 2 = 4 by decide,
      show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide, ↓reduceIte,
      show z - 3 + 1 = z - 2 by omega, hnil2, List.nil_append, hidx2,
      show z - 2 ≠ z - 3 by omega, show z - 1 ≠ z - 3 by omega, show z - 1 ≠ z - 2 by omega,
      show z ≠ z - 3 by omega, show z ≠ z - 2 by omega, hnil1, hnil0, hidx1, hidx0]
    refine ⟨?_, trivial, trivial, trivial, trivial⟩
    apply List.map_congr_left
    intro k hk
    have hk4 : k < 4 := List.mem_range.mp hk
    rw [hbuf3 (2 * k) (by omega), hbuf3 (2 * k + 1) (by omega)]
    have hz2 : z - 2 = (z - 3) + 1 := by omega
    rw [hz2, forsNode]
    congr 2
    · congr 1; omega
    · congr 1; omega
  rcases hstep1 with ⟨h1_b2, h1_b1, h1_b0, h1_i1, h1_i0⟩
  set st1 := tailStep p pk adrs st (z - 3)
  -- Step 2: h = z - 2 (count = 2, pair_active branch)
  have hstep2 :
      let st2 := tailStep p pk adrs st1 (z - 2)
      st2.buf (z - 1) = (List.range 2).map (fun k => forsNode p sk (2 * nodeIndex + k) (z - 1) pk adrs) ∧
      st2.buf z = [] ∧ st2.nextIdx z = nodeIndex := by
    simp only [tailStep, h1_b2, List.length_map, List.length_range,
      show (4 : Nat) / 2 = 2 by decide, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide, ↓reduceIte,
      show z - 2 + 1 = z - 1 by omega, h1_b1, List.nil_append, h1_i1,
      show z - 1 ≠ z - 2 by omega, show z ≠ z - 2 by omega, show z ≠ z - 1 by omega,
      h1_b0, h1_i0]
    refine ⟨?_, trivial, trivial⟩
    apply List.map_congr_left
    intro k hk
    have hk2 : k < 2 := List.mem_range.mp hk
    have he1 : ((List.range 4).map (fun j => forsNode p sk (4 * nodeIndex + j) (z - 2) pk adrs))[2 * k]! =
        forsNode p sk (2 * (2 * nodeIndex + k)) (z - 2) pk adrs := by
      rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
      congr 1; omega
    have he2 : ((List.range 4).map (fun j => forsNode p sk (4 * nodeIndex + j) (z - 2) pk adrs))[2 * k + 1]! =
        forsNode p sk (2 * (2 * nodeIndex + k) + 1) (z - 2) pk adrs := by
      rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
      congr 1; omega
    rw [he1, he2]
    have hz1 : z - 1 = (z - 2) + 1 := by omega
    rw [hz1, forsNode]
  rcases hstep2 with ⟨h2_b1, h2_b0, h2_i0⟩
  set st2 := tailStep p pk adrs st1 (z - 2)
  -- Step 3: h = z - 1 (count = 1, thash_pair branch)
  simp only [tailStep, h2_b1, List.length_map, List.length_range,
    show (2 : Nat) / 2 = 1 by decide, show (1 : Nat) ≠ 0 by decide, ↓reduceIte,
    show z - 1 + 1 = z by omega, h2_b0, List.nil_append, h2_i0,
    show z ≠ z - 1 by omega]
  have heL : ((List.range 2).map (fun j => forsNode p sk (2 * nodeIndex + j) (z - 1) pk adrs))[0]! =
      forsNode p sk (2 * nodeIndex) (z - 1) pk adrs := by
    rw [getElem!_pos _ _ (by simp), List.getElem_map, List.getElem_range]
    simp
  have heR : ((List.range 2).map (fun j => forsNode p sk (2 * nodeIndex + j) (z - 1) pk adrs))[1]! =
      forsNode p sk (2 * nodeIndex + 1) (z - 1) pk adrs := by
    rw [getElem!_pos _ _ (by simp), List.getElem_map, List.getElem_range]
  rw [heL, heR]
  have hz0 : z = (z - 1) + 1 := by omega
  conv_rhs => rw [hz0, forsNode]
  simp [List.headD, ← hz0]

/-! ## Part 2: Cross-Tree Batching (Heights 0..=2) and `fors_batch::sign` (Algorithm 16) -/

/-- Model of `batch_leaves_slice`: computes `forsNode ... idx 0` in active batches of `width`. -/
def batchLeavesSlice (width : Nat) (hw : 0 < width) (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (indices : List Nat) : List Bytes :=
  batchChunks width indices.length hw (fun i => forsNode p sk indices[i]! 0 pk adrs)

theorem batchLeavesSlice_eq (width : Nat) (hw : 0 < width) (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (indices : List Nat) :
    batchLeavesSlice width hw p sk pk adrs indices =
      indices.map (fun idx => forsNode p sk idx 0 pk adrs) := by
  unfold batchLeavesSlice
  rw [batchChunks_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [getElem!_pos _ _ (by simpa using h2)]

/-- Model of `batch_pairs_slice`: computes `H p pk {adrs with word2 := level, word3 := idx}`
    for adjacent child pairs in active batches of `width`. -/
def batchPairsSlice (width : Nat) (hw : 0 < width) (p : Params) (pk : Bytes) (adrs : Adrs)
    (level : Nat) (nodeIndices : List Nat) (children : List Bytes) : List Bytes :=
  batchChunks width nodeIndices.length hw (fun i =>
    H p pk { adrs with word2 := level, word3 := nodeIndices[i]! }
      (children[2 * i]! ++ children[2 * i + 1]!))

theorem batchPairsSlice_eq (width : Nat) (hw : 0 < width) (p : Params) (pk : Bytes) (adrs : Adrs)
    (level : Nat) (nodeIndices : List Nat) (children : List Bytes) :
    batchPairsSlice width hw p pk adrs level nodeIndices children =
      (List.range nodeIndices.length).map (fun i =>
        H p pk { adrs with word2 := level, word3 := nodeIndices[i]! }
          (children[2 * i]! ++ children[2 * i + 1]!)) :=
  batchChunks_eq width nodeIndices.length hw _

/-- Cross-tree height-0 sibling leaves across all `k` trees (`fors_batch::sign` lines 280–291). -/
def crossTreeHeight0 (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat) : List Bytes :=
  let idx0 := (List.range p.k).map fun tree => (tree * 2 ^ p.a + selections[tree]!) ^^^ 1
  batchLeavesSlice 8 (by decide) p sk pk adrs idx0

theorem crossTreeHeight0_get (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat)
    (ha : 0 < p.a) (tree : Nat) (ht : tree < p.k) :
    (crossTreeHeight0 p sk pk adrs selections)[tree]! =
      forsNode p sk (tree * 2 ^ p.a + (selections[tree]! ^^^ 1)) 0 pk adrs := by
  unfold crossTreeHeight0
  rw [batchLeavesSlice_eq, List.map_map]
  rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  simp only [Function.comp_apply]
  have h := fors_sibling_index tree p.a selections[tree]! 0 ha
  simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero] at h
  rw [h]

/-- Cross-tree height-1 sibling nodes (`2k` leaves -> `k` level-1 parents, lines 293–317). -/
def crossTreeHeight1 (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat) : List Bytes :=
  let sib (tree : Nat) := ((tree * 2 ^ p.a + selections[tree]!) / 2) ^^^ 1
  let nodeIdx := (List.range p.k).map sib
  let leafIdx := (List.range (2 * p.k)).map fun j => 2 * sib (j / 2) + j % 2
  let leaves := batchLeavesSlice 8 (by decide) p sk pk adrs leafIdx
  batchPairsSlice 8 (by decide) p pk adrs 1 nodeIdx leaves

theorem crossTreeHeight1_get (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat)
    (ha : 1 < p.a) (tree : Nat) (ht : tree < p.k) :
    (crossTreeHeight1 p sk pk adrs selections)[tree]! =
      forsNode p sk (tree * 2 ^ (p.a - 1) + ((selections[tree]! / 2) ^^^ 1)) 1 pk adrs := by
  unfold crossTreeHeight1 batchPairsSlice
  dsimp only
  rw [batchLeavesSlice_eq, batchChunks_eq]
  simp only [List.length_map, List.length_range]
  rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hn : ((List.range p.k).map fun t => ((t * 2 ^ p.a + selections[t]!) / 2) ^^^ 1)[tree]! =
      ((tree * 2 ^ p.a + selections[tree]!) / 2) ^^^ 1 := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hL : (((List.range (2 * p.k)).map fun j =>
      2 * (((j / 2 * 2 ^ p.a + selections[j / 2]!) / 2) ^^^ 1) + j % 2).map
      fun idx => forsNode p sk idx 0 pk adrs)[2 * tree]! =
      forsNode p sk (2 * (((tree * 2 ^ p.a + selections[tree]!) / 2) ^^^ 1)) 0 pk adrs := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_map, List.getElem_range]
    simp [show 2 * tree / 2 = tree by omega, show 2 * tree % 2 = 0 by omega]
  have hR : (((List.range (2 * p.k)).map fun j =>
      2 * (((j / 2 * 2 ^ p.a + selections[j / 2]!) / 2) ^^^ 1) + j % 2).map
      fun idx => forsNode p sk idx 0 pk adrs)[2 * tree + 1]! =
      forsNode p sk (2 * (((tree * 2 ^ p.a + selections[tree]!) / 2) ^^^ 1) + 1) 0 pk adrs := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_map, List.getElem_range]
    simp [show (2 * tree + 1) / 2 = tree by omega, show (2 * tree + 1) % 2 = 1 by omega]
  rw [hn, hL, hR]
  have hsib := fors_sibling_index tree p.a selections[tree]! 1 ha
  simp only [Nat.pow_one] at hsib
  rw [hsib]
  rfl

/-- Cross-tree height-2 sibling nodes (`4k` leaves -> `2k` lvl1 -> `k` lvl2, lines 319–356). -/
def crossTreeHeight2 (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat) : List Bytes :=
  let sib (tree : Nat) := ((tree * 2 ^ p.a + selections[tree]!) / 4) ^^^ 1
  let n2Idx := (List.range p.k).map sib
  let n1Idx := (List.range (2 * p.k)).map fun j => 2 * sib (j / 2) + j % 2
  let leafIdx := (List.range (4 * p.k)).map fun j => 4 * sib (j / 4) + j % 4
  let leaves := batchLeavesSlice 8 (by decide) p sk pk adrs leafIdx
  let lvl1 := batchPairsSlice 8 (by decide) p pk adrs 1 n1Idx leaves
  batchPairsSlice 8 (by decide) p pk adrs 2 n2Idx lvl1

theorem crossTreeHeight2_get (p : Params) (sk pk : Bytes) (adrs : Adrs) (selections : List Nat)
    (ha : 2 < p.a) (tree : Nat) (ht : tree < p.k) :
    (crossTreeHeight2 p sk pk adrs selections)[tree]! =
      forsNode p sk (tree * 2 ^ (p.a - 2) + ((selections[tree]! / 4) ^^^ 1)) 2 pk adrs := by
  unfold crossTreeHeight2 batchPairsSlice
  dsimp only
  rw [batchLeavesSlice_eq, batchChunks_eq, batchChunks_eq]
  simp only [List.length_map, List.length_range]
  rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  set sib := fun t => ((t * 2 ^ p.a + selections[t]!) / 4) ^^^ 1
  have hn2 : ((List.range p.k).map sib)[tree]! = sib tree := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hleaf : ∀ c < 4,
      (((List.range (4 * p.k)).map fun j => 4 * sib (j / 4) + j % 4).map
        fun idx => forsNode p sk idx 0 pk adrs)[4 * tree + c]! =
      forsNode p sk (4 * sib tree + c) 0 pk adrs := by
    intro c hc
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_map, List.getElem_range]
    simp [show (4 * tree + c) / 4 = tree by omega, show (4 * tree + c) % 4 = c by omega]
  have hlvl1 : ∀ b < 2,
      ((List.range (2 * p.k)).map fun i =>
        H p pk { adrs with word2 := 1, word3 := ((List.range (2 * p.k)).map fun j => 2 * sib (j / 2) + j % 2)[i]! }
          ((((List.range (4 * p.k)).map fun j => 4 * sib (j / 4) + j % 4).map
            fun idx => forsNode p sk idx 0 pk adrs)[2 * i]! ++
           (((List.range (4 * p.k)).map fun j => 4 * sib (j / 4) + j % 4).map
            fun idx => forsNode p sk idx 0 pk adrs)[2 * i + 1]!))[2 * tree + b]! =
      forsNode p sk (2 * sib tree + b) 1 pk adrs := by
    intro b hb
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    have hni : ((List.range (2 * p.k)).map fun j => 2 * sib (j / 2) + j % 2)[2 * tree + b]! =
        2 * sib tree + b := by
      rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
      simp [show (2 * tree + b) / 2 = tree by omega, show (2 * tree + b) % 2 = b by omega]
    rw [hni]
    have hL := hleaf (2 * b) (by omega)
    have hR := hleaf (2 * b + 1) (by omega)
    rw [show 2 * (2 * tree + b) = 4 * tree + 2 * b by omega,
        show 4 * tree + 2 * b + 1 = 4 * tree + (2 * b + 1) by omega, hL, hR]
    have h2L : 4 * sib tree + 2 * b = 2 * (2 * sib tree + b) := by omega
    have h2R : 4 * sib tree + (2 * b + 1) = 2 * (2 * sib tree + b) + 1 := by omega
    rw [h2L, h2R]; rfl
  have h2L := hlvl1 0 (by decide)
  have h2R := hlvl1 1 (by decide)
  simp only [Nat.add_zero] at h2L
  rw [hn2]
  change H p pk { adrs with word2 := 2, word3 := sib tree } _ = _
  rw [h2L, h2R]
  have hsib : sib tree = tree * 2 ^ (p.a - 2) + (selections[tree]! / 4 ^^^ 1) := by
    simpa [sib, show (2 : Nat) ^ 2 = 4 by decide] using
      fors_sibling_index tree p.a selections[tree]! 2 ha
  rw [hsib]; rfl

/-- Complete model of `fors_batch::sign` on the `WIDTH == 8` horizontal path:
    1. Batched `FORS_PRF` secret values across all `k` trees;
    2. Cross-tree heights `0`, `1`, `2` (`crossTreeHeight0/1/2`);
    3. Heights `3..a` via `forsSubtreeHoriz`. -/
def forsSignHoriz (p : Params) (md sk pk : Bytes) (adrs : Adrs) : Bytes :=
  let selections := base2b md p.a p.k
  let secrets := batchChunks 8 p.k (by decide) fun tree =>
    forsSkGen p sk pk adrs (tree * 2 ^ p.a + selections[tree]!)
  let h0 := crossTreeHeight0 p sk pk adrs selections
  let h1 := crossTreeHeight1 p sk pk adrs selections
  let h2 := crossTreeHeight2 p sk pk adrs selections
  (List.range p.k).flatMap fun tree =>
    secrets[tree]! ++
      (List.range p.a).flatMap fun j =>
        if j = 0 then h0[tree]!
        else if j = 1 then h1[tree]!
        else if j = 2 then h2[tree]!
        else forsSubtreeHoriz p sk pk adrs (((tree * 2 ^ p.a + selections[tree]!) / 2 ^ j) ^^^ 1) j

/-- **Headline Theorem (Horizontal FORS Signing = FIPS 205 Algorithm 16)**:
    `fors_batch::sign` (horizontal 8-way path with cross-tree `0..=2` batching and
    `fors_subtree_horiz` for heights `3..a`) produces the exact byte string of
    `Spec.forsSign`. -/
theorem fors_sign_horiz_eq (p : Params) (md sk pk : Bytes) (adrs : Adrs) :
    forsSignHoriz p md sk pk adrs = forsSign p md sk pk adrs := by
  unfold forsSignHoriz forsSign
  dsimp only
  set selections := base2b md p.a p.k
  rw [batchChunks_eq]
  apply List.flatMap_congr
  intro tree htree
  have ht : tree < p.k := List.mem_range.mp htree
  have hsec : ((List.range p.k).map fun t => forsSkGen p sk pk adrs (t * 2 ^ p.a + selections[t]!))[tree]! =
      forsSkGen p sk pk adrs (tree * 2 ^ p.a + selections[tree]!) := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  rw [hsec]
  congr 1
  apply List.flatMap_congr
  intro j hj
  have hja : j < p.a := List.mem_range.mp hj
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceIte, Nat.pow_zero, Nat.div_one, Nat.sub_zero]
    exact crossTreeHeight0_get p sk pk adrs selections hja tree ht
  · by_cases hj1 : j = 1
    · subst hj1
      simp only [hj0, ↓reduceIte, Nat.pow_one]
      exact crossTreeHeight1_get p sk pk adrs selections hja tree ht
    · by_cases hj2 : j = 2
      · subst hj2
        simp only [hj0, hj1, ↓reduceIte, show (2 : Nat) ^ 2 = 4 by decide]
        exact crossTreeHeight2_get p sk pk adrs selections hja tree ht
      · simp only [hj0, hj1, hj2, ↓reduceIte]
        rw [fors_subtree_horiz_eq p sk pk adrs _ j (by omega),
          fors_sibling_index tree p.a selections[tree]! j hja]

/-- Width-generic recursive `nodes_fallback` (`WIDTH != 8`, lines 204–227). -/
def nodesFallback (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (indices : Nat → Nat) (active : Nat) : Nat → Nat → Bytes
  | 0, lane => if lane < active then forsNode p sk (indices lane) 0 pk adrs else []
  | level + 1, lane =>
    if lane < active then
      let l := nodesFallback p sk pk adrs (fun i => indices i * 2) active level lane
      let r := nodesFallback p sk pk adrs (fun i => indices i * 2 + 1) active level lane
      H p pk { adrs with word2 := level + 1, word3 := indices lane } (l ++ r)
    else []

theorem nodesFallback_eq (p : Params) (sk pk : Bytes) (adrs : Adrs)
    (indices : Nat → Nat) (active level lane : Nat) (hl : lane < active) :
    nodesFallback p sk pk adrs indices active level lane =
      forsNode p sk (indices lane) level pk adrs := by
  induction level generalizing indices with
  | zero => simp [nodesFallback, hl]
  | succ lvl ih =>
    simp only [nodesFallback, hl, ↓reduceIte]
    rw [ih (fun i => indices i * 2), ih (fun i => indices i * 2 + 1)]
    simp only [Nat.mul_comm _ 2]
    rfl

/-- Model of `fors_batch::sign` on the `WIDTH != 8` fallback path (lines 258–275). -/
def forsSignFallback (width : Nat) (hw : 0 < width) (p : Params) (md sk pk : Bytes)
    (adrs : Adrs) : Bytes :=
  let selections := base2b md p.a p.k
  let treeSig (tree : Nat) : Bytes :=
    let leaf := tree * 2 ^ p.a + selections[tree]!
    forsSkGen p sk pk adrs leaf ++
      (List.range p.a).flatMap fun j =>
        nodesFallback p sk pk adrs (fun _ => (leaf / 2 ^ j) ^^^ 1) 1 j 0
  (batchChunks width p.k hw treeSig).flatten

theorem fors_sign_fallback_eq (width : Nat) (hw : 0 < width) (p : Params) (md sk pk : Bytes)
    (adrs : Adrs) :
    forsSignFallback width hw p md sk pk adrs = forsSign p md sk pk adrs := by
  unfold forsSignFallback forsSign
  dsimp only
  rw [batchChunks_eq, ← List.flatMap_def]
  apply List.flatMap_congr
  intro tree htree
  congr 1
  apply List.flatMap_congr
  intro j hj
  rw [nodesFallback_eq p sk pk adrs _ 1 j 0 (by decide),
    fors_sibling_index tree p.a (base2b md p.a p.k)[tree]! j (List.mem_range.mp hj)]

/-! ## Part 3: Active-Lane FORS Recovery (`fors_batch::recover`, Algorithm 17) -/

/-- One tree's in-place active-lane climb loop (`fors_batch::recover`, lines 399–458):
    starts from secret leaf at `tree * (a + 1)` and climbs `lvl ∈ 0..a` using
    single running index `idx := idx / 2` and parity test `idx % 2 == 0`. -/
def recoverTree (p : Params) (sig pk : Bytes) (adrs : Adrs) (tree sel : Nat) : Bytes :=
  let stride := p.a + 1
  let leaf := tree * 2 ^ p.a + sel
  let initNode := F p pk { adrs with word2 := 0, word3 := leaf } (block p sig (tree * stride))
  ((List.range p.a).foldl (fun (st : Bytes × Nat) lvl =>
    let (cur, idx) := st
    let parent := idx / 2
    let sib := block p sig (tree * stride + lvl + 1)
    let next :=
      if idx % 2 = 0 then
        H p pk { adrs with word2 := lvl + 1, word3 := parent } (cur ++ sib)
      else
        H p pk { adrs with word2 := lvl + 1, word3 := parent } (sib ++ cur)
    (next, parent))
    (initNode, leaf)).1

/-- Complete model of `fors_batch::recover` across batches of `width` active lanes
    followed by `FORS_ROOTS` sponge compression. -/
def forsRecoverBatch (width : Nat) (hw : 0 < width) (p : Params) (sig md pk : Bytes)
    (adrs : Adrs) : Bytes :=
  let selections := base2b md p.a p.k
  let roots := (batchChunks width p.k hw (fun tree =>
    recoverTree p sig pk adrs tree selections[tree]!)).flatten
  T p pk { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair } roots

private theorem block_auth_slice (p : Params) (sig : Bytes) (tree lvl : Nat) (hl : lvl < p.a) :
    block p ((sig.drop ((tree * (p.a + 1) + 1) * p.n)).take (p.a * p.n)) lvl =
      block p sig (tree * (p.a + 1) + lvl + 1) := by
  unfold block
  rw [List.drop_take, List.drop_drop, List.take_take]
  have hmin : min p.n (p.a * p.n - lvl * p.n) = p.n := by
    apply Nat.min_eq_left
    have hmul : (p.a - lvl) * p.n = p.a * p.n - lvl * p.n := Nat.sub_mul p.a lvl p.n
    rw [← hmul]
    exact Nat.le_mul_of_pos_left p.n (by omega)
  rw [hmin]
  congr 2
  ring

private theorem recover_climb_eq (p : Params) (sig pk : Bytes) (adrs : Adrs)
    (tree sel : Nat) (node : Bytes) :
    ∀ k ≤ p.a,
      (List.range k).foldl (fun (st : Bytes × Nat) lvl =>
        let (cur, idx) := st
        let parent := idx / 2
        let sib := block p sig (tree * (p.a + 1) + lvl + 1)
        let next :=
          if idx % 2 = 0 then
            H p pk { adrs with word2 := lvl + 1, word3 := parent } (cur ++ sib)
          else
            H p pk { adrs with word2 := lvl + 1, word3 := parent } (sib ++ cur)
        (next, parent))
        (node, tree * 2 ^ p.a + sel) =
      (List.range k).foldl (fun (st : Bytes × Nat) lvl =>
        let (cur, ti) := st
        let auth := (sig.drop ((tree * (p.a + 1) + 1) * p.n)).take (p.a * p.n)
        if (sel / 2 ^ lvl) % 2 = 0 then
          let ti := ti / 2
          (H p pk { adrs with word2 := lvl + 1, word3 := ti } (cur ++ block p auth lvl), ti)
        else
          let ti := (ti - 1) / 2
          (H p pk { adrs with word2 := lvl + 1, word3 := ti } (block p auth lvl ++ cur), ti))
        (node, tree * 2 ^ p.a + sel) ∧
      ((List.range k).foldl (fun (st : Bytes × Nat) lvl =>
        let (cur, idx) := st
        let parent := idx / 2
        let sib := block p sig (tree * (p.a + 1) + lvl + 1)
        let next :=
          if idx % 2 = 0 then
            H p pk { adrs with word2 := lvl + 1, word3 := parent } (cur ++ sib)
          else
            H p pk { adrs with word2 := lvl + 1, word3 := parent } (sib ++ cur)
        (next, parent))
        (node, tree * 2 ^ p.a + sel)).2 = (tree * 2 ^ p.a + sel) / 2 ^ k
  | 0, _ => by simp
  | k + 1, hk => by
    obtain ⟨ih_eq, ih_idx⟩ := recover_climb_eq p sig pk adrs tree sel node k (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set lhs := (List.range k).foldl _ (node, tree * 2 ^ p.a + sel)
    rw [← ih_eq]
    have hidx : lhs.2 = (tree * 2 ^ p.a + sel) / 2 ^ k := ih_idx
    have hpar : lhs.2 % 2 = (sel / 2 ^ k) % 2 := by
      rw [hidx]; exact fors_climb_parity tree p.a sel k (by omega)
    have hblk := block_auth_slice p sig tree k (by omega)
    constructor
    · rw [hpar, hblk]
      by_cases hp : (sel / 2 ^ k) % 2 = 0
      · simp [hp]
      · have hodd : lhs.2 % 2 = 1 := by omega
        have hdiv : (lhs.2 - 1) / 2 = lhs.2 / 2 := by omega
        simp [hp, hdiv]
    · rw [hidx, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- **Headline Theorem (Active-Lane FORS Recovery = FIPS 205 Algorithm 17)**:
    For every batch width `width >= 1` (including Apple/x86 `WIDTH = 8` and Linux AArch64
    `WIDTH = 3`), `fors_batch::recover` computes the exact FIPS 205 Algorithm 17 public key
    `Spec.forsPkFromSig`. -/
theorem fors_recover_batch_eq (width : Nat) (hw : 0 < width)
    (p : Params) (sig md pk : Bytes) (adrs : Adrs) :
    forsRecoverBatch width hw p sig md pk adrs = forsPkFromSig p sig md pk adrs := by
  unfold forsRecoverBatch forsPkFromSig
  dsimp only
  rw [batchChunks_eq, ← List.flatMap_def]
  congr 1
  apply List.flatMap_congr
  intro tree _
  unfold recoverTree climb
  exact congrArg Prod.fst
    (recover_climb_eq p sig pk adrs tree (base2b md p.a p.k)[tree]! _ p.a (Nat.le_refl _)).1

end Shakeopt.ForsHoriz
