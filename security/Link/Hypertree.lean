import Link.Xmss

/-!
# Hypertree root recovery (FIPS 205 Algorithm 13): `Spec` = VCVio
-/

namespace Link

open SLHDSA

/-- One layer of the fold in `Spec.htVerify`. -/
def htStep (sig pkSeed : Spec.Bytes) (st : Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Nat × Nat :=
  let (node, tree, leaf) := st
  let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
  let s := (sig.drop (j * Spec.xmssSigBytes)).take Spec.xmssSigBytes
  (Spec.xmssPkFromSig leaf s node pkSeed adrs, tree >>> Spec.hp, tree % 2 ^ Spec.hp)

/-- The root recomputed by `Spec.htVerify` before its final comparison. -/
def specHtRoot (msg sig pkSeed : Spec.Bytes) (idxTree idxLeaf : Nat) : Spec.Bytes :=
  ((List.range Spec.d).foldl (htStep sig pkSeed) (msg, idxTree, idxLeaf)).1

theorem htVerify_eq (msg sig pkSeed : Spec.Bytes) (t l : Nat) (root : Spec.Bytes) :
    Spec.htVerify msg sig pkSeed t l root = (specHtRoot msg sig pkSeed t l == root) := rfl

/-- The same walk over a list of per-layer XMSS signature chunks. -/
def htGo (pk : Spec.Bytes) : Nat → Spec.Bytes → Nat → Nat → List Spec.Bytes → Spec.Bytes
  | _, node, _, _, [] => node
  | j, node, tree, leaf, s :: ss =>
    htGo pk (j + 1)
      (Spec.xmssPkFromSig leaf s node pk { Spec.Adrs.zero with layer := j, tree := tree })
      (tree >>> Spec.hp) (tree % 2 ^ Spec.hp) ss

theorem foldl_htStep (pk : Spec.Bytes) (chunks : List Spec.Bytes)
    (hall : ∀ c ∈ chunks, c.length = Spec.xmssSigBytes) :
    ∀ (j : Nat) (pre : Spec.Bytes) (_ : pre.length = j * Spec.xmssSigBytes)
      (rest : List Spec.Bytes) (node : Spec.Bytes) (tree leaf : Nat)
      (done : List Spec.Bytes) (_ : done.flatten = pre) (_ : chunks = done ++ rest),
      ((List.range' j rest.length).foldl (htStep chunks.flatten pk) (node, tree, leaf)).1 =
        htGo pk j node tree leaf rest := by
  intro j pre hpre rest node tree leaf done hdone hch
  induction rest generalizing j pre node tree leaf done with
  | nil => simp [htGo]
  | cons c cs ih =>
    have hc : c.length = Spec.xmssSigBytes := hall c (by simp [hch])
    simp only [List.length_cons, List.range'_succ, List.foldl_cons, htGo]
    have hslice : ((chunks.flatten).drop (j * Spec.xmssSigBytes)).take Spec.xmssSigBytes = c := by
      rw [hch, List.flatten_append, hdone, List.flatten_cons, ← hpre, List.drop_left',
        ← hc, List.take_left']
      all_goals rfl
    have := ih (j + 1) (pre ++ c) (by simp [hpre, hc]; ring)
      (Spec.xmssPkFromSig leaf c node pk { Spec.Adrs.zero with layer := j, tree := tree })
      (tree >>> Spec.hp) (tree % 2 ^ Spec.hp) (done ++ [c]) (by simp [hdone]) (by simp [hch])
    rw [← this]
    simp only [htStep, hslice]

theorem specHtRoot_eq_htGo (msg pk : Spec.Bytes) (t l : Nat) (chunks : List Spec.Bytes)
    (hlen : chunks.length = Spec.d) (hall : ∀ c ∈ chunks, c.length = Spec.xmssSigBytes) :
    specHtRoot msg chunks.flatten pk t l = htGo pk 0 msg t l chunks := by
  unfold specHtRoot
  rw [List.range_eq_range', ← hlen]
  exact foldl_htStep pk chunks hall 0 [] rfl chunks msg t l [] rfl rfl

theorem recover_eq (pk : Node) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : Node) (sigs : Vector (XmssSig vp.params prims.core) layers),
      nd (GeneralHypertree.recoverFromPosition vp prims pk pos layers h msg sigs) =
        htGo (nd pk) pos.layer.val (nd msg) pos.tree.val pos.leaf.val
          (sigs.toList.map xmssBytes) := by
  have hx : ∀ (pos : LayerPosition vp) (s : XmssSig vp.params prims.core) (msg : Node),
      nd (SLHDSA.xmssPkFromSig prims pos.leaf.val s msg pk pos.toAdrs) =
        Spec.xmssPkFromSig pos.leaf.val (xmssBytes s) (nd msg) (nd pk)
          { Spec.Adrs.zero with layer := pos.layer.val, tree := pos.tree.val } := by
    intro pos s msg
    have hl : pos.layer.val < 7 := pos.layer.isLt
    have ht : pos.tree.val < 2 ^ 64 := by
      have h1 := pos.tree.isLt
      have h2 : layerTreeHeight vp pos.layer.val ≤ 64 := by
        simp only [layerTreeHeight]
        show (7 - (pos.layer.val + 1)) * 9 ≤ 64
        omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)
    exact xmssPkFromSig_eq pos.leaf.val pos.leaf.isLt s msg pk pos.toAdrs
      ⟨by show pos.layer.val < 256; omega, ht⟩
  intro layers
  induction layers using Nat.strong_induction_on with
  | _ layers ih =>
    intro pos h msg sigs
    match layers, sigs, h with
    | 0, sigs, h =>
      have : sigs.toList = [] := by
        apply List.eq_nil_of_length_eq_zero; simp
      simp [GeneralHypertree.recoverFromPosition, this, htGo]
    | 1, sigs, h =>
      obtain ⟨s, rfl⟩ : ∃ s, sigs = #v[s] := ⟨sigs.head, by
        apply Vector.ext; intro i hi
        have : i = 0 := by omega
        subst this; simp [Vector.head]⟩
      simp only [GeneralHypertree.recoverFromPosition]
      rw [show (#v[s] : Vector _ 1).head = s from rfl, hx]
      simp [htGo]
    | layers + 2, sigs, h =>
      have hs : sigs.toList = sigs.head :: sigs.tail.toList := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          cases i with
          | zero => simp [Vector.head]
          | succ i => simp [Vector.tail, Nat.add_comm]
      simp only [GeneralHypertree.recoverFromPosition]
      refine (ih (layers + 1) (by omega) _ _ _ sigs.tail).trans ?_
      rw [hs, List.map_cons, htGo, hx]
      simp [LayerPosition.next, Nat.shiftRight_eq_div_pow, Spec.hp]
      rfl

end Link
