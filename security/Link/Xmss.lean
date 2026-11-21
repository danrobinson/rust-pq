import Link.Wots
import Link.Climb

/-!
# XMSS root recovery (FIPS 205 Algorithm 11): `Spec` = VCVio
-/

namespace Link

open SLHDSA

private theorem nds_length (ys : List Node) : (nds ys).length = ys.length * 16 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have : nds (y :: ys) = nd y ++ nds ys := rfl
    rw [this, List.length_append, nd_length, ih, List.length_cons]
    omega

private theorem xmssNode_dom (a : SLHDSA.Adrs) (ha : BaseDom a) (z t : ℕ) (hz : z < 2 ^ 32)
    (ht : t < 2 ^ 32) : Dom (xmssNodeAdrs a z t) := by
  obtain ⟨hl, htr⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [xmssNodeAdrs, Adrs.setTypeAndClear, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega)
  · simp only [xmssNodeAdrs, Adrs.setTypeAndClear, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [xmssNodeAdrs, Adrs.setTypeAndClear, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.Fits]
    apply decide_eq_true; omega

/-- Algorithm 11 on a signature that is literally `sig_WOTS ‖ AUTH`. -/
private theorem specXmss_split (W A : List Node) (hW : W.length = 35) (hA : A.length = 9)
    (idx : ℕ) (msg pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.xmssPkFromSig idx (nds W ++ nds A) msg pk adrs =
      Spec.climb
        (Spec.wotsPkFromSig (nds W) msg pk
          { adrs.setTypeAndClear Spec.WOTS_HASH with keypair := idx })
        idx idx (nds A) 9 pk (adrs.setTypeAndClear Spec.TREE) := by
  have hw : (nds W ++ nds A).take (Spec.len * Spec.n) = nds W := by
    rw [List.take_append_of_le_length (by rw [nds_length, hW]; decide)]
    exact List.take_of_length_le (by rw [nds_length, hW]; decide)
  have hau : ((nds W ++ nds A).drop (Spec.len * Spec.n)).take (Spec.hp * Spec.n) = nds A := by
    rw [List.drop_append_of_le_length (by rw [nds_length, hW]; decide),
      List.drop_of_length_le (by rw [nds_length, hW]; decide), List.nil_append]
    exact List.take_of_length_le (by rw [nds_length, hA]; decide)
  unfold Spec.xmssPkFromSig
  simp only [hw, hau]
  rfl

/-- Algorithm 11, `xmss_pkFromSig`, at a base address `(layer, tree)` in the SHA-2 domain. -/
theorem xmssPkFromSig_eq (idx : ℕ) (hidx : idx < 2 ^ 9) (sig : XmssSig vp.params prims)
    (msg pk : Node) (a : SLHDSA.Adrs) (ha : BaseDom a) :
    nd (SLHDSA.xmssPkFromSig prims idx sig msg pk a) =
      Spec.xmssPkFromSig idx (xmssBytes sig) (nd msg) (nd pk) (adr a) := by
  have e := xmssPkFromSig_eq_climb prims idx sig msg pk a
  refine (congrArg nd e).trans ?_
  have hwl : sig.wots.toList.length = 35 := Vector.length_toList
  have hal : sig.auth.toList.length = 9 := Vector.length_toList
  have hwd : WotsDom (wotsLeafAdrs a idx) := by
    obtain ⟨hl, htr⟩ := ha
    refine ⟨rfl, hl, htr, ?_⟩
    show idx < 2 ^ 32
    omega
  have hleaf := wotsPkFromSig_eq sig.wots msg pk (wotsLeafAdrs a idx) hwd
  have hc := climb_eq (xmssNodeHash prims pk a) pk ((adr a).setTypeAndClear Spec.TREE) idx idx
    (SLHDSA.wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs a idx)) sig.auth.toList
    (by
      intro z hz1 hz2 l r
      have hz : z ≤ 9 := hal ▸ hz2
      have ht : idx / 2 ^ z < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      exact H_eq pk (xmssNodeAdrs a z (idx / 2 ^ z))
        (xmssNode_dom a ha z _ (by omega) ht) l r)
    (fun _ _ => rfl)
  refine hc.trans ?_
  refine Eq.trans ?_
    (specXmss_split sig.wots.toList sig.auth.toList hwl hal idx (nd msg) (nd pk) (adr a)).symm
  exact congrArg₂
    (fun n k => Spec.climb n idx idx (nds sig.auth.toList) k (nd pk)
      ((adr a).setTypeAndClear Spec.TREE)) hleaf hal

end Link

#print axioms Link.xmssPkFromSig_eq
