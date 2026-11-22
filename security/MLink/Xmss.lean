import MLink.Wots
import MLink.Climb

/-!
# XMSS root recovery (FIPS 205 Algorithm 11): `Spec` = VCVio, all six SHA-2 parameter sets
-/

namespace MLink

open SLHDSA

variable (S : Sha2Set)

/-- `h' ∈ {9, 3, 8, 4}`. -/
theorem Sha2Set.hp_le (S : Sha2Set) : S.vp.params.hp ≤ 9 := by cases S <;> decide

theorem xmssNode_dom (a : SLHDSA.Adrs) (ha : BaseDom a) (z t : ℕ) (hz : z < 2 ^ 32)
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
theorem specXmss_split (W A : List S.Node) (hW : W.length = S.vp.params.len)
    (hA : A.length = S.vp.params.hp)
    (idx : ℕ) (msg pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.xmssPkFromSig S.spec idx (nds W ++ nds A) msg pk adrs =
      Spec.climb S.spec
        (Spec.wotsPkFromSig S.spec (nds W) msg pk
          { adrs.setTypeAndClear Spec.WOTS_HASH with keypair := idx })
        idx idx (nds A) S.spec.hp pk (adrs.setTypeAndClear Spec.TREE) := by
  have hWl : (nds W).length = S.spec.len * S.spec.n := by
    rw [nds_length, hW, S.len_eq, S.n_eq, Nat.mul_comm]
  have hAl : (nds A).length = S.spec.hp * S.spec.n := by
    rw [nds_length, hA, S.hp_eq, S.n_eq, Nat.mul_comm]
  have hw : (nds W ++ nds A).take (S.spec.len * S.spec.n) = nds W := List.take_left' hWl
  have hau : ((nds W ++ nds A).drop (S.spec.len * S.spec.n)).take (S.spec.hp * S.spec.n) =
      nds A := by
    rw [List.drop_left' hWl]
    exact List.take_of_length_le (Nat.le_of_eq hAl)
  unfold Spec.xmssPkFromSig
  simp only [hw, hau]

/-- Algorithm 11, `xmss_pkFromSig`, at a base address `(layer, tree)` in the SHA-2 domain. -/
theorem xmssPkFromSig_eq (idx : ℕ) (hidx : idx < 2 ^ S.vp.params.hp)
    (sig : XmssSig S.vp.params S.prims) (msg pk : S.Node) (a : SLHDSA.Adrs) (ha : BaseDom a) :
    nd (SLHDSA.xmssPkFromSig S.prims idx sig msg pk a) =
      Spec.xmssPkFromSig S.spec idx (xmssBytes S sig) (nd msg) (nd pk) (adr a) := by
  have e := xmssPkFromSig_eq_climb S.prims idx sig msg pk a
  refine (congrArg nd e).trans ?_
  have hwl : sig.wots.toList.length = S.vp.params.len := Vector.length_toList
  have hal : sig.auth.toList.length = S.vp.params.hp := Vector.length_toList
  have hidx32 : idx < 2 ^ 32 :=
    lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (le_trans S.hp_le (by norm_num)))
  have hwd : WotsDom (wotsLeafAdrs a idx) := by
    obtain ⟨hl, htr⟩ := ha
    exact ⟨rfl, hl, htr, hidx32⟩
  have hleaf := wotsPkFromSig_eq S sig.wots msg pk (wotsLeafAdrs a idx) hwd
  have hc := climb_eq S (xmssNodeHash S.prims pk a) pk ((adr a).setTypeAndClear Spec.TREE) idx idx
    (SLHDSA.wotsPkFromSig S.prims sig.wots msg pk (wotsLeafAdrs a idx)) sig.auth.toList
    (by
      intro z hz1 hz2 l r
      have hz : z ≤ 9 := le_trans (hal ▸ hz2) S.hp_le
      have ht : idx / 2 ^ z < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx32
      exact H_eq S pk (xmssNodeAdrs a z (idx / 2 ^ z))
        (xmssNode_dom a ha z _ (by omega) ht) l r)
    (fun _ _ => rfl)
  refine hc.trans ?_
  refine Eq.trans ?_
    (specXmss_split S sig.wots.toList sig.auth.toList hwl hal idx (nd msg) (nd pk) (adr a)).symm
  exact congrArg₂
    (fun n k => Spec.climb S.spec n idx idx (nds sig.auth.toList) k (nd pk)
      ((adr a).setTypeAndClear Spec.TREE)) hleaf (hal.trans S.hp_eq)

end MLink

#print axioms MLink.xmssPkFromSig_eq
