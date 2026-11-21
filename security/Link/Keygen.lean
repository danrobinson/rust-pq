import Link.Verify

/-!
# Key generation (FIPS 205 Algorithm 18): `Spec` = VCVio
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
def skBytes (k : SecretKeyCore prims.core) : Spec.Bytes :=
  nd k.skSeed ++ nd k.skPrf ++ nd k.pkSeed ++ nd k.pkRoot

private theorem wotsSk_dom (a : SLHDSA.Adrs) (ha : WotsDom a) (i : ℕ) (hi : i < 35) :
    Dom (wotsSkAdrs a i) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega)
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.Fits]
    apply decide_eq_true; omega

private theorem wotsChain_dom' (a : SLHDSA.Adrs) (ha : WotsDom a) (i j : ℕ) (hi : i < 35)
    (hj : j < 16) : Dom ((wotsChainAdrs a i).setHashAddress j) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.getKeyPairAddress,
      Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega) | simp
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.setChainAddress, Adrs.setHashAddress, Adrs.Fits]
    apply decide_eq_true; omega

private theorem wotsPk_dom' (a : SLHDSA.Adrs) (ha : WotsDom a) : Dom (wotsPkAdrs a) := by
  obtain ⟨ht, hl, htr, hw⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
      Adrs.getKeyPairAddress, Adrs.isCanonical, Adrs.Fits, AddrType.toCode, AddrType.ofCode]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      first | rfl | (apply decide_eq_true; omega)
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.Fits]
    apply decide_eq_true; omega
  · simp only [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.Fits]
    apply decide_eq_true; omega

private theorem xmssNode_dom' (a : SLHDSA.Adrs) (ha : BaseDom a) (z t : ℕ) (hz : z < 2 ^ 32)
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

private theorem nds_ofFn' (f : Fin 35 → Node) :
    nds (Vector.ofFn f).toList =
      (List.range 35).flatMap fun i => if h : i < 35 then nd (f ⟨i, h⟩) else [] := by
  simp only [nds, Vector.toList_ofFn, List.ofFn_eq_map, List.flatMap_map]
  rw [← List.map_coe_finRange_eq_range (n := 35), List.flatMap_map]
  congr 1
  funext i
  simp

private theorem specChain_word3' (x : Spec.Bytes) (i s : ℕ) (pk : Spec.Bytes) (a : Spec.Adrs)
    (v : ℕ) : Spec.chain x i s pk { a with word3 := v } = Spec.chain x i s pk a := rfl

/-- Algorithm 6, `wots_pkGen`. -/
theorem wotsPkGen_eq (sk pk : Node) (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nd (SLHDSA.wotsPkGen prims sk pk a) = Spec.wotsPkGen (nd sk) (nd pk) (adr a) := by
  have e : SLHDSA.wotsPkGen prims sk pk a =
      prims.Tl pk (wotsPkAdrs a) (Vector.ofFn fun i : Fin 35 =>
        SLHDSA.chain prims pk (wotsChainAdrs a i.val)
          (prims.PRF pk sk (wotsSkAdrs a i.val)) 0 (16 - 1)).toList := by
    have e1 := wotsPkGen_eq_tl prims sk pk a
    have e2 := wotsPkGenTops_eq_ofFn prims sk pk a
    exact e1.trans (congrArg (fun v => prims.Tl pk (wotsPkAdrs a) v.toList) e2)
  refine (congrArg nd e).trans ?_
  refine (Tl_eq pk _ (wotsPk_dom' a ha) _).trans ?_
  have key : nds (Vector.ofFn fun i : Fin 35 =>
        SLHDSA.chain prims pk (wotsChainAdrs a i.val)
          (prims.PRF pk sk (wotsSkAdrs a i.val)) 0 (16 - 1)).toList =
      (List.range Spec.len).flatMap fun i =>
        Spec.chain (Spec.PRF (nd pk) (nd sk) { Spec.wotsSkAdrs (adr a) with word2 := i })
          0 (Spec.w - 1) (nd pk) { adr a with word2 := i } := by
    refine (nds_ofFn' _).trans ?_
    apply List.flatMap_congr
    intro i hi
    have hi' : i < 35 := List.mem_range.mp hi
    rw [dif_pos hi']
    have hc := chain_eq pk (wotsChainAdrs a i) (prims.PRF pk sk (wotsSkAdrs a i)) 0 (16 - 1)
      (fun j _ hj => wotsChain_dom' a ha i j hi' (by omega))
    refine hc.trans ?_
    have hp := PRF_eq pk sk (wotsSkAdrs a i) (wotsSk_dom a ha i hi')
    have hadr1 : adr (wotsSkAdrs a i) = { Spec.wotsSkAdrs (adr a) with word2 := i } := by
      simp [adr, wotsSkAdrs, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear, Adrs.setTypeAndClear,
        Adrs.setKeyPairAddress, Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode,
        Spec.WOTS_PRF]
    have hadr2 : adr (wotsChainAdrs a i) =
        { ({ adr a with word2 := i } : Spec.Adrs) with word3 := 0 } := by
      simp [adr, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
        Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode, ha.1]
    rw [hadr1] at hp
    rw [hadr2, specChain_word3']
    exact congrArg (fun x => Spec.chain x 0 (16 - 1) (nd pk) { adr a with word2 := i }) hp
  exact congrArg (Spec.T (nd pk) (Spec.wotsPkAdrs (adr a))) key

/-- Algorithm 9, `xmss_node`, for a node inside a height-9 tree. -/
theorem xmssNode_eq (sk pk : Node) (a : SLHDSA.Adrs) (ha : BaseDom a) (z t : ℕ) (hz : z ≤ 9)
    (ht : t < 2 ^ (9 - z)) :
    nd (SLHDSA.xmssNode prims sk pk a z t) = Spec.xmssNode (nd sk) t z (nd pk) (adr a) := by
  induction z generalizing t with
  | zero =>
    have e : SLHDSA.xmssNode prims sk pk a 0 t =
        SLHDSA.wotsPkGen prims sk pk (wotsLeafAdrs a t) :=
      (xmssNode_zero prims sk pk a t).trans (xmssLeaf_eq_wotsPkGen prims sk pk a t)
    refine (congrArg nd e).trans ?_
    have hwd : WotsDom (wotsLeafAdrs a t) := by
      obtain ⟨hl, htr⟩ := ha
      refine ⟨rfl, hl, htr, ?_⟩
      show t < 2 ^ 32
      have : t < 2 ^ 9 := ht
      omega
    exact wotsPkGen_eq sk pk (wotsLeafAdrs a t) hwd
  | succ z ih =>
    have e := xmssNode_succ prims sk pk a z t
    refine (congrArg nd e).trans ?_
    have h2 : (2:ℕ) ^ (9 - z) = 2 * 2 ^ (9 - (z + 1)) := by
      rw [show 9 - z = (9 - (z + 1)) + 1 by omega, pow_succ]; omega
    have hl := ih (2 * t) (by omega) (by omega)
    have hr := ih (2 * t + 1) (by omega) (by omega)
    have htb : t < 2 ^ 32 :=
      lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) (by omega))
    have hH := H_eq pk (xmssNodeAdrs a (z + 1) t) (xmssNode_dom' a ha (z + 1) t (by omega) htb)
      (SLHDSA.xmssNode prims sk pk a z (2 * t)) (SLHDSA.xmssNode prims sk pk a z (2 * t + 1))
    refine hH.trans ?_
    rw [hl, hr]
    rfl

/-- FIPS 205 Algorithm 18, `slh_keygen_internal`. -/
theorem keygen_eq (skSeed skPrf pkSeed : Node) :
    Spec.slhKeygenInternal (nd skSeed) (nd skPrf) (nd pkSeed) =
      (skBytes (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2,
       pkBytes (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1) := by
  have hroot : nd (GeneralHypertree.root vp prims skSeed pkSeed) =
      Spec.xmssNode (nd skSeed) 0 Spec.hp (nd pkSeed) { Spec.Adrs.zero with layer := Spec.d - 1 } := by
    have e : GeneralHypertree.root vp prims skSeed pkSeed =
        SLHDSA.xmssNode prims skSeed pkSeed (GeneralHypertree.layerAdrs 6 0) 9 0 :=
      (GeneralHypertree.root_eq_xmssRoot vp prims skSeed pkSeed).trans
        (xmssRoot_eq_node prims skSeed pkSeed _)
    refine (congrArg nd e).trans ?_
    exact xmssNode_eq skSeed pkSeed (GeneralHypertree.layerAdrs 6 0)
      ⟨by decide, by decide⟩ 9 0 (by omega) (by omega)
  have h1 := GeneralScheme.keygenInternal_fst vp prims skSeed skPrf pkSeed
  have h2 := GeneralScheme.keygenInternal_snd vp prims skSeed skPrf pkSeed
  rw [h1, h2]
  unfold Spec.slhKeygenInternal skBytes pkBytes
  simp only []
  rw [← hroot]

end Link

#print axioms Link.wotsPkGen_eq
#print axioms Link.xmssNode_eq
#print axioms Link.keygen_eq
