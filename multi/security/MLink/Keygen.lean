import MLink.Verify

/-!
# Key generation (FIPS 205 Algorithm 18): `Spec` = VCVio, all six SHA-2 parameter sets
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

variable (S : Sha2Set)

/-- `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
def skBytes (k : SecretKeyCore S.prims.core) : Spec.Bytes :=
  nd k.skSeed ++ nd k.skPrf ++ nd k.pkSeed ++ nd k.pkRoot

theorem skBytes_length (k : SecretKeyCore S.prims.core) : (skBytes S k).length = 4 * S.spec.n := by
  have h1 : (nd k.skSeed).length = S.vp.params.n := nd_length _
  have h2 : (nd k.skPrf).length = S.vp.params.n := nd_length _
  have h3 : (nd k.pkSeed).length = S.vp.params.n := nd_length _
  have h4 : (nd k.pkRoot).length = S.vp.params.n := nd_length _
  simp only [skBytes, List.length_append, h1, h2, h3, h4, S.n_eq]
  omega

/-- The WOTS+ secret-value addresses are in the SHA-2 domain. -/
theorem wotsSk_dom (a : SLHDSA.Adrs) (ha : WotsDom a) (i : ℕ) (hi : i < 2 ^ 32) :
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

theorem adr_wotsSk (a : SLHDSA.Adrs) (i : ℕ) :
    adr (wotsSkAdrs a i) = { Spec.wotsSkAdrs (adr a) with word2 := i } := by
  simp [adr, wotsSkAdrs, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear, Adrs.setTypeAndClear,
    Adrs.setKeyPairAddress, Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode,
    Spec.WOTS_PRF]

theorem adr_wotsChain (a : SLHDSA.Adrs) (h0 : a.type = 0) (i : ℕ) :
    adr (wotsChainAdrs a i) = { ({ adr a with word2 := i } : Spec.Adrs) with word3 := 0 } := by
  simp [adr, wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setChainAddress, Adrs.getKeyPairAddress, AddrType.toCode, h0]

/-- Algorithm 6, `wots_pkGen`. -/
theorem wotsPkGen_eq (sk pk : S.Node) (a : SLHDSA.Adrs) (ha : WotsDom a) :
    nd (SLHDSA.wotsPkGen S.prims sk pk a) = Spec.wotsPkGen S.spec (nd sk) (nd pk) (adr a) := by
  have e : SLHDSA.wotsPkGen S.prims sk pk a =
      S.prims.Tl pk (wotsPkAdrs a) (Vector.ofFn fun i : Fin S.vp.params.len =>
        SLHDSA.chain S.prims pk (wotsChainAdrs a i.val)
          (S.prims.PRF pk sk (wotsSkAdrs a i.val)) 0 (S.vp.params.w - 1)).toList := by
    have e1 := wotsPkGen_eq_tl S.prims sk pk a
    have e2 := wotsPkGenTops_eq_ofFn S.prims sk pk a
    exact e1.trans (congrArg (fun v => S.prims.Tl pk (wotsPkAdrs a) v.toList) e2)
  refine (congrArg nd e).trans ?_
  refine (Tl_eq S pk _ (wotsPk_dom a ha) _
    (fun h => S.len_ne_one (Vector.length_toList.symm.trans h))).trans ?_
  have key : nds (Vector.ofFn fun i : Fin S.vp.params.len =>
        SLHDSA.chain S.prims pk (wotsChainAdrs a i.val)
          (S.prims.PRF pk sk (wotsSkAdrs a i.val)) 0 (S.vp.params.w - 1)).toList =
      (List.range S.vp.params.len).flatMap fun i =>
        Spec.chain S.spec
          (Spec.PRF S.spec (nd pk) (nd sk) { Spec.wotsSkAdrs (adr a) with word2 := i })
          0 (S.spec.w - 1) (nd pk) { adr a with word2 := i } := by
    refine nds_ofFn _ _ fun i => ?_
    have hi' : i.val < S.vp.params.len := i.isLt
    have hi32 : i.val < 2 ^ 32 := lt_trans hi' S.len_lt
    have hw := S.w_sixteen
    have hc := chain_eq S pk (wotsChainAdrs a i.val) (S.prims.PRF pk sk (wotsSkAdrs a i.val)) 0
      (S.vp.params.w - 1) (fun j _ hj => wotsChain_dom a ha i.val j hi32 (by omega))
    refine hc.trans ?_
    have hp := PRF_eq S pk sk (wotsSkAdrs a i.val) (wotsSk_dom a ha i.val hi32)
    rw [adr_wotsSk] at hp
    rw [adr_wotsChain a ha.1, specChain_word3, hp, S.w_eq]
  refine (congrArg (Spec.T S.spec (nd pk) (Spec.wotsPkAdrs (adr a))) key).trans ?_
  unfold Spec.wotsPkGen
  rw [← S.len_eq]

/-- Algorithm 9, `xmss_node`, for a node inside a height-`h'` tree. -/
theorem xmssNode_eq (sk pk : S.Node) (a : SLHDSA.Adrs) (ha : BaseDom a) (z t : ℕ)
    (hz : z ≤ S.vp.params.hp) (ht : t < 2 ^ (S.vp.params.hp - z)) :
    nd (SLHDSA.xmssNode S.prims sk pk a z t) =
      Spec.xmssNode S.spec (nd sk) t z (nd pk) (adr a) := by
  have hhp := S.hp_le
  have hb : ∀ (z t : ℕ), t < 2 ^ (S.vp.params.hp - z) → t < 2 ^ 32 := fun z t ht =>
    lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega))
  induction z generalizing t with
  | zero =>
    have e : SLHDSA.xmssNode S.prims sk pk a 0 t =
        SLHDSA.wotsPkGen S.prims sk pk (wotsLeafAdrs a t) :=
      (xmssNode_zero S.prims sk pk a t).trans (xmssLeaf_eq_wotsPkGen S.prims sk pk a t)
    refine (congrArg nd e).trans ?_
    have hwd : WotsDom (wotsLeafAdrs a t) := by
      obtain ⟨hl, htr⟩ := ha
      exact ⟨rfl, hl, htr, hb 0 t ht⟩
    exact wotsPkGen_eq S sk pk (wotsLeafAdrs a t) hwd
  | succ z ih =>
    have e := xmssNode_succ S.prims sk pk a z t
    refine (congrArg nd e).trans ?_
    have h2 : (2:ℕ) ^ (S.vp.params.hp - z) = 2 * 2 ^ (S.vp.params.hp - (z + 1)) := by
      rw [show S.vp.params.hp - z = (S.vp.params.hp - (z + 1)) + 1 by omega, pow_succ]; omega
    have hl := ih (2 * t) (by omega) (by omega)
    have hr := ih (2 * t + 1) (by omega) (by omega)
    have htb : t < 2 ^ 32 := hb _ t ht
    have hH := H_eq S pk (xmssNodeAdrs a (z + 1) t) (xmssNode_dom a ha (z + 1) t (by omega) htb)
      (SLHDSA.xmssNode S.prims sk pk a z (2 * t)) (SLHDSA.xmssNode S.prims sk pk a z (2 * t + 1))
    refine hH.trans ?_
    rw [hl, hr]
    rfl

/-- The top-layer base address `(d − 1, 0)` is in the SHA-2 domain. -/
theorem topLayer_baseDom : BaseDom (GeneralHypertree.layerAdrs (S.vp.params.d - 1) 0) := by
  have := S.d_lt
  exact ⟨by show S.vp.params.d - 1 < 256; omega, by show (0 : ℕ) < 2 ^ 64; norm_num⟩

/-- The public root: `xmss_node(SK.seed, 0, h', PK.seed, ADRS[layer = d − 1])`. -/
theorem htRoot_eq (skSeed pkSeed : S.Node) :
    nd (GeneralHypertree.root S.vp S.prims skSeed pkSeed) =
      Spec.xmssNode S.spec (nd skSeed) 0 S.spec.hp (nd pkSeed)
        { Spec.Adrs.zero with layer := S.spec.d - 1 } := by
  have e : GeneralHypertree.root S.vp S.prims skSeed pkSeed =
      SLHDSA.xmssNode S.prims skSeed pkSeed (GeneralHypertree.layerAdrs (S.vp.params.d - 1) 0)
        S.vp.params.hp 0 :=
    (GeneralHypertree.root_eq_xmssRoot S.vp S.prims skSeed pkSeed).trans
      (xmssRoot_eq_node S.prims skSeed pkSeed _)
  refine (congrArg nd e).trans ?_
  refine (xmssNode_eq S skSeed pkSeed (GeneralHypertree.layerAdrs (S.vp.params.d - 1) 0)
    (topLayer_baseDom S) S.vp.params.hp 0 le_rfl (by positivity)).trans ?_
  rw [S.hp_eq]
  have : adr (GeneralHypertree.layerAdrs (S.vp.params.d - 1) 0) =
      { Spec.Adrs.zero with layer := S.spec.d - 1 } := by
    rw [← S.d_eq]; rfl
  rw [this]

/-- FIPS 205 Algorithm 18, `slh_keygen_internal`. -/
theorem keygen_eq (skSeed skPrf pkSeed : S.Node) :
    Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed) =
      (skBytes S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).2,
       pkBytes S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).1) := by
  have hroot := htRoot_eq S skSeed pkSeed
  have h1 := GeneralScheme.keygenInternal_fst S.vp S.prims skSeed skPrf pkSeed
  have h2 := GeneralScheme.keygenInternal_snd S.vp S.prims skSeed skPrf pkSeed
  rw [h1, h2]
  unfold Spec.slhKeygenInternal skBytes pkBytes
  simp only []
  rw [← hroot]

end MLink

#print axioms MLink.wotsPkGen_eq
#print axioms MLink.xmssNode_eq
#print axioms MLink.keygen_eq
