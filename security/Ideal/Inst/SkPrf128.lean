import Ideal.Games.Prf
import Ideal.Sha.Shape
import Reduction.PrfDomainNonVacuity

/-!
# PRF security on the secret-key address domain at SLH-DSA-SHA2-128s, ideal-compression model

On the secret-key address domain `Reduction.SkAdrs Link.vp` the SHA-2 `PRF` of the 128s bundle
over a compression table `g` is

`PRF_g(k, (pk, a)) = out16 (g (g (IV128, sb128 pk), blk128 a k))`,
`blk128 a k = ADRSc(a) ‖ k ‖ 0x80 ‖ 0^17 ‖ len` (the single block after the seed block),

so `Reduction.skPrfC Link.vp (primsG (liftC g))` is the generic scheme `prfSchemeI` of
`Ideal/Games/PrfDefs.lean` (`skPrfC_eq`), and `Ideal.prfAdvantageI_le` gives
`skPrf_bound_128s : skPrfAdvantageI A ≤ q / 2^128 + (q + qO)² / 2^256`.
-/

open OracleComp OracleSpec ENNReal PRFScheme SLHDSA SLHDSA.Concrete

namespace Ideal

/-- Secret-key addresses of SLH-DSA-SHA2-128s. -/
abbrev SkAd : Type := Reduction.SkAdrs Link.vp

/-- The key block: the single 64-byte block after the seed block of
`pad(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed)`. -/
def blk128 (a : SkAd) (k : Bytes 16) : Blk := (tblocks (sha2AdrsKey a.val) [k]).1

/-! ## The hypotheses of the generic theorem -/

theorem sha2AdrsKey_injective_skAd {a a' : SkAd} (h : sha2AdrsKey a.val = sha2AdrsKey a'.val) :
    a = a' := by
  have ha := Reduction.skAdrs_dom_128s a
  have ha' := Reduction.skAdrs_dom_128s a'
  exact Subtype.ext
    (sha2AdrsKey_injective_of_domain ha.1 ha.2.1 ha.2.2 ha'.1 ha'.2.1 ha'.2.2 h)

instance : Finite SkAd :=
  Finite.of_injective (fun a : SkAd => sha2AdrsKey a.val) fun _ _ h =>
    sha2AdrsKey_injective_skAd h

/-- The key block determines the address and the key. -/
theorem blk128_injective (a a' : SkAd) (k k' : Bytes 16) (h : blk128 a k = blk128 a' k') :
    a = a' ∧ k = k' := by
  have h2 : tblocks (sha2AdrsKey a.val) [k] = tblocks (sha2AdrsKey a'.val) [k'] :=
    Prod.ext h (by
      rw [tblocks_snd_of_length_one _ _ rfl, tblocks_snd_of_length_one _ _ rfl])
  obtain ⟨h3, h4⟩ := tblocks_injective h2
  exact ⟨sha2AdrsKey_injective_skAd h3, (List.cons.inj h4).1⟩

/-- The first block of `tblocks`, bytewise. -/
theorem tblocks_fst_eq (a : Bytes 22) (xs : List (Bytes 16)) :
    (tblocks a xs).1 = Vector.ofFn fun j : Fin 64 => (tbytes a xs).getD j.val 0 := by
  have h := blocksOf_tbytes a xs
  have hl := tbytes_length a xs
  unfold blocksOf at h
  rw [hl, show 64 * ((30 + 16 * xs.length) / 64 + 1) / 64 = (30 + 16 * xs.length) / 64 + 1 by omega,
    List.range_succ_eq_map] at h
  simp only [List.map_cons] at h
  have h1 := (List.cons.inj h).1.symm
  simpa using h1

/-- Byte 38 of the key block is the padding byte `0x80`. -/
theorem tblocks_one_get38 (a : Bytes 22) (k : Bytes 16) : (tblocks a [k]).1[38] = 0x80 := by
  rw [tblocks_fst_eq]
  simp only [Vector.getElem_ofFn, tbytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [tailL]
  rfl

/-- Byte 38 of a seed block is zero. -/
theorem sb128_get38 (pk : Bytes 16) : (sb128 pk)[38] = 0 := by
  have h : (sb128 pk).toList[38]? = some 0 := by
    rw [sb128_toList, List.getElem?_append_right (by simp)]
    simp
  have h2 : (sb128 pk).toList[38]? = some (sb128 pk)[38] := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp
  exact Option.some.inj (h2.symm.trans h)

/-- A seed block is never a key block. -/
theorem sb128_ne_blk128 (pk : Bytes 16) (a : SkAd) (k : Bytes 16) : sb128 pk ≠ blk128 a k := by
  intro h
  have h1 := congrArg (fun v : Blk => v[38]) h
  simp only [blk128, sb128_get38, tblocks_one_get38] at h1
  exact absurd h1 (by decide)

/-! ## The Reduction's scheme is the generic scheme -/

theorem ofAdrs_skAd (a : SkAd) : ∃ chk, Sha2Address.ofAdrs a.val = .ok chk := by
  have h := Reduction.skAdrs_dom_128s a
  exact ⟨⟨a.val, h.1, h.2.1, h.2.2⟩, by
    simp only [Sha2Address.ofAdrs, h.1, h.2.1, h.2.2, dite_true]⟩

/-- On the secret-key address domain the 128s `PRF` over `g` is two compression calls. -/
theorem PRF_128s_eq (g : CF St Blk) (pk k : Bytes 16) (a : SkAd) :
    (primsG (liftC g)).PRF pk k a.val = prfF IV128 sb128 blk128 out16 g k (pk, a) := by
  obtain ⟨chk, hchk⟩ := ofAdrs_skAd a
  rw [PRF_eq_Thash (liftC g) Link.vp.params pk k a.val hchk]
  refine (primsG_Thash_shape g pk (sha2AdrsKey a.val) [k]).trans ?_
  unfold keyedChain prfF blk128
  rw [tblocks_snd_of_length_one _ _ rfl]
  rfl

/-- **`Reduction.skPrfC` at the 128s bundle over `g` is the generic scheme `⟨$ᵗ K, f g⟩`.** -/
theorem skPrfC_eq (g : CF St Blk) :
    Reduction.skPrfC Link.vp (primsG (liftC g)) = prfSchemeI IV128 sb128 blk128 out16 g := by
  unfold Reduction.skPrfC prfSchemeI
  congr 1
  funext k d
  exact PRF_128s_eq g d.1 k d.2

/-! ## The advantage and the bound -/

/-- The PRF advantage of an ideal-model distinguisher against the Reduction's scheme
`Reduction.skPrfC Link.vp` at the 128s bundle over a uniformly random compression table. -/
noncomputable def skPrfAdvantageI (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) : ℝ≥0∞ :=
  (𝒟[do
      let g ← $ᵗ (CF St Blk)
      (Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g)]).boolDist
    (𝒟[do
      let g ← $ᵗ (CF St Blk)
      prfIdealExperiment (A.inst g)])

theorem skPrfAdvantageI_eq (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) :
    skPrfAdvantageI A = prfAdvantageI IV128 sb128 blk128 out16 A := by
  unfold skPrfAdvantageI prfAdvantageI prfRealIdeal prfIdealIdeal prfRealGameI prfIdealGameI
  simp only [skPrfC_eq]
  rfl

/-- **PRF security on the secret-key address domain at SLH-DSA-SHA2-128s in the
ideal-compression model.**  A distinguisher making at most `q` compression queries and `qO`
PRF-oracle queries has advantage at most `q / 2^128 + (q + qO)² / 2^256`. -/
theorem skPrf_bound_128s (A : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16)) (q qO : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO) :
    skPrfAdvantageI A ≤
      (q : ℝ≥0∞) / 2 ^ 128 + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let : Fintype SkAd := Fintype.ofFinite SkAd
  rw [skPrfAdvantageI_eq]
  refine (prfAdvantageI_le IV128 sb128 blk128 out16 blk128_injective sb128_ne_blk128
    sb128_injective prEvent_out16 A q qO hq hO).trans (le_of_eq ?_)
  rw [card_bytes 16, card_St, div_eq_mul_inv, div_eq_mul_inv]
  norm_num

end Ideal

#print axioms Ideal.skPrfC_eq
#print axioms Ideal.skPrf_bound_128s
