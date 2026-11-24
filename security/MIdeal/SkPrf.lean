import MIdeal.MixedTables
import Ideal.Inst.SkPrf128
import MReduction.Instances

namespace MIdeal.SkPrf

open MLink Ideal SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec PRFScheme ENNReal

variable (S : Sha2Set)

private theorem width : S.vp.params.n ≤ 32 := by cases S <;> decide

def seedBlock (pk : S.Node) : Blk :=
  ⟨(pk.toList ++ List.replicate (64 - S.vp.params.n) 0).toArray, by
    simp; have := width S; omega⟩

def singletonBlock (a : Bytes 22) (k : S.Node) : Blk :=
  ⟨(a.toList ++ k.toList ++ tailL (86 + S.vp.params.n)).toArray, by
    simp [tailL_length]; cases S <;> decide⟩

abbrev keyBlock (a : Reduction.SkAdrs S.vp) := singletonBlock S (sha2AdrsKey a.val)

def output (st : St) : S.Node :=
  Vector.ofFn fun i => st[i.val]'(Nat.lt_of_lt_of_le i.isLt (width S))

private theorem ad_inj : Function.Injective (fun a : Reduction.SkAdrs S.vp => sha2AdrsKey a.val) :=
  fun a b h => Subtype.ext ((MReduction.structural S).keyInj a.property.addressFacts b.property.addressFacts h)

private theorem keyBlock_inj (a b : Reduction.SkAdrs S.vp) (k l : S.Node)
    (h : keyBlock S a k = keyBlock S b l) : a = b ∧ k = l := by
  have eq := congrArg Vector.toList h
  change _ ++ tailL _ = _ ++ tailL _ at eq
  have e := List.append_cancel_right eq
  obtain ⟨ha, hk⟩ := List.append_inj e (by simp)
  exact ⟨ad_inj S (Vector.toList_inj.mp ha), Vector.toList_inj.mp hk⟩

theorem seed_inj : Function.Injective (seedBlock S) := by
  intro x y h
  have e := congrArg Vector.toList h
  exact Vector.toList_inj.mp (List.append_cancel_right e)

theorem seed_ne_singleton (pk : S.Node) (a : Bytes 22) (k : S.Node) :
    seedBlock S pk ≠ singletonBlock S a k := by
  intro h
  have e := congrArg (fun b : Blk => b.toList[22 + S.vp.params.n]?) h
  have hn := width S
  simp only [seedBlock, singletonBlock, Vector.toList, List.toList_toArray] at e
  rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)] at e
  simp [tailL, List.getElem?_replicate] at e

theorem balanced (P : S.Node → Prop) :
    Pr{let u ← $ᵗ St}[P (output S u)] = Pr{let y ← $ᵗ S.Node}[P y] := by
  let n := S.vp.params.n
  have hn : n ≤ 32 := width S
  let low (s : St) : Bytes (32-n) := Vector.ofFn fun i => s[i.val+n]'(by omega)
  have split : Function.Bijective (fun s : St => (output S s, low s)) := by
    constructor
    · intro s t h
      obtain ⟨h1,h2⟩ := Prod.mk.inj h
      apply Vector.ext
      intro i hi
      by_cases h : i < n
      · simpa [output] using congrArg (fun v : S.Node => v[i]'h) h1
      · have eq := congrArg (fun v : Bytes (32-n) => v[i-n]'(by omega)) h2
        simpa [low, show i-n+n = i by omega] using eq
    · rintro ⟨a,b⟩
      refine ⟨Vector.ofFn fun i : Fin 32 => if h : i.val < n then a[i.val]'h else b[i.val-n]'(by omega), ?_⟩
      apply Prod.ext
      · apply Vector.ext; intro i hi; simp [output, n]
      · apply Vector.ext; intro i hi; simp [low]
  exact (SampleableType.prEvent_uniformSample_comp_of_bijective split (fun z => P z.1)).trans
    (SampleableType.prEvent_uniformSample_fst P)

private theorem prefix_output (s : St) : byteArrayPrefixOrZero (bytesToByteArray s) S.vp.params.n = output S s := by
  have hraw : ((bytesToByteArray s).extract 0 S.vp.params.n).toList = s.toList.take S.vp.params.n := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : ((bytesToByteArray s).extract 0 S.vp.params.n).toList.length = S.vp.params.n := by
    rw [hraw]; simp [Nat.min_eq_left (width S)]
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [output, hraw]

/-- All singleton tweakable hashes use two SHA-256 blocks, at every FIPS node width. -/
theorem singleton_shape (g : CF St Blk) (pk : S.Node) (a : Bytes 22) (k : S.Node) :
    sha2ThashG (liftC g) S.vp.params pk a [k] =
      output S (g (g (IV128,seedBlock S pk),singletonBlock S a k)) := by
  change sha2ThashG (liftC g) S.vp.params pk a [k] = _
  simp only [sha2ThashG, List.length_cons, List.length_nil, ite_true, sha256G_shape, prefix_output]
  have blocks : padBlocks (sha2Prefix256Key pk a ++ concatBytes [k]) =
      [seedBlock S pk, singletonBlock S a k] := by
    have bytes : (sha2Prefix256Key pk a ++ concatBytes [k]).data.toList =
        (seedBlock S pk).toList ++ (a.toList ++ k.toList) := by
      simp [seedBlock, concatBytes, sha2Prefix256Key, bytesToByteArray, zeroByteArray, Vector.toList,
        List.append_assoc]
    unfold padBlocks
    rw [bytes]
    have pad : padL ((seedBlock S pk).toList ++ (a.toList ++ k.toList)) =
        (seedBlock S pk).toList ++ (singletonBlock S a k).toList := by
      simp [padL, singletonBlock, List.append_assoc, Vector.toList]
      rw [← Nat.add_assoc]
    rw [pad, blocksOf_cons]
    simpa only [List.append_nil, show blocksOf [] = [] from rfl, List.cons.injEq, true_and] using blocksOf_cons (singletonBlock S a k) []
  rw [blocks]
  rfl

/-- The PRF at every width factors through exactly two SHA-256 table lookups. -/
theorem shape (g : CF St Blk) (pk k : S.Node) (a : Reduction.SkAdrs S.vp) :
    (sha2PrimitivesG (liftC g) S.vp.params).PRF pk k a.val =
      prfF IV128 (seedBlock S) (keyBlock S) (output S) g k (pk,a) := by
  have ha := a.property.sha2Domain (fipsApprovedAddressBounds S.fips)
  let checked : Sha2Address := ⟨a.val, ha.1, ha.2.1, ha.2.2⟩
  have hcheck : Sha2Address.ofAdrs a.val = .ok checked := by
    simp [Sha2Address.ofAdrs, checked, ha.1, ha.2.1, ha.2.2]
  rw [PRF_eq_Thash _ _ _ _ _ hcheck]
  exact singleton_shape S g pk (sha2AdrsKey a.val) k

/-- SHA-512 table queries cannot affect the secret-address PRF computation. -/
theorem mixed_shape (tables : CompressionTables) (pk k : S.Node) (a : Reduction.SkAdrs S.vp) :
    (tablePrimitives tables S.vp.params).PRF pk k a.val =
      prfF IV128 (seedBlock S) (keyBlock S) (output S) tables.1 k (pk,a) :=
  by
    have h := shape S tables.1 pk k a
    simp only [tablePrimitives, sha2PrimitivesMixed, sha2PrimitivesG] at h ⊢
    exact h

/-- Advantage for the actual secret-address PRF, with the same table accessible to
the adversary. SHA-512 is unused by this component at every width. -/
noncomputable def advantage (A : PrfAdvI St Blk S.Node (Reduction.SkAdrs S.vp) S.Node) : ℝ≥0∞ :=
  (𝒟[do let g ← $ᵗ (CF St Blk)
        (Reduction.skPrfC S.vp (sha2PrimitivesG (liftC g) S.vp.params)).prfRealExperiment (A.inst g)]).boolDist
    (𝒟[do let g ← $ᵗ (CF St Blk); prfIdealExperiment (A.inst g)])

theorem bound (A : PrfAdvI St Blk S.Node (Reduction.SkAdrs S.vp) S.Node) (q qo : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (ho : IsQueryBoundP A (fun i => isPrfQ i = true) qo) :
    advantage S A ≤ (q : ℝ≥0∞) / 2^(8*S.vp.params.n) + (((q+qo)^2 : ℕ) : ℝ≥0∞) / 2^256 := by
  let : Finite (Reduction.SkAdrs S.vp) := Finite.of_injective _ (ad_inj S)
  let : Fintype (Reduction.SkAdrs S.vp) := Fintype.ofFinite _
  have eq (g : CF St Blk) : Reduction.skPrfC S.vp (sha2PrimitivesG (liftC g) S.vp.params) =
      prfSchemeI IV128 (seedBlock S) (keyBlock S) (output S) g := by
    unfold Reduction.skPrfC prfSchemeI
    congr 1
    funext k d
    exact shape S g d.1 k d.2
  have h := prfAdvantageI_le IV128 _ _ _ (keyBlock_inj S) (fun pk a k => seed_ne_singleton S pk (sha2AdrsKey a.val) k) (seed_inj S) (balanced S) A q qo hq ho
  unfold advantage
  simp only [eq]
  apply h.trans
  rw [card_bytes, card_St, pow_mul, div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  norm_num

end MIdeal.SkPrf

#print axioms MIdeal.SkPrf.shape
#print axioms MIdeal.SkPrf.bound
