import Integration.SlhDsaCompressionSingleTarget
import MReduction.ShakeOracle

/-! With at most one signed target, ITSR success gives a collision of two
distinct SHAKE input strings on the complete FIPS-decoded message digest. -/
namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.DigestTransport OracleComp OracleSpec ENNReal

abbrev Query (S : Sha2Set) := S.Node × S.Node × S.Node × List Byte
def encode (S : Sha2Set) (x : Query S) : List Byte :=
  x.1.toList ++ (x.2.1.toList ++ (x.2.2.1.toList ++ x.2.2.2))

private theorem prefix_inj {n : ℕ} {a b : Bytes n} {x y : List Byte}
    (h : a.toList ++ x = b.toList ++ y) : a = b ∧ x = y := by
  have ha := congrArg (List.take n) h
  have hb := congrArg (List.drop n) h
  constructor
  · apply Vector.toList_inj.mp
    simpa using ha
  · simpa using hb

theorem encode_injective (S : Sha2Set) : Function.Injective (encode S) := by
  rintro ⟨r,s,t,x⟩ ⟨u,v,w,y⟩ eq
  obtain ⟨rfl,eq⟩ := prefix_inj eq
  obtain ⟨rfl,eq⟩ := prefix_inj eq
  obtain ⟨rfl,rfl⟩ := prefix_inj eq
  rfl

abbrev Decoded (S : Sha2Set) := KeyedHash.Covering.Digest S.vp.params.h S.vp.params.a S.vp.params.k

/-- Freshness concerns the byte input; unused padding bits in the two XOF
answers may differ even on a win. -/
theorem collision_of_cover (S : Sha2Set) (H : List Byte → Bytes S.vp.params.m)
    (cand : Query S) (ts : List (Query S)) (len : ts.length ≤ 1)
    (fresh : cand ∉ ts)
    (win : ∀ i ∈ idxOf S.vp (H (encode S cand)), i ∈ ts.flatMap (fun z => idxOf S.vp (H (encode S z)))) :
    ∃ y ∈ ts, encode S cand ≠ encode S y ∧
      coveringDigest S.vp (H (encode S cand)) = coveringDigest S.vp (H (encode S y)) := by
  let d := H (encode S cand)
  have component (i : Fin S.vp.params.k) : ∃ y ∈ ts,
      (coveringDigest S.vp (H (encode S y))).1 = (coveringDigest S.vp d).1 ∧
      (coveringDigest S.vp (H (encode S y))).2 i = (coveringDigest S.vp d).2 i := by
    let needle := ((splitDigest S.vp.params d).forsAdrs, i.val * 2^S.vp.params.a +
      forsIdx S.vp.params (splitDigest S.vp.params d).md.toList i.val)
    have hn : needle ∈ idxOf S.vp d := by
      simp only [idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]
      exact ⟨i.val,i.isLt,rfl⟩
    obtain ⟨y,hy,hit⟩ := List.mem_flatMap.mp (win needle hn)
    exact ⟨y,hy,match_of_mem_idxOf S.vp d _ i hit⟩
  let i : Fin S.vp.params.k := ⟨0,by cases S <;> decide⟩
  obtain ⟨y,hy,addr,_⟩ := component i
  refine ⟨y,hy,(fun h => fresh (encode_injective S h ▸ hy)),Prod.ext addr.symm (funext fun j => ?_)⟩
  obtain ⟨z,hz,_,eq⟩ := component j
  have same : z = y := by
    rcases ts with _|⟨t,tail⟩
    · simp at hy
    cases tail with
    | nil => simp_all
    | cons => simp only [List.length_cons] at len; omega
  subst z
  exact eq.symm

theorem fraction (S : Sha2Set) (B : Finset (Decoded S)) :
    ((Finset.univ.filter fun y : Bytes S.vp.params.m => coveringDigest S.vp y ∈ B).card : ℝ) /
      Fintype.card (Bytes S.vp.params.m) = (B.card:ℝ)/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := by
  classical
  have u := Compression.MessageHash.covering_uniform S (fun z => z ∈ B)
  rw [MIdeal.Hmsg.digest_uniform S (fun d => coveringDigest S.vp d ∈ B)] at u
  have card : Fintype.card (Decoded S) = 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := by
    change Fintype.card (Fin (2^S.vp.params.h) × (Fin S.vp.params.k → Fin (2^S.vp.params.a))) = _
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin,←pow_mul,←pow_add]
  simp only [SampleableType.prEvent_uniformSample] at u
  have e := congrArg ENNReal.toReal u
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
    Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using e

end Reduction.ShakeSingle
#print axioms Reduction.ShakeSingle.encode_injective
#print axioms Reduction.ShakeSingle.collision_of_cover
#print axioms Reduction.ShakeSingle.fraction
