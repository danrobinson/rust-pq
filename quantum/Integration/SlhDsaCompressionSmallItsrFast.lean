import Integration.SlhDsaCompressionItsrCover
import MIdeal.Itsr128f

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Reduction.Compression.SmallItsr.Fast
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.DigestTransport Classical OracleComp OracleSpec
abbrev vp := Sha2Set.s128f.vp
abbrev Key := Fin (2^55) × Fin (2^6)
abbrev Ix := Fin vp.params.k
def trim (d : Bytes 34) (i : Ix) : Key :=
  ((finProdFinEquiv (m := 2^55) (n := 2^11)).symm (coveringDigest vp d).1 |>.1,(coveringDigest vp d).2 i)

private theorem same_bytes (s t u : St) (i : ℕ) (h : i < 32) :
    (digest128f (s,t))[i]'(by omega) = (digest128f (s,u))[i]'(by omega) := by
  simp only [digest128f,MIdeal.Sha512.takeBytes,Vector.getElem_ofFn]
  exact (Vector.getElem_append_left h).trans (Vector.getElem_append_left h).symm

private theorem front (a b : Bytes 34) (he : ∀ j (hj : j < 32), a[j]'(by omega) = b[j]'(by omega)) :
    a.extract 0 25 = b.extract 0 25 := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_extract,Vector.getElem_extract]
  apply he
  omega

private theorem middle (a b : Bytes 34) (he : ∀ j (hj : j < 32), a[j]'(by omega) = b[j]'(by omega)) :
    (a.extract 25 33).toList.take 7 = (b.extract 25 33).toList.take 7 := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have h := (Nat.lt_min.mp (by simpa only [List.length_take] using hj)).1
    simp only [List.getElem_take,Vector.getElem_toList,Vector.getElem_extract]
    apply he
    omega

private theorem md_of_front (p : Params) (a b : Bytes p.m)
    (he : a.extract 0 p.digestBytes = b.extract 0 p.digestBytes) : (splitDigest p a).md = (splitDigest p b).md :=
  congrArg (Vector.cast (by simp [Params.m]; omega)) he

private theorem tree_of_middle (p : Params) (a b : Bytes p.m)
    (he : (a.extract p.digestBytes (p.digestBytes+p.treeIdxBytes)).toList.take 7 =
      (b.extract p.digestBytes (p.digestBytes+p.treeIdxBytes)).toList.take 7) :
    (digestTreeBytes p a).toList.take 7 = (digestTreeBytes p b).toList.take 7 := he

private theorem same_md (s t u : St) :
    (splitDigest vp.params (digest128f (s,t))).md = (splitDigest vp.params (digest128f (s,u))).md :=
  md_of_front vp.params _ _ (front (digest128f (s,t)) (digest128f (s,u)) (same_bytes s t u))

private theorem tree_prefix (s t u : St) :
    (digestTreeBytes vp.params (digest128f (s,t))).toList.take 7 =
      (digestTreeBytes vp.params (digest128f (s,u))).toList.take 7 :=
  tree_of_middle vp.params _ _ (middle (digest128f (s,t)) (digest128f (s,u)) (same_bytes s t u))

private theorem tree_form (d : Bytes 34) : ∃ b : Byte,
    (digestTreeBytes vp.params d).toList = (digestTreeBytes vp.params d).toList.take 7 ++ [b] := by
  let t := (digestTreeBytes vp.params d).toList
  have len : t.length = 8 := Vector.length_toList
  refine ⟨t[7]'(by omega),?_⟩
  have h := List.take_concat_get (l := t) (i := 7) (by omega)
  change t = _
  exact (List.take_of_length_le (show t.length ≤ 8 by omega)).symm.trans (by simpa only [List.concat_eq_append] using h.symm)

/-- Counter one contributes the final tree byte and the three lowest leaf bits.
Removing those eleven bits preserves the other 55 position bits and every
FORS coordinate, even when counter one's output depends on the row. -/
theorem trim_independent (s t u : St) (i : Ix) : trim (digest128f (s,t)) i = trim (digest128f (s,u)) i := by
  apply Prod.ext
  · apply Fin.ext
    change ((coveringDigest vp (digest128f (s,t))).1.val / 2048) = _
    change _ = ((coveringDigest vp (digest128f (s,u))).1.val / 2048)
    rw [coveringDigest_fst_val,coveringDigest_fst_val]
    obtain ⟨b,hb⟩ := tree_form (digest128f (s,t))
    obtain ⟨c,hc⟩ := tree_form (digest128f (s,u))
    have hx := tree_prefix s t u
    have h1 := (splitDigest vp.params (digest128f (s,t))).idxLeaf.isLt
    have h2 := (splitDigest vp.params (digest128f (s,u))).idxLeaf.isLt
    change _ < 8 at h1 h2
    change (toInt _ % 9223372036854775808 * 8 + _)/2048 =
      (toInt _ % 9223372036854775808 * 8 + _)/2048
    rw [hb,hc,hx,toInt_append_byte,toInt_append_byte]
    have h3 : b.toNat < 256 := b.toBitVec.isLt
    have h4 : c.toNat < 256 := c.toBitVec.isLt
    omega
  · apply Fin.ext
    change ((coveringDigest vp (digest128f (s,t))).2 i).val = ((coveringDigest vp (digest128f (s,u))).2 i).val
    rw [coveringDigest_snd_val,coveringDigest_snd_val,same_md s t u]

end Reduction.Compression.SmallItsr.Fast
#print axioms Reduction.Compression.SmallItsr.Fast.trim_independent
