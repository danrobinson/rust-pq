import Integration.SlhDsaCompressionItsrWalk

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.DigestTransport
variable (S : Sha2Set)

def coordinate (i : Fin S.vp.params.k) (s : Chain512) :
    Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a) :=
  let z := coveringDigest S.vp (digest S s)
  (z.1,z.2 i)

/-- One candidate cell is covered across all FORS trees. Each covering cell
is physically distinct from that candidate, and can cover several coordinates. -/
theorem cover_cells (g : CompressionTables) (xs : List HmacKey.InputCell) (nd : xs.Nodup)
    (cov : CovP (idxOf S.vp) (xs.map fun u => digest S (g.2 u))) :
    ∃ u ∈ xs, ∀ i : Fin S.vp.params.k, ∃ v ∈ xs, u ≠ v ∧ coordinate S i (g.2 u) = coordinate S i (g.2 v) := by
  obtain ⟨pre,y,post,hs,coverage⟩ := cov
  obtain ⟨l,r,rfl,rfl,hr⟩ := List.map_eq_append_iff.mp hs
  obtain ⟨u,tail,rfl,rfl,rfl⟩ := List.map_eq_cons_iff.mp hr
  refine ⟨u,by simp,fun i => ?_⟩
  let d := digest S (g.2 u)
  obtain ⟨z,hz,hiz⟩ := coverage ((splitDigest S.vp.params d).forsAdrs,
      i.val * 2^S.vp.params.a + forsIdx S.vp.params (splitDigest S.vp.params d).md.toList i.val)
    (by
      simp only [idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]
      exact ⟨i.val,i.isLt,rfl⟩)
  rw [← List.map_append] at hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  obtain ⟨h₁,h₂⟩ := match_of_mem_idxOf S.vp d (digest S (g.2 v)) i hiz
  refine ⟨v,?_,?_,Prod.ext h₁.symm h₂.symm⟩
  · simpa only [List.mem_append,List.mem_cons] using
      (List.mem_append.mp hv).elim (fun hl => Or.inl hl) (fun ht => Or.inr (Or.inr ht))
  · rintro rfl
    rcases List.mem_append.mp hv with h|h
    · exact (List.nodup_append.mp nd).2.2 _ h _ (List.mem_cons_self ..) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp nd).2.1).1 h

open OracleComp OracleSpec KeyedHash.Covering

/-- The FIPS digest decoder applied to a fresh SHA-512 result yields a
uniform leaf and independent uniform FORS coordinates. -/
theorem covering_uniform (P : Digest S.vp.params.h S.vp.params.a S.vp.params.k → Prop) :
    Pr{let s ← $ᵗ Chain512}[P (coveringDigest S.vp (digest S s))] =
      Pr{let d ← $ᵗ (Digest S.vp.params.h S.vp.params.a S.vp.params.k)}[P d] := by
  classical
  rw [digest_uniform S (fun d => P (coveringDigest S.vp d))]
  let _ : MeasurableSpace (Bytes S.vp.params.m) := ⊤
  let _ : DiscreteMeasurableSpace (Bytes S.vp.params.m) := ⟨fun _ => trivial⟩
  rw [prEvent_eq_evalDist_of_discrete,prEvent_eq_evalDist_of_discrete]
  exact evalDist_uniformSample_preimage_coveringDigest S.vp {d | P d}

/-- Each coordinate match checks both the hypertree position and one FORS index. -/
theorem coordinate_uniform (i : Fin S.vp.params.k) (P : Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a) → Prop) :
    Pr{let s ← $ᵗ Chain512}[P (coordinate S i s)] =
      Pr{let u ← $ᵗ (Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a))}[P u] := by
  classical
  let leaf := Fin (2^S.vp.params.h)
  let digit := Fin (2^S.vp.params.a)
  let rest := {j : Fin S.vp.params.k // j ≠ i} → digit
  let e : Digest S.vp.params.h S.vp.params.a S.vp.params.k ≃ (leaf × digit) × rest :=
    (Equiv.prodCongr (Equiv.refl leaf) (Equiv.funSplitAt i digit)).trans (Equiv.prodAssoc ..).symm
  have hc := covering_uniform S (fun d => P (d.1,d.2 i))
  exact hc.trans ((SampleableType.prEvent_uniformSample_comp_of_bijective e.bijective
    (fun z => P z.1)).trans (SampleableType.prEvent_uniformSample_fst P))

/-- Density of an arbitrary set of leaf-and-digit matches in a fresh
compression cell, in the form consumed by the recording-oracle estimate. -/
theorem coordinate_fraction (i : Fin S.vp.params.k) (B : Finset (Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a))) :
    ((Finset.univ.filter fun y => coordinate S i y ∈ B).card : ℝ) / Fintype.card Chain512 =
      (B.card : ℝ) / 2^(S.vp.params.h + S.vp.params.a) := by
  have h := coordinate_uniform S i (fun v => v ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at h
  have e := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_add, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using e

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.cover_cells
#print axioms Reduction.Compression.MessageHash.covering_uniform
#print axioms Reduction.Compression.MessageHash.coordinate_uniform
#print axioms Reduction.Compression.MessageHash.coordinate_fraction
