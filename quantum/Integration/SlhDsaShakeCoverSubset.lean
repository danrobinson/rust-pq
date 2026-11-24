import Integration.SlhDsaShakeSignatureItsr
import Integration.SlhDsaCompressionTargetSubset

namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.DigestTransport PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec
open Compression.Recording Classical
open Compression.MessageHash (Mask Masked)
open scoped ComplexOrder ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def project (S : Sha2Set) (m : Finset (Fin S.vp.params.k)) (d : Bytes S.vp.params.m) : Masked S m :=
  ((coveringDigest S.vp d).1,fun i => (coveringDigest S.vp d).2 i)

theorem project_fraction (S : Sha2Set) (m : Finset (Fin S.vp.params.k)) (B : Finset (Masked S m)) :
    ((Finset.univ.filter fun y : Bytes S.vp.params.m => project S m y ∈ B).card : ℝ) /
      Fintype.card (Bytes S.vp.params.m) = (B.card:ℝ)/2^(S.vp.params.h+S.vp.params.a*m.card) := by
  classical
  let leaf := Fin (2^S.vp.params.h)
  let digit := Fin (2^S.vp.params.a)
  let rest := {i : Fin S.vp.params.k // i ∉ m} → digit
  let e : Decoded S ≃ Masked S m × rest := (Equiv.prodCongr (Equiv.refl leaf)
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ m) (fun _ => digit))).trans (Equiv.prodAssoc ..).symm
  have hc := Compression.MessageHash.covering_uniform S (fun z => (z.1,fun i : m => z.2 i) ∈ B)
  have hu := (MIdeal.Hmsg.digest_uniform S (fun x => project S m x ∈ B)).symm.trans hc
  have h := hu.trans ((SampleableType.prEvent_uniformSample_comp_of_bijective e.bijective
    (fun z => z.1 ∈ B)).trans (SampleableType.prEvent_uniformSample_fst _))
  have card : Fintype.card (Masked S m) = 2^(S.vp.params.h+S.vp.params.a*m.card) := by
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Fintype.card_coe,←pow_mul,←pow_add]
  simp only [SampleableType.prEvent_uniformSample] at h
  simpa only [project,ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
    Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using congrArg ENNReal.toReal h

def pickTarget (S : Sha2Set) (N j : ℕ) (z : Transcript S) : Option (ShakeApi.Input N × ShakeApi.Input N) := do
  let y ← z.2[j]?
  if hx : (encode S z.1).length ≤ N then
    if hy : (encode S y).length ≤ N then some (BList.ofList _ hx,BList.ofList _ hy) else none
  else none

/-- A successful cover with at most s signatures has a target agreeing with
the forgery on the leaf address and on at least d+1 FORS coordinates. -/
theorem reports_subset (S : Sha2Set) (N s d : ℕ) (many : s*d < S.vp.params.k)
    (H : ShakeApi.RawTable S N) (z : Transcript S)
    (scope : z.2.length ≤ s ∧ (encode S z.1).length ≤ N ∧ ∀ y ∈ z.2, (encode S y).length ≤ N)
    (win : covered S (ShakeApi.extend H) z) :
    ∃ u : Mask S (d+1) × Fin s, Database.reports (project S u.1.1) (pickTarget S N u.2 z) H := by
  classical
  let hash := fun x => ShakeApi.extend H (encode S x)
  let dec := fun x => coveringDigest S.vp (hash x)
  have component (i : Fin S.vp.params.k) : ∃ j : Fin z.2.length,
      (dec z.2[j]).1 = (dec z.1).1 ∧ (dec z.2[j]).2 i = (dec z.1).2 i := by
    let a := splitDigest S.vp.params (hash z.1)
    let needle := (a.forsAdrs,i.val*2^S.vp.params.a+forsIdx S.vp.params a.md.toList i.val)
    have hn : needle ∈ idxOf S.vp (hash z.1) := by
      simp only [idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]; exact ⟨i.val,i.isLt,rfl⟩
    obtain ⟨y,hy,hit⟩ := List.mem_flatMap.mp (win.2 needle hn)
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hy
    subst y
    exact ⟨⟨j,hj⟩,match_of_mem_idxOf S.vp _ _ i hit⟩
  choose f hf using component
  obtain ⟨j,_,large⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := f) (n := d)
    (fun _ _ => Finset.mem_univ _) (by simpa using (Nat.mul_le_mul_right d scope.1).trans_lt many)
  obtain ⟨m,sub,size⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt large)
  have same (i : m) : f i.val = j := (Finset.mem_filter.mp (sub i.property)).2
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (size ▸ Nat.succ_pos d)
  let y := z.2[j]
  have hy : y ∈ z.2 := List.getElem_mem ..
  have eq : project S m (hash y) = project S m (hash z.1) := by
    apply Prod.ext
    · change (dec z.2[j]).1 = (dec z.1).1
      simpa only [same ⟨i,hi⟩] using (hf i).1
    · exact funext fun a => by
        change (dec z.2[j]).2 a.val = (dec z.1).2 a.val
        simpa only [same a] using (hf a.val).2
  refine ⟨(⟨m,size⟩,⟨j.val,j.isLt.trans_le scope.1⟩),BList.ofList _ scope.2.1,BList.ofList _ (scope.2.2 y hy),?_,?_,?_⟩
  · simp [pickTarget,scope.2.1,y]
    exact scope.2.2 y hy
  · intro h
    exact win.1 (encode_injective S (by simpa only [BList.ofFn_ofList] using congrArg (fun x : ShakeApi.Input N => List.ofFn x.2) h) ▸ hy)
  · simpa only [hash,ShakeApi.extend_apply _ _ scope.2.1,ShakeApi.extend_apply _ _ (scope.2.2 y hy)] using eq.symm

noncomputable def subsetLoss (S : Sha2Set) (q s d : ℕ) : ℝ≥0∞ :=
  (S.vp.params.k.choose (d+1)*s : ℕ) * ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*(d+1)))

theorem subset_search (S : Sha2Set) (N s d : ℕ) (many : s*d < S.vp.params.k)
    {E : Type} [Fintype E] [DecidableEq E]
    (M : ShakeApi.RawTable S N → Closed (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) (Transcript S))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (hscope : ∀ H, AllQueries (fun _ => True) (fun z : Transcript S => z.2.length ≤ s ∧ (encode S z.1).length ≤ N ∧
      ∀ y ∈ z.2, (encode S y).length ≤ N) (M H))
    (ρ : Matrix (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) _ ℂ)
    (pos : ρ.PosSemidef) (tr : ρ.trace = 1) :
    SetOracle.uniformMean (fun H => qWeight (covered S (ShakeApi.extend H)) (M H) ρ) ≤ subsetLoss S q s d := by
  classical
  let U := Mask S (d+1) × Fin s
  let P (u : U) H z := Database.reports (project S u.1.1) (pickTarget S N u.2 z) H
  have each (u : U) : SetOracle.uniformMean (fun H => qWeight (P u H) (M H) ρ) ≤
      ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*(d+1))) := by
    obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
    obtain ⟨v,rfl⟩ := exists_subState ρ pos tr
    unfold SetOracle.uniformMean
    simp_rw [← he]
    apply Compile.mixed_mean_over _ x v q hx id _ _ (by positivity)
    intro w
    apply RawSearch.pure_mean (project S u.1.1) _ (by positivity) _ _ (fun _ y => y) (pickTarget S N u.2) x q hx w
    intro B
    simpa only [u.1.2] using (project_fraction S u.1.1 B).le
  have per H : qWeight (covered S (ShakeApi.extend H)) (M H) ρ ≤ ∑ u : U, qWeight (P u H) (M H) ρ := by
    apply le_trans _ (Compression.MessageHash.union_weight (M H) ρ Finset.univ (fun u => P u H))
    apply QItsr.qWeight_mono_allQ (hscope H)
    intro z scope win
    obtain ⟨u,hu⟩ := reports_subset S N s d many H z scope win
    exact ⟨u,Finset.mem_univ _,hu⟩
  apply (Finset.sum_le_sum fun H _ => mul_le_mul' (a := unifW _ H) le_rfl (per H)).trans
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : U, ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*(d+1))) :=
      Finset.sum_le_sum fun u _ => each u
    _ = _ := by simp [U,subsetLoss,Mask,nsmul_eq_mul]

end Reduction.ShakeSingle
#print axioms Reduction.ShakeSingle.reports_subset
#print axioms Reduction.ShakeSingle.subset_search
