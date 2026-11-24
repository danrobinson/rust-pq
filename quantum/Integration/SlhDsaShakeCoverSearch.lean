import Integration.SlhDsaShakeDigestSearch

namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.DigestTransport PQ.Interactive Quantum OracleComp OracleSpec
open Compression.Recording Classical
open scoped ComplexOrder
abbrev Transcript (S : Sha2Set) := Query S × List (Query S)

def pair (S : Sha2Set) (N : ℕ) (z : Transcript S) : Option (ShakeApi.Input N × ShakeApi.Input N) := do
  let [y] := z.2 | none
  if hx : (encode S z.1).length ≤ N then
    if hy : (encode S y).length ≤ N then
      some (BList.ofList _ hx,BList.ofList _ hy)
    else none
  else none

def covered (S : Sha2Set) (H : ShakeApi.Xof S) (z : Transcript S) : Prop :=
  z.1 ∉ z.2 ∧ ∀ i ∈ idxOf S.vp (H (encode S z.1)), i ∈ z.2.flatMap (fun y => idxOf S.vp (H (encode S y)))

def scopedTranscript (S : Sha2Set) (N : ℕ) (z : Transcript S) : Prop :=
  z.2.length ≤ 1 ∧ (encode S z.1).length ≤ N ∧ ∀ y ∈ z.2, (encode S y).length ≤ N

theorem reports_of_cover (S : Sha2Set) (N : ℕ) (H : ShakeApi.RawTable S N) (z : Transcript S)
    (bounds : scopedTranscript S N z) (win : covered S (ShakeApi.extend H) z) :
    Database.reports (coveringDigest S.vp) (pair S N z) H := by
  obtain ⟨y,hy,ne,eq⟩ := collision_of_cover S _ z.1 z.2 bounds.1 win.1 win.2
  have hx := bounds.2.1
  have hlen := bounds.2.2 y hy
  have single : z.2 = [y] := by
    have n := bounds.1
    cases ht : z.2 with
    | nil => simp [ht] at hy
    | cons a t =>
      cases t with
      | cons => simp [ht] at n
      | nil => simpa [ht] using (List.mem_singleton.mp (ht ▸ hy)).symm
  refine ⟨BList.ofList _ hx,BList.ofList _ hlen,?_,?_,?_⟩
  · simp [pair,single,hx,hlen]
  · intro e
    exact ne (by simpa only [BList.ofFn_ofList] using congrArg (fun x : ShakeApi.Input N => List.ofFn x.2) e)
  · simpa only [ShakeApi.extend_apply _ _ hx,ShakeApi.extend_apply _ _ hlen] using eq

/-- ITSR success for any bounded one-target transcript computation on the actual
shared port. The computation can use digest prefixes from the same table. -/
theorem covered_search (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
    (M : ShakeApi.RawTable S N → Closed (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) (Transcript S))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (hscope : ∀ H, AllQueries (fun _ => True) (scopedTranscript S N) (M H))
    (ρ₀ : Matrix (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) _ ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    SetOracle.uniformMean (fun H => qWeight (covered S (ShakeApi.extend H)) (M H) ρ₀) ≤
      ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)) := by
  apply le_trans _ (digest_search S N M (pair S N) q hq ρ₀ pos tr)
  apply Finset.sum_le_sum
  intro H _
  exact mul_le_mul' le_rfl (QItsr.qWeight_mono_allQ (hscope H) (reports_of_cover S N H) ρ₀)

end Reduction.ShakeSingle
#print axioms Reduction.ShakeSingle.covered_search
