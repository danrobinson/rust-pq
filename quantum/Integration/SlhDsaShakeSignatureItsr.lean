import Integration.SlhDsaShakeApiItsr
import Integration.SlhDsaShakeCoverSearch
import Integration.SlhDsaCompressionItsrSupport

namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder
open Classical

variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "Q" => fun H => qPureBytesToInternal (ShakeApi.rawForger S N r seeds F H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)

private theorem support (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (H : ShakeApi.RawTable S N) :
    AllQueries (fun _ => True) (scopedTranscript S N)
      (close (ITSROracles (itsrProblem S.vp (P H))) (qbItsrL (Q H)) []) := by
  let A := Q H
  have hQ (pk) : AllQueries (QG _ (Gint c.ml)) (fun z => z.1.length ≤ c.ml) (A.main pk) :=
    allQ_and (allQ_qPureBytesToInternal c.ml _ (fun pkb => allQ_compileQ c H _ (hc pkb)) pk)
      (out_qPureBytesToInternal _ c.ml (fun pkb => allQ_out_simulateQ (compileImplQ H) (hc pkb)) pk)
  have hO := allQ_qItsrOpen (P H) c.ml A hQ
  have bound : CountBound (QC _ isR) (qbItsrL A) 1 := cb_qLazyRun _ _ (cb_qItsrOpen (P H) A fun pk =>
    cb_qPureBytesToInternal _ (fun pkb => cb_compileQ H (F.main pkb) (hs pkb)) pk)
  have h := Compression.MessageHash.target_support (itsrProblem S.vp (P H)) (Ptgt _ c.ml) _
    (qbItsrL A) 1 [] (allQ_and (allQ_qLazyRun _ (Ptgt (P H) c.ml) _
      (allQ_mono (fun _ h => h) (fun _ _ => trivial) hO)) (out_qLazyRun _ _ hO)) bound
  apply allQ_mono (fun _ _ => trivial) _ h
  intro z hz
  simp only [List.not_mem_nil,false_or,List.length_nil,Nat.zero_add,Ptgt] at hz
  have len (x : Query S) : (encode S x).length = 3*S.vp.params.n + x.2.2.2.length := by
    simp only [encode,List.length_append,Vector.length_toList]
    omega
  refine ⟨hz.2.1,?_,fun y hy => ?_⟩
  · rw [len]; exact (Nat.add_le_add_left hz.1 _).trans raw
  · rw [len]; exact (Nat.add_le_add_left (hz.2.2 y hy) _).trans raw

theorem signature_itsr (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N) (q : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (Q H)) F.ρ₀) ≤
      ENNReal.ofReal (16*(((q+itsrHashes S.vp 1:ℕ):ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)) := by
  classical
  let base : ShakeApi.Xof S := fun _ => default
  let mach := fun H => close (ITSROracles (itsrProblem S.vp (ShakeApi.primitives S base)))
    (ShakeApi.itsrMach S N r seeds F base H) []
  have eq (H : ShakeApi.RawTable S N) : mach H =
      close (ITSROracles (itsrProblem S.vp (P H))) (qbItsrL (Q H)) [] := by
    unfold mach
    rw [ShakeApi.itsrMach_oracle]
    rfl
  have u := covered_search S N mach _ (PUE.close _ (fun t s => EvalCost.const _)
    (ShakeApi.pue_itsrMach S N r seeds F base q 1 hq hs) []) (fun H => eq H ▸ support S N r seeds F c raw hs hc H)
    F.ρ₀ F.posSemidef F.trace_eq_one
  apply le_trans _ u
  apply Finset.sum_le_sum
  intro H _
  apply mul_le_mul' le_rfl
  dsimp only
  rw [eq H]
  unfold qItsrAdvantage
  have events : (fun z : Transcript S => (itsrProblem S.vp (P H)).Wins z.2 z.1) = covered S (ShakeApi.extend H) := by
    funext z
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    have idx : (itsrProblem S.vp (P H)).indexSet =
        fun (y : Query S) => Ideal.idxOf S.vp (ShakeApi.extend H (encode S y)) := by
      funext y
      change forsIndices _ (splitDigest _ (ShakeApi.extend H _)) = forsIndices _ (splitDigest _ (ShakeApi.extend H _))
      simp [encode,List.append_assoc]
    change (∀ i ∈ (itsrProblem S.vp (P H)).indexSet z.1, i ∈ z.2.flatMap (itsrProblem S.vp (P H)).indexSet) ↔ _
    rw [idx]
    exact Iff.rfl
  apply le_of_eq
  congr 1

/-- The actual one-signature reduction, charged for key generation and signing.
The exponent is a common lower bound on the digest security across all six sets. -/
theorem signature_itsr_benchmark (c : Caps) (msg : c.ml = 65536)
    (raw : 3*S.vp.params.n+65536 ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (Q H)) F.ρ₀) ≤
      ENNReal.ofReal ((2:ℝ)^100)⁻¹ := by
  apply (signature_itsr S N r seeds F c (msg ▸ raw) _ hq hs hc).trans
  apply digest_search_budget
  cases S <;> decide +kernel

end Reduction.ShakeSingle
#print axioms Reduction.ShakeSingle.signature_itsr
#print axioms Reduction.ShakeSingle.signature_itsr_benchmark
