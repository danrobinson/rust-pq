import Integration.SlhDsaShakePermutationItsrSource
import Integration.SlhDsaShakeCoverSearch
import Integration.SlhDsaCompressionItsrSupport

namespace Reduction.ShakePermutation.ItsrCost
open ShakeSingle MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder
open Classical

variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger Port Words E)
local notation "Q" => fun H => qPureBytesToInternal (ShakeApi.forgerAt S r seeds F (ShakeApi.extend (SkCost.table S N H)) H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N H))

private theorem support (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (H : Port → Words) :
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
  have len (x : Query S) : (ShakeSingle.encode S x).length = 3*S.vp.params.n + x.2.2.2.length := by
    simp only [ShakeSingle.encode,List.length_append,Vector.length_toList]
    omega
  refine ⟨hz.2.1,?_,fun y hy => ?_⟩
  · rw [len]; exact (Nat.add_le_add_left hz.1 _).trans raw
  · rw [len]; exact (Nat.add_le_add_left (hz.2.2 y hy) _).trans raw


def blank : ShakeApi.Xof S := fun _ => default
noncomputable def transcript (H : Port → Words) : Closed (WS Port Words E) (Transcript S) :=
  close (ITSROracles (itsrProblem S.vp (ShakeApi.primitives S (blank S)))) (itsrMach S N r seeds F (blank S) H) []

theorem transcript_native (H : Port → Words) : transcript S N r seeds F H =
    close (ITSROracles (itsrProblem S.vp (P H))) (qbItsrL (Q H)) [] := by
  unfold transcript
  rw [itsrMach_oracle]
  rfl

noncomputable def candidates (H : Port → Words) := ShakeSingle.pair S N <$> transcript S N r seeds F H

theorem candidates_cost (cap : N ≤ ShakeApi.rawCap S 67 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    PUE (spec := unifSpec) cnt0 (candidates S N r seeds F) (2^41) := by
  have h := PUE.close (fun _ => ITSROracles (itsrProblem S.vp (ShakeApi.primitives S (blank S)))) (fun t s => EvalCost.const _)
    (pue_itsrMach S N r seeds F (blank S) cap _ _ hq hs) []
  exact (PUE.map (ShakeSingle.pair S N) h).mono (by cases S <;> decide +kernel)

def reports (π : Permutation) (z : Option (ShakeApi.Input N × ShakeApi.Input N)) : Prop :=
  ∃ x y, z = some (x,y) ∧ x ≠ y ∧
    DigestTransport.coveringDigest S.vp (answer S (lanes π) (List.ofFn x.2)) =
    DigestTransport.coveringDigest S.vp (answer S (lanes π) (List.ofFn y.2))

theorem pair_reduction (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (π : Permutation) :
    qItsrAdvantage (itsrProblem S.vp (P (oracle π))) (qbItsrL (Q (oracle π))) F.ρ₀ ≤
      qWeight (reports S N π) (candidates S N r seeds F (oracle π)) F.ρ₀ := by
  let H := oracle π
  let T := SkCost.table S N H
  let actual := transcript S N r seeds F H
  have h := support S N r seeds F c raw hs hc H
  have ev : (fun z : Transcript S => (itsrProblem S.vp (P H)).Wins z.2 z.1) = covered S (ShakeApi.extend T) := by
    funext z
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    have idx : (itsrProblem S.vp (P H)).indexSet =
        fun (y : Query S) => Ideal.idxOf S.vp (ShakeApi.extend T (ShakeSingle.encode S y)) := by
      funext y
      change forsIndices _ (splitDigest _ (ShakeApi.extend T _)) = forsIndices _ (splitDigest _ (ShakeApi.extend T _))
      simp [ShakeSingle.encode,List.append_assoc]
    change (∀ i ∈ (itsrProblem S.vp (P H)).indexSet z.1, i ∈ z.2.flatMap (itsrProblem S.vp (P H)).indexSet) ↔ _
    rw [idx]
    exact Iff.rfl
  unfold candidates
  rw [qWeight_map,transcript_native]
  unfold qItsrAdvantage
  letI : DecidablePred (fun z : Transcript S => (itsrProblem S.vp (P H)).Wins z.2 z.1) :=
    fun z => instDecidableWins _ _ _
  apply qWeight_mono_allQ h
  intro z hz win
  obtain ⟨x,y,hxy,ne,same⟩ := reports_of_cover S N T z hz (ev ▸ win)
  exact ⟨x,y,hxy,ne,same⟩

end Reduction.ShakePermutation.ItsrCost
#print axioms Reduction.ShakePermutation.ItsrCost.candidates_cost
#print axioms Reduction.ShakePermutation.ItsrCost.pair_reduction
