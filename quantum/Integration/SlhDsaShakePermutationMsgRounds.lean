import Integration.SlhDsaShakePermutationMsgCut
import Integration.SlhDsaShakePermutationMsgFormat

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security OracleSpec OracleComp PQ.Interactive Quantum ENNReal SetOracle QMsg ShakeApi MsgSplit MsgTrajectory
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxHeartbeats 1800000

/-- A pointwise replacement of an independent classical experiment holds
under an arbitrary common quantum prefix, including adaptive instruments. -/
private theorem mean_post {T W Z A : Type} [Fintype W] [Fintype T] (p : Closed W Z)
    (l : T → Z → Closed W A) (r : Z → Closed W A) (acc : A → Prop) [DecidablePred acc]
    (h : ∀ z M, uniformMean (fun t => qWeight acc (l t z) M) = qWeight acc (r z) M)
    (M : Matrix W W ℂ) :
    uniformMean (fun t => qWeight acc (p >>= l t) M) = qWeight acc (p >>= r) M := by
  induction p using OracleComp.inductionOn generalizing M with
  | pure z => simpa using h z M
  | query_bind i k ih =>
    simp only [bind_assoc]
    rcases i with j|n
    · simp only [qWeight_instr_bind,uniformMean,Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => ih i _
    · simp only [qWeight_unif_bind,uniformMean]
      conv_lhs => arg 2; intro t; rw [mul_left_comm]
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => ih i M

private theorem bind_valid {I Z A : Type} {spec : OracleSpec I} (p : OracleComp spec Z) (ok : Z → Prop)
    (hp : AllQueries (fun _ => True) ok p) (l r : Z → OracleComp spec A)
    (h : ∀ z, ok z → l z = r z) : p >>= l = p >>= r := by
  induction p using OracleComp.inductionOn with
  | pure z => simpa using h z hp
  | query_bind i k ih =>
    simp only [bind_assoc]
    exact bind_congr fun a => ih a (hp.2 a)

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => rawCap S 67 65536
local notation "Work" => WS Port Words E
local notation "D" => S.Node × List SLHDSA.Byte
local notation "Stages" => FamilyStage Port Words E D S.Node Bool (2^41)
local notation "P" => native S N rand seeds F
local notation "P₀" => fun π : Permutation => ShakeApi.primitives S (extend (SkCost.table S N (oracle π)))

def roundValue (π σ : Permutation) (k : S.Node) (d : D) : S.Node :=
  (SkFormat.split S (MsgTrajectory.suffix π (laterBlocks S d.1 d.2) (σ (join (firstBlock S k d.1 d.2) 0)))).1

private theorem real_value (π : Permutation) (k : S.Node) (d : D) (bound : d.2.length ≤ 65536) :
    ((P₀) π).PRFmsg k d.1 d.2 = roundValue S π π k d := by
  apply Eq.trans _ (MsgTrajectory.byte_prf S π k d.1 d.2 _ _ (split_blocks S k d.1 d.2))
  change prefixBytes S.vp.params.n (extend (SkCost.table S N (oracle π)) (k.toList ++ d.1.toList ++ d.2)) =
    hash (lanes π) (nd k ++ nd d.1 ++ sp d.2) S.vp.params.n
  rw [SkCost.table,extend_restrict _ _ _ _ ((in_range S 67 65536 N le_rfl).2.2.1 _ _ _ bound),hash_prefix]
  simp only [sp_append]
  rfl

variable (pre : (Port → Words) → Closed (WS Port Words E) (FamilyStage Port Words E (S.Node × List SLHDSA.Byte) S.Node Bool (2^41)))
    (eq : ∀ H, before (native S (rawCap S 67 65536) rand seeds F H) = specialize H <$> pre H)
    (ok : ∀ H, AllQueries (fun _ => True) (validStage S (E:=E) 65536) (pre H))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)

include eq ok hs in
theorem same_round (π : Permutation) (M : Matrix Work Work ℂ) :
    qPrfRealPr (msgPrf S.vp ((P₀) π)) (P (oracle π)) M =
      uniformMean (fun k => qWeight (· = true) (pre (oracle π) >>= callPost (oracle π) (roundValue S π π k)) M) := by
  let H := oracle π
  change qWeight (· = true) (liftU ($ᵗ S.Node) >>= fun k => ansRun (fun d : D => ((P₀) π).PRFmsg k d.1 d.2) (P H)) M = _
  rw [qWeight_liftU_uniform_bind]
  simp only [uniformMean,unifW,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply congrArg (fun p => qWeight (· = true) p M)
  change ansRun (fun d : D => ((P₀) π).PRFmsg k d.1 d.2) (P H) = _
  rw [answered _ (P H) (native_count S (extend (SkCost.table S N H)) F rand seeds H 1 hs),eq,bind_map_left]
  apply bind_valid _ _ (ok H)
  rintro (a|⟨d,post⟩) cap
  · rfl
  · exact congrArg (fun r => post.val r H) (real_value S π k d cap)

include eq hs in
theorem independent_round_game (π : Permutation) (k : S.Node) (M : Matrix Work Work ℂ) :
    uniformMean (fun σ : Permutation => qWeight (· = true) (pre (oracle π) >>= callPost (oracle π) (roundValue S π σ k)) M) =
      qPrfIdealPr (P (oracle π)) M := by
  let H := oracle π
  change _ = qWeight (· = true) (idealRun (P H) ∅) M
  rw [fresh (P H) (native_count S (extend (SkCost.table S N H)) F rand seeds H 1 hs),eq,bind_map_left]
  apply mean_post
  rintro (a|⟨d,post⟩) M'
  · change uniformMean (fun _ : Permutation => qWeight _ (pure a : Closed Work Bool) M') = _
    simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
    rfl
  · change uniformMean (fun σ => qWeight (· = true) (post.val (roundValue S π σ k d) H) M') =
      qWeight (· = true) (liftU ($ᵗ S.Node) >>= fun r => post.val r H) M'
    rw [qWeight_liftU_uniform_bind]
    simpa only [uniformMean,unifW,Finset.mul_sum,roundValue] using independent_round S π k d.1 d.2 (fun r => qWeight (· = true) (post.val r H) M')

end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.same_round
#print axioms Reduction.ShakePermutation.MsgCost.independent_round_game
