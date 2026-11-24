import Integration.SlhDsaShakePermutationMsgPrefixReal

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle QMsg ShakeApi MsgSplit MsgTrajectory
open scoped ComplexOrder
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
noncomputable section
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => rawCap S 67 65536
local notation "Work" => WS Port Words E
local notation "D" => S.Node × List SLHDSA.Byte
local notation "P" => native S N rand seeds F
local notation "P₀" => fun π : Permutation => ShakeApi.primitives S (extend (SkCost.table S N (oracle π)))
variable (pre : (Port → Words) → Closed (WS Port Words E) (FamilyStage Port Words E (S.Node × List SLHDSA.Byte) S.Node Bool (2^41)))
    (hp : PUE (spec:=unifSpec) cnt0 pre (2^41))
    (eq : ∀ H, before (native S (rawCap S 67 65536) rand seeds F H) = specialize H <$> pre H)
    (ok : ∀ H, AllQueries (fun _ => True) (validStage S (E:=E) 65536) (pre H))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)

def real_post (δ : Permutation) (k : S.Node) :=
  callPost (E:=E) (A:=Bool) (Q:=2^41) (oracle δ) (fun d : D =>
    (primitives (lanes δ) S.vp.params).PRFmsg k d.1 d.2)

include hp eq ok hs in
theorem native_real_prefix (M : Matrix Work Work ℂ) (pos : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun π => qPrfRealPr (msgPrf S.vp ((P₀) π)) (P (oracle π)) M) ≤
      uniformMean (fun π => uniformMean (fun σ => uniformMean (fun k =>
        qWeight (· = true) (pre (oracle π) >>= real_post S (programmed S k π σ) k) M))) + ((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ := by
  have post_eq (π : Permutation) (k : S.Node) :
      callPost (E:=E) (A:=Bool) (Q:=2^41) (oracle π) (roundValue S π π k) = real_post S π k := by
    apply congrArg (callPost (E:=E) (A:=Bool) (Q:=2^41) (oracle π))
    funext d
    exact (byte_prf S π k d.1 d.2 _ _ (split_blocks S k d.1 d.2)).symm
  have switched := MsgEffect.real_public_switch S pre hp (fun k π => real_post S π k) M pos one
  simp_rw [same_round S rand seeds F pre eq ok hs,post_eq]
  exact switched

def ideal_post (H : Port → Words) :
    FamilyStage Port Words E D S.Node Bool (2^41) → Closed Work Bool
  | .inl b => pure b
  | .inr (_,post) => liftU ($ᵗ S.Node) >>= fun r => post.val r H

include eq hs in
theorem native_ideal_prefix (π : Permutation) (M : Matrix Work Work ℂ) :
    qPrfIdealPr (P (oracle π)) M = qWeight (· = true) (pre (oracle π) >>= ideal_post S (oracle π)) M := by
  let H := oracle π
  change qWeight (· = true) (idealRun (P H) ∅) M = _
  rw [fresh (P H) (native_count S (extend (SkCost.table S N H)) F rand seeds H 1 hs),eq,bind_map_left]
  apply congrArg (fun a => qWeight (· = true) a M)
  exact bind_congr fun s => by rcases s with b|⟨d,post⟩ <;> rfl
end
end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.native_real_prefix
#print axioms Reduction.ShakePermutation.MsgCost.native_ideal_prefix
