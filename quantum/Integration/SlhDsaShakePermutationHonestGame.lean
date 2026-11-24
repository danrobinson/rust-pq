import Integration.SlhDsaShakePermutationHonestCap

namespace Reduction.ShakePermutation.Honest
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg QItsr
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (fixed base : Xof S) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype E] [DecidableEq E] (F : PortForger X Y E)
variable (fresh : QueryLog (ByteMessage →ₒ ByteSig) → ByteMessage → ByteSig → Bool)

theorem runJoint_full (c : Caps) (cap : ShakeApi.rawCap S 67 c.ml ≤ N)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (port : X → Y) :
    ansRun (ShakeApi.restrict S N base)
      (joint S N F (rawScheme S N fixed rand seeds) fresh port) =
      qSigExperiment fresh (ShakeApi.forgerAt S rand seeds F base port) := by
  rw [rawScheme_independent S N base fixed,runJoint]
  obtain ⟨key,sign,verify⟩ := run_cap S base c.ml rand seeds N cap
  unfold qSigExperiment
  simp only [key]
  apply bind_congr
  intro ks
  refine Compression.close_congr_on _ _ (G := Gbyte c.ml) (ok := capOut c) ?_ _ _ ?_
    (compileQ port (F.main ks.1)) ?_ []
  · rintro (n|m) hm
    · rfl
    · funext s
      simp only [PQ.Interactive.signImpl,sign ks.1 ks.2 m hm]
  · intro z hz
    rw [verify ks.1 z.1.1 z.1.2 hz]
  · exact allQ_and (allQ_compileQ c port (F.main _) (hc _)) (allQ_out_simulateQ (compileImplQ port) (hc _))

private theorem scheme_permutation (p : Spec.Keccak.State → Spec.Keccak.State) :
    ShakeApi.scheme S rand seeds (answer S p) =
    pureBytesAlg S.vp (primitives p S.vp.params) (codec p S.vp.params) (fun pk => rand pk.pkSeed pk.pkRoot) seeds := by
  have h := primitives_as_xof S p
  unfold ShakeApi.primitives ShakeApi.bundle ShakeSecurity.primitives primitives at h
  simp only [Primitives.mk.injEq,CorePrimitives.mk.injEq,heq_eq_eq,true_and,and_true] at h
  obtain ⟨⟨pr,pm⟩,th,hm⟩ := h
  unfold ShakeApi.scheme ShakeApi.codec ShakeApi.primitives ShakeApi.bundle ShakeSecurity.primitives
  rw [pr,pm,th,hm]
  rfl

theorem runJoint_permutation (F : PortForger Port Words E) (c : Caps)
    (cap : ShakeApi.rawCap S 67 c.ml ≤ N) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (π : Permutation) :
    ansRun (ShakeApi.restrict S N (answer S (lanes π)))
      (joint S N F (rawScheme S N fixed rand seeds) fresh (oracle π)) =
      qSigExperiment fresh (experiment S rand seeds F π) := by
  rw [runJoint_full S N fixed _ rand seeds F fresh c cap hc]
  unfold ShakeApi.forgerAt
  rw [scheme_permutation]

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.runJoint_permutation
