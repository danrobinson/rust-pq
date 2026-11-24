import Integration.SlhDsaShakePermutationHonestScheme
import Integration.SlhDsaShakeApiSkBridge

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum
open ShakeApi (Xof RawTable)
open Compression.SkGame (answerImpl ans_bind ans_classical ans_wrap answer_uniform)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives

abbrev RawSpec (S : Sha2Set) (N : ℕ) := PRFScheme.PRFOracleSpec (ShakeApi.Input N) (Bytes S.vp.params.m)
abbrev ByteMessage := List SLHDSA.Byte × List SLHDSA.Byte
abbrev ByteSig := Option (List SLHDSA.Byte)
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => ShakeApi.primitives S base

def readRaw (xs : List SLHDSA.Byte) : OracleComp (RawSpec S N) (Bytes S.vp.params.m) :=
  if h : xs.length ≤ N then liftM ((RawSpec S N).query (.inr (BList.ofList xs h))) else pure default

def rawHash : QueryImpl (hashSpec (P₀).core) (OracleComp (RawSpec S N))
  | .inl (.thash pk a xs) => prefixBytes _ <$> readRaw S N (pk.toList ++ a.toList ++ (xs.map Vector.toList).flatten)
  | .inl (.hmsg r pk root m) => readRaw S N (r.toList ++ pk.toList ++ root.toList ++ m)
  | .inr q => prefixBytes _ <$> readRaw S N (q.skPrf.toList ++ q.optRand.toList ++ q.msg)

def rawImpl : QueryImpl (unifSpec + hashSpec (P₀).core) (OracleComp (RawSpec S N)) :=
  (QueryImpl.ofLift unifSpec (OracleComp (RawSpec S N))) + rawHash S N base

@[simp] theorem runRead (H : RawTable S N) (xs : List SLHDSA.Byte) :
    simulateQ (answerImpl H) (readRaw S N xs) = pure (ShakeApi.extend H xs) := by
  by_cases h : xs.length ≤ N
  · simp only [readRaw,ShakeApi.extend,dite_eq_left h,simulateQ_spec_query,answerImpl]
  · simp [readRaw,ShakeApi.extend,h]

theorem impl_self (H : RawTable S N) : answerImpl H ∘ₛ rawImpl S N (ShakeApi.extend H) =
    unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S (ShakeApi.extend H))) := by
  funext t
  rcases t with n | (q | q)
  · simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inl,QueryImpl.ofLift_apply]
    exact simulateQ_spec_query _ _
  · cases q with
    | thash pk a xs =>
      simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inr,rawHash,simulateQ_map,runRead,map_pure]
      rfl
    | hmsg r pk root m => exact runRead S N H _
  · simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inr,rawHash,runRead,simulateQ_map,map_pure]
    rfl

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)

noncomputable def rawScheme : SignatureAlg (OracleComp (RawSpec S N)) ByteMessage (List SLHDSA.Byte) (List SLHDSA.Byte) ByteSig :=
  (pureBytesRomScheme S base (ShakeApi.signRand S rand base) seeds).map (simulateQ' (rawImpl S N base))

theorem runRaw_self (H : RawTable S N) :
    (rawScheme S N (ShakeApi.extend H) rand seeds).map (simulateQ' (answerImpl H)) =
      ShakeApi.scheme S rand seeds (ShakeApi.extend H) := by
  have h := pureBytesRomScheme_instantiation S (ShakeApi.extend H) (ShakeApi.signRand S rand _) seeds
  refine Eq.trans ?_ h
  apply SignatureAlg.ext
  · change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose,impl_self]
  · funext pk sk m
    change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose,impl_self]
  · funext pk m sig
    change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose,impl_self]

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] (F : PortForger X Y E)

noncomputable def signing (A : SignatureAlg (OracleComp (RawSpec S N)) ByteMessage (List SLHDSA.Byte)
    (List SLHDSA.Byte) ByteSig) (pk sk : List SLHDSA.Byte) :
    QueryImpl (unifSpec + (ByteMessage →ₒ ByteSig)) (StateT (QueryLog (ByteMessage →ₒ ByteSig)) (OracleComp (RawSpec S N))) :=
  fun t => match t with
    | .inl n => fun log => (fun u => (u,log)) <$> (liftM ((RawSpec S N).query (.inl n)) : OracleComp (RawSpec S N) _)
    | .inr m => fun log => (fun sig => (sig,log ++ [⟨m,sig⟩])) <$> A.sign pk sk m

noncomputable def joint (A : SignatureAlg (OracleComp (RawSpec S N)) ByteMessage (List SLHDSA.Byte)
    (List SLHDSA.Byte) ByteSig) (fresh : QueryLog (ByteMessage →ₒ ByteSig) → ByteMessage → ByteSig → Bool)
    (port : X → Y) : QOC (WS X Y E) (RawSpec S N) Bool := do
  let ks ← liftQ A.keygen
  let z ← wrap (signing S N A ks.1 ks.2) (compileQ port (F.main ks.1)) []
  let ok ← liftQ (A.verify ks.1 z.1.1 z.1.2)
  pure (fresh z.2 z.1.1 z.1.2 && ok)

/-- Interpreting the external hash component of the open experiment recovers the
literal byte-signature game, including invalid encodings and the signing log. -/
theorem runJoint (A : SignatureAlg (OracleComp (RawSpec S N)) ByteMessage (List SLHDSA.Byte)
    (List SLHDSA.Byte) ByteSig) (fresh : QueryLog (ByteMessage →ₒ ByteSig) → ByteMessage → ByteSig → Bool)
    (port : X → Y) (H : RawTable S N) :
    ansRun H (joint S N F A fresh port) =
      qSigExperiment fresh (F.at port (A.map (simulateQ' (answerImpl H)))) := by
  unfold joint qSigExperiment
  rw [ans_bind,ans_classical]
  apply bind_congr
  intro ks
  rw [ans_bind,ans_wrap]
  congr 1
  · congr 1
    funext t s
    rcases t with n|m
    · simp only [signing, StateT.run,simulateQ_map,simulateQ_spec_query, PQ.Interactive.signImpl,answerImpl]
      rfl
    · simp only [signing,StateT.run,simulateQ_map,PQ.Interactive.signImpl,SignatureAlg.map_sign]
      rfl
  · funext z
    rw [ans_bind,ans_classical]
    apply bind_congr
    intro ok
    exact ansRun_pure _ _

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.runRaw_self
#print axioms Reduction.ShakePermutation.Honest.runJoint
