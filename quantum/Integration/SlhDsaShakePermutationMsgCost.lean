import Integration.SlhDsaShakePermutationMsgUniform
import Integration.SlhDsaShakePermutationSkBudget

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg ShakeApi
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable (S : Sha2Set) (N : ℕ) (base : Xof S) {E : Type} [Fintype E] [DecidableEq E]
local notation "P₀" => ShakeApi.primitives S base
local notation "Work" => WS Port Words E
local notation "PS" => PRFScheme.PRFOracleSpec (S.Node × List SLHDSA.Byte) S.Node
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)
local notation "Sig" => GeneralScheme.SignatureCore (Sha2Set.vp S) (Primitives.core (ShakeApi.primitives S base))
local notation "SG" => unifSpec + (List SLHDSA.Byte →ₒ Sig)

def hashWeight (D : Type) : (Lazy.RSpec (Lazy.msgG P₀) D S.Node (publicHashSpec (P₀).core)).Domain → ℕ :=
  fun t => if Lazy.kind t = .hash then 1 else 0
local notation "Wc" => hashWeight S base SecIdx

private theorem liftDet {ι α : Type} {sp : OracleSpec ι} (cnt : (unifSpec + sp).Domain → ℕ)
    (hu : ∀ n, cnt (.inl n) = 0) (d : (Port → Words) → α) {n : ℕ}
    (h : EvalCost (fun H => (pure (d H) : ProbComp α)) n) :
    EvalCostQ E cnt (fun H => (pure (d H) : OracleComp (unifSpec + sp) α)) n := by
  have hc := h E α (fun a _ => (pure a : Closed Work α)) 0 (fun a => PUE.pure a 0)
  simp only [liftU_pure,pure_bind,Nat.zero_add] at hc
  let emb : QueryImpl unifSpec (OracleComp (unifSpec + sp)) := fun i => liftM ((unifSpec + sp).query (.inl i))
  have ho := PUE.wrap0 (cnt' := cnt) emb (fun t => wCount_liftM_query _ _ (le_of_eq (hu t))) hc
  simp only [wrap0_pure] at ho
  intro β B q hB
  simpa only [liftQ_pure,pure_bind,Nat.add_comm n q] using PUE.bind ho hB

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger Port Words E)

private theorem signCost (pk : PublicKeyCore (P₀).core) (t : (SG).Domain) (log : SigLog S.vp P₀) :
    WCount Wc ((ShakeApi.Msg.signImpl S base rand pk t).run log) (sgnW (Lazy.signHashes S.vp) t) := by
  rcases t with n|m
  · exact WCount.map (wCount_liftM_query (sp := OS) Wc (.inl n) le_rfl) (fun x => (x,log))
  · simp only [ShakeApi.Msg.signImpl,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    have sample : WCount Wc (liftM (signRand S rand base pk) : OracleComp OS _) 0 :=
      wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) _)
    have h := WCount.bind sample (fun r =>
      WCount.bind (wCount_liftM_query (sp := OS) Wc (.inr (.inl (r,m))) le_rfl) (fun R =>
        wCount_of_isQueryBoundP (fun t => Lazy.kind t = .hash) _ (Lazy.signHashes S.vp)
          ((Lazy.openSign_kindBound (prims := P₀) (gspec := Lazy.msgG P₀) .hash m pk.pkSeed pk.pkRoot R).mono
            (by simpa [Lazy.ind] using Lazy.signB_hash (vp := S.vp)))))
    have h' : WCount Wc (Lazy.msgSignO (signRand S rand base) pk m) (Lazy.signHashes S.vp) := by
      simpa only [Lazy.msgSignO,Lazy.gameQ,Nat.zero_add] using h
    exact (WCount.bind h' (m := 0) (fun sig => wCount_pure Wc (sig,log ++ [⟨m,sig⟩]) 0)).mono (Nat.le_of_eq (Nat.add_zero _))


private theorem scale {I A : Type} {sp : OracleSpec I} (w : I → ℕ) (p : OracleComp sp A)
    (a : ℕ) (hc : WCount w p a) : WCount (fun i => 483*w i) p (483*a) := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure x => trivial
  | query_bind t f ih =>
    rw [wCount_query_bind] at hc ⊢
    exact ⟨Nat.mul_le_mul_left 483 hc.1,fun u => by simpa only [Nat.mul_sub] using ih u (a-w t) (hc.2 u)⟩

local notation "Wb" => fun i => 483 * Wc i
variable (cap : N ≤ ShakeApi.rawCap S 67 65536)
include cap in
private theorem verdict_cost (pk : PublicKeyCore (P₀).core) (z : (List SLHDSA.Byte × Sig) × SigLog S.vp P₀) :
    EvalCostQ E Wb (fun H => (pure (ShakeApi.Msg.verdict S N base (SkCost.table S N H) pk z) : OracleComp OS Bool)) (483*(1 + Resources2.verifyHashes S.vp)) := by
  apply liftDet (E:=E) Wb (fun _ => rfl)
  have hi (H : Port → Words) : (fun t => pure (hashPort S N base (SkCost.table S N H) t) : QueryImpl _ ProbComp) =
      (hashPort S N base (SkCost.table S N H)).liftTarget ProbComp := by funext t; rfl
  have h := SkCost.check_cost S N base pk z.1 z.2 cap
  simp only [hi,simulateQ_liftTarget] at h
  kexact h

noncomputable def openMachine (H : Port → Words) : QOC Work OS Bool := do
  let pk ← liftQ (liftM seeds : OracleComp OS S.Node)
  let root ← liftQ (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk)
  let z ← wrap (ShakeApi.Msg.signImpl S base rand ⟨pk,root⟩) (SkCost.qmForger S F base H ⟨pk,root⟩) []
  pure (ShakeApi.Msg.verdict S N base (SkCost.table S N H) ⟨pk,root⟩ z)

def budget (q qs : ℕ) := 483*Lazy.keygenHashes S.vp + q + qs*(483*Lazy.signHashes S.vp) + (483*(1+Resources2.verifyHashes S.vp))

include cap in
theorem openMachine_cost (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE Wb (openMachine S N base rand seeds F) (budget S q qs) := by
  unfold openMachine
  have w (pk : PublicKeyCore (P₀).core) : PUE Wb (fun H =>
      wrap (ShakeApi.Msg.signImpl S base rand pk) (SkCost.qmForger S F base H pk) [] >>= fun z =>
      pure (ShakeApi.Msg.verdict S N base (SkCost.table S N H) pk z)) (q + qs*(483*Lazy.signHashes S.vp) + (483*(1+Resources2.verifyHashes S.vp))) := by
    refine PUE.bind (PUE.wrap (ShakeApi.Msg.signImpl S base rand pk) (cnt' := Wb) (fun t l => by
      have b := scale Wc _ _ (signCost S base rand pk t l)
      rcases t with n|m
      · simpa [sgnW] using b
      · exact b) (SkCost.pue_qmForger S F base q qs (483*Lazy.signHashes S.vp) hq hs pk) []) fun z => ?_
    have ev := verdict_cost (E := E) S N base cap pk z
    have h := ev Bool (fun b _ => (pure b : QOC Work OS Bool)) 0 (fun b => PUE.pure b 0)
    simpa only [liftQ_pure,pure_bind,Nat.zero_add] using h
  have h0 : WCount Wc (liftM seeds : OracleComp OS _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) seeds)
  have hk (pk : S.Node) : WCount Wc (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk) (Lazy.keygenHashes S.vp) :=
    wCount_of_isQueryBoundP _ _ _ ((Lazy.openKeygen_kindBound (prims := P₀) (gspec := Lazy.msgG P₀) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp)))
  have h := PUE.liftQ_bind _ (scale Wc _ _ h0) fun pk => PUE.liftQ_bind _ (scale Wc _ _ (hk pk)) fun root => w ⟨pk,root⟩
  exact h.mono (by unfold budget; omega)

noncomputable def machine (H : Port → Words) : QOC Work PS Bool :=
  qLazyRun (hashPort S N base (SkCost.table S N H)) (openMachine S N base rand seeds F H)

include cap in
theorem machine_cost (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ => 0) (machine S N base rand seeds F) (budget S q qs) := by
  unfold machine qLazyRun
  refine PUE.wrap0E (fun H => Lazy.interp (hashPort S N base (SkCost.table S N H))) (cnt := fun i => 483*hashWeight S base Unit i) ?_
    (PUE.map _ (PUE.wrap _ (cnt := Wb) ?_ (openMachine_cost S N base rand seeds F cap q qs hq hs) []))
  · rintro (n|d|u|t)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact liftDet _ (fun _ => rfl) _ (SkCost.hash_cost S N base cap t)
  · intro t s
    apply scale (hashWeight S base Unit)
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n|d|a|h
    · simp [Lazy.lazyImplR,Lazy.kind]
    · simp [Lazy.lazyImplR,Lazy.kind]
    · rcases hc : s.lookup a with _|v
      · rw [Lazy.lazyImplR_sec_run_miss a s hc]; simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit a s v hc]; simp
    · simp [Lazy.lazyImplR,Lazy.kind,hashWeight]


end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.machine_cost
