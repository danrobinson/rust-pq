import Integration.SlhDsaShakeApiForger
import Integration.SlhDsaShakeApiSkCost

namespace Reduction.ShakeApi.Msg
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives

variable (S : Sha2Set) (N : ℕ) (base : Xof S) {E : Type} [Fintype E] [DecidableEq E]
local notation "P₀" => primitives S base
local notation "Work" => WS (Input N) (Bytes S.vp.params.m) E
local notation "PS" => PRFScheme.PRFOracleSpec (S.Node × List SLHDSA.Byte) S.Node
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)
local notation "Sig" => GeneralScheme.SignatureCore (Sha2Set.vp S) (Primitives.core (primitives S base))
local notation "SG" => unifSpec + (List SLHDSA.Byte →ₒ Sig)

def hashWeight (D : Type) : (Lazy.RSpec (Lazy.msgG P₀) D S.Node (publicHashSpec (P₀).core)).Domain → ℕ :=
  fun t => if Lazy.kind t = .hash then 1 else 0
local notation "Wc" => hashWeight S base SecIdx

private theorem liftDet {ι α : Type} {sp : OracleSpec ι} (cnt : (unifSpec + sp).Domain → ℕ)
    (hu : ∀ n, cnt (.inl n) = 0) (d : RawTable S N → α) {n : ℕ}
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
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

noncomputable def signImpl (pk : PublicKeyCore (P₀).core) :
    QueryImpl SG (StateT (SigLog S.vp P₀) (OracleComp OS)) :=
  (QueryImpl.ofLift unifSpec (OracleComp OS)).liftTarget (StateT (SigLog S.vp P₀) (OracleComp OS)) +
    sigSignOracle (Lazy.msgSignO (signRand S rand base) pk)

private theorem signCost (pk : PublicKeyCore (P₀).core) (t : (SG).Domain) (log : SigLog S.vp P₀) :
    WCount Wc ((signImpl S base rand pk t).run log) (sgnW (Lazy.signHashes S.vp) t) := by
  rcases t with n|m
  · exact WCount.map (wCount_liftM_query (sp := OS) Wc (.inl n) le_rfl) (fun x => (x,log))
  · simp only [signImpl,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
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

noncomputable def verdict (H : RawTable S N) (pk : PublicKeyCore (P₀).core)
    (z : (List SLHDSA.Byte × Sig) × SigLog S.vp P₀) : Bool :=
  simulateQ (hashPort S N base H) (sufCheckOpen pk z.1 z.2)

private theorem verdict_cost (pk : PublicKeyCore (P₀).core) (z : (List SLHDSA.Byte × Sig) × SigLog S.vp P₀) :
    EvalCostQ E Wc (fun H => (pure (verdict S N base H pk z) : OracleComp OS Bool)) (1 + Resources2.verifyHashes S.vp) := by
  apply liftDet S N Wc (fun _ => rfl)
  have hi (H : RawTable S N) : (fun t => pure (hashPort S N base H t) : QueryImpl _ ProbComp) =
      (hashPort S N base H).liftTarget ProbComp := by funext t; rfl
  have h := Sk.check_cost S N base pk z.1 z.2
  simp only [hi,simulateQ_liftTarget] at h
  kexact h

noncomputable def openMachine (H : RawTable S N) : QOC Work OS Bool := do
  let pk ← liftQ (liftM seeds : OracleComp OS S.Node)
  let root ← liftQ (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk)
  let z ← wrap (signImpl S base rand ⟨pk,root⟩) (qmForger S N F base H ⟨pk,root⟩) []
  pure (verdict S N base H ⟨pk,root⟩ z)

def budget (q qs : ℕ) := Lazy.keygenHashes S.vp + q + qs*Lazy.signHashes S.vp + (1+Resources2.verifyHashes S.vp)

theorem openMachine_cost (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE Wc (openMachine S N base rand seeds F) (budget S q qs) := by
  unfold openMachine
  have w (pk : PublicKeyCore (P₀).core) : PUE Wc (fun H =>
      wrap (signImpl S base rand pk) (qmForger S N F base H pk) [] >>= fun z =>
      pure (verdict S N base H pk z)) (q + qs*Lazy.signHashes S.vp + (1+Resources2.verifyHashes S.vp)) := by
    refine PUE.bind (PUE.wrap _ (signCost S base rand pk) (pue_qmForger S N F base q qs _ hq hs pk) []) fun z => ?_
    have ev := verdict_cost (E := E) S N base pk z
    have h := ev Bool (fun b _ => (pure b : QOC Work OS Bool)) 0 (fun b => PUE.pure b 0)
    simpa only [liftQ_pure,pure_bind,Nat.zero_add] using h
  have h0 : WCount Wc (liftM seeds : OracleComp OS _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) seeds)
  have hk (pk : S.Node) : WCount Wc (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk) (Lazy.keygenHashes S.vp) :=
    wCount_of_isQueryBoundP _ _ _ ((Lazy.openKeygen_kindBound (prims := P₀) (gspec := Lazy.msgG P₀) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp)))
  have h := PUE.liftQ_bind _ h0 fun pk => PUE.liftQ_bind _ (hk pk) fun root => w ⟨pk,root⟩
  exact h.mono (by unfold budget; omega)

noncomputable def machine (H : RawTable S N) : QOC Work PS Bool :=
  qLazyRun (hashPort S N base H) (openMachine S N base rand seeds F H)

theorem machine_cost (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ => 0) (machine S N base rand seeds F) (budget S q qs) := by
  unfold machine qLazyRun
  refine PUE.wrap0E (fun H => Lazy.interp (hashPort S N base H)) (cnt := hashWeight S base Unit) ?_
    (PUE.map _ (PUE.wrap _ (cnt := Wc) ?_ (openMachine_cost S N base rand seeds F q qs hq hs) []))
  · rintro (n|d|u|t)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact EvalCostQ.const _ (wCount_zero _ _)
    · exact liftDet S N _ (fun _ => rfl) _ (hash_cost S N base t)
  · intro t s
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n|d|a|h
    · simp [Lazy.lazyImplR,Lazy.kind]
    · simp [Lazy.lazyImplR,Lazy.kind]
    · rcases hc : s.lookup a with _|v
      · rw [Lazy.lazyImplR_sec_run_miss a s hc]; simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit a s v hc]; simp
    · simp [Lazy.lazyImplR,Lazy.kind,hashWeight]

end Reduction.ShakeApi.Msg
#print axioms Reduction.ShakeApi.Msg.machine_cost
