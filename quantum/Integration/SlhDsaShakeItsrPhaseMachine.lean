import Integration.SlhDsaShakeAdaptiveRows
import Integration.SlhDsaShakeXofSkOpenCost

namespace Reduction.ShakeAdaptive.Phase
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg QItsr
open scoped ENNReal Kronecker
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeApi.primitives ShakeSecurity.primitives

variable (S : Sha2Set) (N : ℕ) (base : ShakeApi.Xof S)
local notation "P" => ShakeApi.primitives S base
local notation "Game" => Lazy.itsrG P

/-- Interpret honest hash calls locally with the table selected by the list of
responses already issued. A target is forwarded before its response is recorded. -/
noncomputable def handler (honest : List S.Node → ShakeApi.RawTable S N) :
    QueryImpl (Lazy.RSpec Game Unit (P).Y (publicHashSpec (P).core))
      (StateT (List S.Node) (OracleComp (unifSpec + Game))) :=
  fun t hist => match t with
  | .inr (.inl req) => (fun (r : S.Node) => (r,hist ++ [r])) <$> liftM ((unifSpec + Game).query (.inr req))
  | t => (fun x => (x,hist)) <$> Lazy.interp (gspec := Game) (V := (P).Y)
      (ShakeApi.hashPort S N base (honest hist)) t

variable {E : Type} [Fintype E] [DecidableEq E]
  (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "Work" => WS (ShakeApi.Input N) (Bytes S.vp.params.m) E

/-- The ITSR reduction with a separate local honest evaluator. Only the
adversary's coherent queries access the runtime public port. -/
noncomputable def machine (honest : List S.Node → ShakeApi.RawTable S N) (H : ShakeApi.RawTable S N) :
    QOC Work (unifSpec + Game) (ShakeSingle.Query S) :=
  Prod.fst <$> wrap (handler S N base honest) (Prod.fst <$> wrap Lazy.lazyImplR
    (qmItsrOpen (ShakeApi.signRand S rand base) seeds (ShakeApi.qmForger S N F base H)) []) []

theorem public_cost (honest : List S.Node → ShakeApi.RawTable S N) (q : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) :
    PU (machine S N base rand seeds F honest) q := by
  unfold machine
  apply PU.map
  apply PU.wrap
  apply PU.map
  apply PU.wrap
  unfold qmItsrOpen
  apply PU.liftQ_bind
  intro pk
  apply PU.liftQ_bind
  intro root
  rw [← Nat.add_zero q]
  apply PU.bind (PU.wrap _
    (ShakeApi.Sk.Mixed.forger_public S N base F _ q hq) [])

  intro z
  exact PU.liftQ (E := E) _ 0

/-- Erasing the record of issued responses gives the original lazy interpreter
when the honest table is fixed. This equality holds for every initial history. -/
theorem wrap_constant {α : Type} (honest : ShakeApi.RawTable S N)
    (X : QOC Work (Lazy.RSpec Game Unit (P).Y (publicHashSpec (P).core)) α) (hist : List S.Node) :
    Prod.fst <$> wrap (handler S N base (fun _ => honest)) X hist =
      wrap0 (Lazy.interp (ShakeApi.hashPort S N base honest)) X := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure => simp
  | query_bind t k ih =>
    cases t with
    | inl j => simp only [wrap_instr_bind,wrap0_instr_bind,map_bind,ih]
    | inr t =>
      rw [wrap_query_bind,wrap0_query_bind,map_bind]
      simp only [ih]
      rcases t with n | req | d | h <;>
        simp only [handler,StateT.run,liftQ,simulateQ_map,bind_map_left,Lazy.interp]
      rfl

/-- Reuniting the honest and coherent tables recovers the signature reduction
itself, including its target queries and returned forgery. -/
theorem represented (H : ShakeApi.RawTable S N) :
    machine S N base rand seeds F (fun _ => H) H =
      qbItsrL (qPureBytesToInternal (ShakeApi.rawForger S N rand seeds F H)) := by
  unfold machine
  rw [wrap_constant]
  exact ShakeApi.itsrMach_oracle S N rand seeds F base H

/-- Tracking salt responses and evaluating local hashes introduces no new
target requests, independently of which honest table the transcript selects. -/
theorem target_cost (honest : List S.Node → ShakeApi.RawTable S N) (s : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : ShakeApi.RawTable S N) :
    CountBound (QC Work isR) (machine S N base rand seeds F honest H) s := by
  let A : QForger Work (internalAlg S.vp P (ShakeApi.signRand S rand base) seeds) :=
    ⟨ShakeApi.qmForger S N F base H,F.ρ₀,F.posSemidef,F.trace_eq_one⟩
  have openCost := cb_qItsrOpen P A (n := s) (fun pk => by
    apply (countBound_iff_wCount _ _ _).2
    have h := ShakeApi.Sk.Mixed.forger_signs S N base F pk 1 s hs H
    rw [Nat.mul_one] at h
    convert h using 2
    rename_i t
    rcases t with j|n|m <;> simp [qw,sgnW,QC,isR])
  unfold machine
  refine cb_map _ (cb_wrap (c := isG) _ ?_ (cb_map _ (cb_wrap (c := isG) _ ?_ openCost [])) [])
  · rintro (m | req | d | h) hist
    · exact cb_map _ (cb_query (c := isR) (Sum.inl m))
    · exact cb_map _ (cb_query (c := isR) (Sum.inr req))
    · exact cb_map _ (cb_of_allQ (allQ_liftProb (G := fun t ↦ ¬ isR t) (fun n ↦ by simp [isR]) _) _)
    · exact cb_map _ (cb_mono (n := 0) (by simp [isG]) trivial)
  · rintro (m | req | d | h) cache
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inl m))
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inl req)))
    · simp only [Lazy.lazyImplR, StateT.run_bind, StateT.run_get, pure_bind]
      cases List.lookup d cache with
      | some v => exact cb_mono (n := 0) (by simp [isG]) trivial
      | none =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        refine cb_mono (n := 0) (by simp [isG])
          (cb_bind_pure (g := fun p : S.Node × List (SecIdx × S.Node) ↦ (p.1, (d, p.1) :: cache)) ?_)
        exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inr (Sum.inl ()))))
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inr (Sum.inr h))))

variable (c : Caps) {s : ℕ} (cap : 3*S.vp.params.n+c.ml ≤ N) (g : ShakeApi.RawTable S N)

/-- Complete a response prefix by defaults. The table only inspects the prefix. -/
noncomputable def historyTable (Ψ : Row S c × Option (Fin s) → Bytes S.vp.params.m)
    (hist : List S.Node) : ShakeApi.RawTable S N :=
  ShakeXof.write (embedding S c cap) g (nFn (fun j => hist[j.val]?.getD default) Ψ hist.length)

/-- The honest evaluator computed from past target responses gives the current
phase table, for every salt tape consistent with those responses. -/
theorem historyTable_eq (Ψ : Row S c × Option (Fin s) → Bytes S.vp.params.m)
    (hist : List S.Node) (Rs : Fin s → S.Node)
    (past : ∀ (j : Fin s), j.val < hist.length → hist[j.val]?.getD default = Rs j) :
    historyTable S N c cap g Ψ hist =
      ShakeXof.write (embedding S c cap) g (nFn Rs Ψ hist.length) := by
  unfold historyTable
  congr 1
  funext z
  unfold nFn lastIdx
  have eq : lastSet (fun j : Fin s => hist[j.val]?.getD default) hist.length z.1 =
      lastSet Rs hist.length z.1 := by
    ext j
    simp only [lastSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right (fun h => by rw [past j h])
  simp only [eq]

/-- Compile the response-driven evaluator into a salt-tape-independent interactive
adversary. Its public query budget and target-request budget are those of the
original forger, even with a different local honest table after every reply. -/
theorem interactive (honest : List S.Node → ShakeApi.RawTable S N) (q s : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s) :
    ∃ x : IA (ShakeApi.Input N) (Bytes S.vp.params.m) E (ItsrIn P) S.Node
        (Option (ShakeSingle.Query S)) s (progReg (ShakeApi.Input N) (Bytes S.vp.params.m) E),
      IAdv.IsQueryBound s x (fun _ => q) ∧
      ∀ (St : Type) (ch : ItsrIn P → St → S.Node × St) (st : St)
        (Ev : Option (ShakeSingle.Query S) × St → Prop) [DecidablePred Ev]
        (H : ShakeApi.RawTable S N) (ρ : SubState ((ShakeApi.Input N × Bytes S.vp.params.m) × E)),
        qprob LocalSig.Interp.instruments H (iflat ch s st x) ρ (fun p => Ev p.2) =
          qWeight (fun z => Ev (some z.1,z.2)) (close (detImpl ch)
            (machine S N base rand seeds F honest H) st) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  have cert := PUE.map (some : ShakeSingle.Query S → Option (ShakeSingle.Query S))
    (public_cost S N base rand seeds F honest q hq).toPUE
  obtain ⟨x,hx,eq⟩ := PUE.exists_iadv_qprob (Req := ItsrIn P) (Resp := S.Node) cert s
  refine ⟨x,hx,?_⟩
  intro St ch st Ev _ H ρ
  have cost := target_cost S N base rand seeds F honest s hs H
  have cg : CountBound (isGameQ (Req := ItsrIn P) (Resp := S.Node)) (machine S N base rand seeds F honest H) s :=
    cb_congr (fun t ↦ by rcases t with _|_|_ <;> simp [QC,isR,isGameQ]) cost
  have out := eq St ch st Ev H ρ (cb_map some cg)
  rwa [close_map_out,qWeight_map] at out

end Reduction.ShakeAdaptive.Phase
#print axioms Reduction.ShakeAdaptive.Phase.public_cost
#print axioms Reduction.ShakeAdaptive.Phase.historyTable_eq

#print axioms Reduction.ShakeAdaptive.Phase.represented
#print axioms Reduction.ShakeAdaptive.Phase.interactive
