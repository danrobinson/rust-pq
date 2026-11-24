import Integration.SlhDsaCompressionClassicalProgram

namespace Reduction.Compression.ClassicalPort
open MLink Ideal SLHDSA PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec ENNReal Matrix
open MIdeal.PureCompression Classical
open scoped ComplexOrder Kronecker
set_option maxRecDepth 8000
abbrev Sig := unifSpec + Sign
abbrev Tagged := Reads Input Output Sig
abbrev W := Reg Input Output
abbrev Return := (List Byte × List Byte) × Option (List Byte)

def route : QueryImpl Ports (OracleComp Tagged)
  | .inl n => Tagged.query (.inr (.inl n))
  | .inr (.inl u) => (fun y : Output => (arrayVectorEquivFin UInt64 8).symm y.2) <$> Tagged.query (.inl (.inr u))
  | .inr (.inr (.inl u)) => Prod.fst <$> Tagged.query (.inl (.inl u))
  | .inr (.inr (.inr m)) => Tagged.query (.inr (.inr m))

theorem fixed_route {α : Type} (P : OracleComp Ports α) (g : CompressionTables) :
    simulateQ (answers (oracle g)) (simulateQ route P) =
      simulateQ (instImpl g.1) (simulateQ (instImpl g.2) P) := by
  induction P using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i f ih =>
    rcases i with n|u|u|m <;>
      simp only [simulateQ_bind,simulateQ_spec_query,route,answers,instImpl,simulateQ_map,
        simulateQ_pure,map_pure,pure_bind,oracle,Equiv.symm_apply_apply,ih]

def initial : W := ((default,0),())

noncomputable def asPort (A : MIdeal.PureCompression.Forger) : PortForger Input Output Unit where
  main pk := simulateQ translate (simulateQ route (A.main pk))
  ρ₀ := (SubState.basis (initial,())).matrix
  posSemidef := (SubState.basis (initial,())).posSemidef
  trace_eq_one := by simp [SubState.matrix_basis]

def publicCount : Ports.Domain → Bool
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | _ => false

def signCount : Ports.Domain → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

def capped (c : Caps) : Ports.Domain → Prop
  | .inr (.inr (.inr m)) => m.1.length + m.2.length + 2 ≤ c.ml
  | _ => True

private theorem count_route {α : Type} (ports : Bool) (P : OracleComp Ports α) (q : ℕ)
    (hp : CountBound (fun i => (if ports then publicCount i else signCount i) = true) P q) :
    CountBound (fun i => countClass (X := Input) (Y := Output) (sp := Sig) ports
      (fun j => !ports && j.isRight) i = true) (simulateQ route P) q := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure x => exact trivial
  | query_bind i f ih =>
    rw [countBound_query_bind] at hp
    cases ports <;> rcases i with n|u|u|m <;>
      simp only [simulateQ_bind,simulateQ_spec_query,route,bind_map_left,countBound_query_bind,
        countClass,publicCount,signCount,Bool.not_true,Bool.not_false,Bool.true_and,Bool.false_and,
        Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,↓reduceIte] at hp ⊢ <;>
      first | exact fun v => ih _ _ (hp _) | exact ⟨hp.1,fun v => ih _ _ (hp.2 _)⟩

theorem cap_forger (A : MIdeal.PureCompression.Forger) (c : Caps) (h : ∀ pk, AllQueries (capped c) (capOut c) (A.main pk)) (pk) :
    AllQueries (capIdx c) (capOut c) ((asPort A).main pk) := by
  let ok : Sig.Domain → Prop
    | .inl _ => True
    | .inr m => m.1.length + m.2.length + 2 ≤ c.ml
  have hroute : AllQueries (fun i : Tagged.Domain => match i with | .inl _ => True | .inr j => ok j)
      (capOut c) (simulateQ route (A.main pk)) := by
    apply QMsg.allQ_simulateQ _ _ (h pk)
    rintro (n|u|u|m) hi
    · exact QMsg.allQ_query _ _ trivial
    · exact QMsg.allQ_map _ (fun _ _ => trivial) (QMsg.allQ_query _ _ trivial)
    · exact QMsg.allQ_map _ (fun _ _ => trivial) (QMsg.allQ_query _ _ trivial)
    · exact QMsg.allQ_query _ _ hi
  have perm := program_cap (X := Input) (Y := Output) (sp := Sig) ok (capOut c) (simulateQ route (A.main pk))
  apply QMsg.allQ_mono _ (fun _ h => h) (perm (QMsg.allQ_mono (fun i hi => by cases i <;> exact hi) (fun _ h => h) hroute))
  rintro (j|u|n|m) hi <;> exact hi

private theorem count_congr {ι α : Type} {spec : OracleSpec ι} {p p' : ι → Prop}
    [d : DecidablePred p] [d' : DecidablePred p'] (e : p = p') (P : OracleComp spec α) (q : ℕ)
    (h : CountBound p P q) : CountBound p' P q := by
  subst p'; cases Subsingleton.elim d d'; exact h

theorem count_forger (A : MIdeal.PureCompression.Forger) (q qs : ℕ)
    (hp : ∀ pk, CountBound (fun i => publicCount i = true) (A.main pk) q)
    (hs : ∀ pk, CountBound (fun i => signCount i = true) (A.main pk) qs) :
    (∀ pk, CountBound isPort ((asPort A).main pk) q) ∧
      (∀ pk, CountBound isSign ((asPort A).main pk) qs) := by
  constructor
  · intro pk
    have e : (fun i => countPort (X := Input) (Y := Output) (sp := Sig) true
      (fun j => !true && j.isRight) i = true) = isPort := by
      funext i; rcases i with j|u|n|m <;> simp [isPort,countPort]
    apply count_congr e
    exact program_count true _ _ q (count_route true _ q (hp pk))
  · intro pk
    have e : (fun i => countPort (X := Input) (Y := Output) (sp := Sig) false
      (fun j => !false && j.isRight) i = true) = isSign := by
      funext i; rcases i with j|u|n|m <;> simp [isSign,countPort]
    apply count_congr e
    exact program_count false _ _ qs (count_route false _ qs (hs pk))

end Reduction.Compression.ClassicalPort
#print axioms Reduction.Compression.ClassicalPort.fixed_route
#print axioms Reduction.Compression.ClassicalPort.count_forger
#print axioms Reduction.Compression.ClassicalPort.cap_forger
