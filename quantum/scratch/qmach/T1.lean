import Integration.SlhDsaBridgePrf
import Reduction.Open.Tcr
import PQ.Interactive.QromBridgeEvalProg

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

namespace Reduction
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

elab "krfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "krfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

def withThash (ω₀ : Ω128 c) (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl → Bytes Link.vp.params.n) : Ω128 c :=
  { ω₀ with thash := T }

def hashH (ω₀ : Ω128 c) (H : EncX c → EncY) : QueryImpl (publicHashSpec (primsΩ ω₀).core) Id
  | .thash pk a xs => if h : xs.length ≤ c.tl then (H (.inl (pk, a, BList.ofList xs h))).1 else default
  | .hmsg r pk root m => if h : m.length ≤ c.ml then (H (.inr (.inl (r, pk, root, BList.ofList m h)))).2 else default

def cSign {M S Sb : Type} (encS : S → Sb) :
    QueryImpl (unifSpec + (M →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => encS <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

def cRead {M S Sb : Type} (decS : Sb → Option S) (fallback : S) (out : M × Sb) : M × S :=
  (out.1, (decS out.2).getD fallback)

theorem cSign_eq {M PK SK S PKb SKb Sb : Type} {alg : SignatureAlg ProbComp M PK SK S}
    {balg : SignatureAlg ProbComp M PKb SKb Sb} (v : Coded.View alg balg) :
    Coded.signingImpl v = cSign v.encS := by
  funext t; rcases t with t | t <;> rfl

theorem cRead_eq {M PK SK S PKb SKb Sb : Type} {alg : SignatureAlg ProbComp M PK SK S}
    {balg : SignatureAlg ProbComp M PKb SKb Sb} (v : Coded.View alg balg) :
    Coded.readForgery v = cRead v.decS := rfl

theorem t1 (ω₀ : Ω128 c) (T) (pk) :
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F (withThash c ω₀ T)).main pk =
    (intF c optRand₀ pkSeedDist₀ F ω₀ (encΩ (withThash c ω₀ T))).main pk := by
  simp only [intF, internalΩ, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger, PortForger.at, cSign_eq, cRead_eq, pureBytesView]
  trace_state
  rfl

example (ω : Ω128 c) : primsΩ ω = PublicHash.withPublicHash (primsΩ ω).core (hashH c ω (encΩ ω)) := rfl

end Reduction
#print axioms Reduction.t1
