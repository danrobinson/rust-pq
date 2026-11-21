import Integration.SlhDsaBridgeMach

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

namespace Reduction
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

elab "krfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.consumeMData.eq? | throwError "krfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

def cSign {M S Sb : Type} (encS : S → Sb) :
    QueryImpl (unifSpec + (M →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => encS <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

def cRead {M S Sb : Type} (decS : Sb → Option S) (fallback : S) (out : M × Sb) : M × S :=
  (out.1, (decS out.2).getD fallback)

def hashH (ω₀ : Ω128 c) (H : EncX c → EncY) : QueryImpl (publicHashSpec (primsΩ ω₀).core) Id
  | .thash pk a xs => if h : xs.length ≤ c.tl then (H (.inl (pk, a, BList.ofList xs h))).1 else default
  | .hmsg r pk root m => if h : m.length ≤ c.ml then (H (.inr (.inl (r, pk, root, BList.ofList m h)))).2 else default

noncomputable def qmForger (ω₀ : Ω128 c) (H : EncX c → EncY) (pk : PublicKeyCore (primsΩ ω₀).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
      wrap0 (Guarded.signingImpl pureEncode)
        (cRead (decodePureSig Link.vp (primsΩ ω₀) (codecR ω₀.toRand))
            (Except.error (External.Error.contextTooLong 0)) <$>
          wrap0 (cSign (encodePureSig Link.vp (primsΩ ω₀) (codecR ω₀.toRand)))
            (compileQ H (F.main (encodePublicKey (codecR ω₀.toRand) pk))))

set_option maxHeartbeats 400000 in
theorem tB (ω₀ : Ω128 c) (T) (n : ℕ) (s) (pk) :
    qmMach (optRandOf c optRand₀ { ω₀ with thash := T }) (PublicHash.impl (primsΩ { ω₀ with thash := T })) n
      (fun pk => qmForger c F ω₀ (encΩ { ω₀ with thash := T }) pk) s pk =
    qmMach (optRandOf c optRand₀ ω₀) (hashH c ω₀ (encΩ { ω₀ with thash := T })) n
      (qmForger c F ω₀ (encΩ { ω₀ with thash := T })) s pk := by
  have : PublicHash.impl (primsΩ { ω₀ with thash := T }) = hashH c ω₀ (encΩ { ω₀ with thash := T }) := by
    funext q; cases q <;> rfl
  rw [this]
  krfl

end Reduction
#print axioms Reduction.tB
