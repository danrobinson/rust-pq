/-
Work package OPEN (R1), part 1: the hash interface `HSpec prims` of the open reduction
adversaries and the generic machinery around it.

* `HSpec prims = publicHashSpec prims.core + ((SkPrf × Y × List Byte) →ₒ Y)`: `Thash`, `H_msg`
  and `PRF_msg` as oracles; `HSpec.impl prims` evaluates them by `prims`.
* `PSpec prims D = unifSpec + ((D →ₒ prims.Y) + HSpec prims)`: interface of an open PRF
  distinguisher with function-oracle domain `D`.
* `HKind`, `hkind`: the kind (`unif`/`game`/`hash`/`prfmsg`) of a query index of `PSpec`.
* `closeImpl prims D`: forward uniform bits and the function oracle, answer `HSpec` by
  `HSpec.impl prims`.
* `restrictO r`: the open counterpart of `Restrict.restrictImpl r` (hash queries forwarded);
  `close_restrictO`: closing commutes with restricting; `restrictO_kindBound`: restricting does
  not increase any per-kind count.
* `hashEmb`: run a program over `publicHashSpec prims.core` inside `PSpec` (every hash evaluation
  one `hash`-kind query); `close_hashEmb`, `hashEmb_kindBound`.
-/
import Reduction.SufPrfV2
import Reduction.Lazy.Open

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The hash interface: the public hash collection (`Thash`, `H_msg`) and `PRF_msg`
(`(SK.prf, opt_rand, M) ↦ R`). -/
abbrev HSpec {p : Params} (prims : Primitives p) :=
  publicHashSpec prims.core + ((prims.SkPrf × prims.Y × List Byte) →ₒ prims.Y)

/-- Evaluation of the hash interface by the functions of `prims`. -/
def HSpec.impl {p : Params} (prims : Primitives p) : QueryImpl (HSpec prims) Id
  | .inl q => PublicHash.impl prims q
  | .inr t => prims.PRFmsg t.1 t.2.1 t.2.2

/-- Interface of an open PRF distinguisher: uniform bits, the function oracle `D →ₒ prims.Y` of
the PRF game, and the hash interface. -/
abbrev PSpec {p : Params} (prims : Primitives p) (D : Type) :=
  unifSpec + ((D →ₒ prims.Y) + HSpec prims)

/-- The kinds of query of an open PRF distinguisher. -/
inductive HKind
  | unif | game | hash | prfmsg
deriving DecidableEq, Repr

/-- The kind of a query index of `PSpec prims D`. -/
def hkind {D P M : Type} : ℕ ⊕ (D ⊕ (P ⊕ M)) → HKind
  | .inl _ => .unif
  | .inr (.inl _) => .game
  | .inr (.inr (.inl _)) => .hash
  | .inr (.inr (.inr _)) => .prfmsg

/-- `1` if the kinds coincide, `0` otherwise. -/
def hind (K K' : HKind) : ℕ := if K = K' then 1 else 0

variable {p : Params} {prims : Primitives p} {D D' : Type}

/-- A function-oracle query of an open program. -/
def gameQ (prims : Primitives p) (d : D) : OracleComp (PSpec prims D) prims.Y :=
  (liftM ((PSpec prims D).query (.inr (.inl d))) : OracleComp (PSpec prims D) _)

/-- A `PRF_msg` query of an open program. -/
def prfMsgQ (prims : Primitives p) (D : Type) (skPrf : prims.SkPrf) (addrnd : prims.Y)
    (m : List Byte) : OracleComp (PSpec prims D) prims.Y :=
  (liftM ((PSpec prims D).query (.inr (.inr (.inr (skPrf, addrnd, m))))) :
    OracleComp (PSpec prims D) _)

/-- A public-hash evaluation, as an explicit query of the open program. -/
@[reducible] def openQ (prims : Primitives p) (D : Type) :
    HasQuery (publicHashSpec prims.core) (OracleComp (PSpec prims D)) :=
  ⟨fun q => (liftM ((PSpec prims D).query (.inr (.inr (.inl q)))) :
    OracleComp (PSpec prims D) _)⟩

/-- Run a program over the public hash collection inside `PSpec`: each of its queries is one
hash query. -/
def hashEmb (prims : Primitives p) (D : Type) :
    QueryImpl (publicHashSpec prims.core) (OracleComp (PSpec prims D)) :=
  fun q => (liftM ((PSpec prims D).query (.inr (.inr (.inl q)))) : OracleComp (PSpec prims D) _)

/-- Forward uniform bits and the function oracle; answer the hash interface by
`HSpec.impl prims`. -/
def closeImpl (prims : Primitives p) (D : Type) :
    QueryImpl (PSpec prims D) (OracleComp (unifSpec + (D →ₒ prims.Y)))
  | .inl n => (liftM (liftM (unifSpec.query n) : ProbComp _) :
      OracleComp (unifSpec + (D →ₒ prims.Y)) _)
  | .inr (.inl d) => (PRFScheme.functionQuery d : OracleComp (PRFScheme.PRFOracleSpec D prims.Y) _)
  | .inr (.inr q) => pure (HSpec.impl prims q)

/-- The open counterpart of `Restrict.restrictImpl r`: uniform bits and hash queries are
forwarded, a function query at `d` is forwarded to `d'` when `r d = some d'` and answered
`default` without a query otherwise. -/
def restrictO [Inhabited prims.Y] (r : D → Option D') :
    QueryImpl (PSpec prims D) (OracleComp (PSpec prims D'))
  | .inl n => (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (PSpec prims D') _)
  | .inr (.inl d) =>
    match r d with
    | some d' => gameQ prims d'
    | none => pure (default : prims.Y)
  | .inr (.inr q) => (liftM ((PSpec prims D').query (.inr (.inr q))) : OracleComp (PSpec prims D') _)

/-! ## Closing -/

theorem close_liftM {β : Type} (ob : ProbComp β) :
    simulateQ (closeImpl prims D) (liftM ob : OracleComp (PSpec prims D) β) =
      (liftM ob : OracleComp (unifSpec + (D →ₒ prims.Y)) β) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    congr 1

theorem close_gameQ (d : D) :
    simulateQ (closeImpl prims D) (gameQ prims d) =
      (PRFScheme.functionQuery d : OracleComp (PRFScheme.PRFOracleSpec D prims.Y) _) := by
  unfold gameQ
  rw [simulateQ_spec_query]
  rfl

theorem close_prfMsgQ (skPrf : prims.SkPrf) (addrnd : prims.Y) (m : List Byte) :
    simulateQ (closeImpl prims D) (prfMsgQ prims D skPrf addrnd m) =
      pure (prims.PRFmsg skPrf addrnd m) := by
  unfold prfMsgQ
  rw [simulateQ_spec_query]
  rfl

/-- Closing an embedded public-hash program evaluates it by `prims`. -/
theorem close_hashEmb {α : Type} (oa : OracleComp (publicHashSpec prims.core) α) :
    simulateQ (closeImpl prims D) (simulateQ (hashEmb prims D) oa) =
      pure (simulateQ (PublicHash.impl prims) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    have h : simulateQ (closeImpl prims D) (hashEmb prims D t) =
        pure (PublicHash.impl prims t) := by
      unfold hashEmb
      rw [simulateQ_spec_query]
      rfl
    rw [h, pure_bind]
    rfl

/-- In the closed world public hashes are evaluated by `prims`. -/
@[reducible] def closedQ (prims : Primitives p) (D : Type) :
    HasQuery (publicHashSpec prims.core) (OracleComp (unifSpec + (D →ₒ prims.Y))) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] openQ closedQ

/-- `closeImpl` as a public-hash-preserving monad morphism (open queries ↦ evaluation by
`prims`). -/
noncomputable def closeHom (prims : Primitives p) (D : Type) :
    HasQuery.QueryHom (publicHashSpec prims.core) (OracleComp (PSpec prims D))
      (OracleComp (unifSpec + (D →ₒ prims.Y))) :=
  { toMonadHom := simulateQ' (closeImpl prims D)
    map_query' := fun q => by
      simp [closeImpl, HSpec.impl] }

theorem closeHom_apply {α : Type} (oa : OracleComp (PSpec prims D) α) :
    (closeHom prims D).toMonadHom oa = simulateQ (closeImpl prims D) oa := rfl

/-! ## Restricting the function-oracle domain -/

theorem close_restrictO [Inhabited prims.Y] (r : D → Option D') {α : Type}
    (oa : OracleComp (PSpec prims D) α) :
    simulateQ (closeImpl prims D') (simulateQ (restrictO r) oa) =
      simulateQ (Restrict.restrictImpl r) (simulateQ (closeImpl prims D) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | d | q
    · have e1 : restrictO (prims := prims) r (Sum.inl n) =
          (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (PSpec prims D') _) := rfl
      have e2 : closeImpl prims D (Sum.inl n) =
          (liftM (liftM (unifSpec.query n) : ProbComp _) :
            OracleComp (unifSpec + (D →ₒ prims.Y)) _) := rfl
      rw [e1, e2, close_liftM, Restrict.simulateQ_restrict_liftM]
      exact bind_congr fun u => ih u
    · have e2 : closeImpl prims D (Sum.inr (Sum.inl d)) =
          (liftM ((unifSpec + (D →ₒ prims.Y)).query (Sum.inr d)) :
            OracleComp (unifSpec + (D →ₒ prims.Y)) _) := rfl
      rw [e2, simulateQ_spec_query]
      cases hd : r d with
      | none =>
        have e1 : restrictO (prims := prims) r (Sum.inr (Sum.inl d)) =
            pure (default : prims.Y) := by
          simp only [restrictO, hd]
        rw [e1, Restrict.restrictImpl_inr_none r hd, simulateQ_pure]
        exact bind_congr fun u => ih u
      | some d' =>
        have e1 : restrictO (prims := prims) r (Sum.inr (Sum.inl d)) = gameQ prims d' := by
          simp only [restrictO, hd]
        rw [e1, Restrict.restrictImpl_inr_some r hd, close_gameQ]
        exact bind_congr fun u => ih u
    · have e1 : simulateQ (closeImpl prims D') (restrictO (prims := prims) r (Sum.inr (Sum.inr q)))
          = pure (HSpec.impl prims q) := by
        simp only [restrictO]
        rw [simulateQ_spec_query]
        rfl
      have e2 : closeImpl prims D (Sum.inr (Sum.inr q)) = pure (HSpec.impl prims q) := rfl
      rw [e1, e2, simulateQ_pure, pure_bind, pure_bind]
      exact ih _

/-! ## Counting by kind -/

theorem query_kindBound (K : HKind) (t : ℕ ⊕ (D ⊕ (_ ⊕ _))) :
    IsQueryBoundP (liftM ((PSpec prims D).query t) : OracleComp (PSpec prims D) _)
      (fun t => hkind t = K) (hind K (hkind t)) :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [hind, h]

/-- A lifted `ProbComp` makes only `unif` queries. -/
theorem liftM_kindBound {β : Type} (K : HKind) (hK : K ≠ .unif) (ob : ProbComp β) :
    IsQueryBoundP (liftM ob : OracleComp (PSpec prims D) β) (fun t => hkind t = K) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by cases t <;> simp_all [hkind])
    (isQueryBoundP_liftM_isRight (hs := (D →ₒ prims.Y) + HSpec prims) ob)

theorem gameQ_kindBound (K : HKind) (d : D) :
    IsQueryBoundP (gameQ prims d) (fun t => hkind t = K) (hind K .game) :=
  query_kindBound K _

theorem prfMsgQ_kindBound (K : HKind) (skPrf : prims.SkPrf) (addrnd : prims.Y) (m : List Byte) :
    IsQueryBoundP (prfMsgQ prims D skPrf addrnd m) (fun t => hkind t = K) (hind K .prfmsg) :=
  query_kindBound K _

/-- An embedded public-hash program with at most `n` queries makes at most `n` hash queries and
no query of another kind. -/
theorem hashEmb_kindBound {α : Type} (K : HKind) {oa : OracleComp (publicHashSpec prims.core) α}
    {n : ℕ} (h : IsQueryBoundP oa (fun _ => True) n) :
    IsQueryBoundP (simulateQ (hashEmb prims D) oa) (fun t => hkind t = K) (hind K .hash * n) := by
  by_cases hK : K = .hash
  · subst hK
    have h1 := IsQueryBoundP.simulateQ_of_step (q := fun t => hkind t = HKind.hash)
      (impl := hashEmb prims D) h
      (fun t _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      (fun t ht => absurd trivial ht)
    simpa [hind] using h1
  · have h0 := isQueryBoundP_simulateQ_zero (q := fun t => hkind t = K) (impl := hashEmb prims D)
      oa (fun t => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h.symm hK)
    simpa [hind, hK] using h0

/-- Restricting the function-oracle domain does not increase the number of queries of any
kind. -/
theorem restrictO_kindBound [Inhabited prims.Y] (r : D → Option D') (K : HKind) {α : Type}
    {oa : OracleComp (PSpec prims D) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => hkind t = K) n) :
    IsQueryBoundP (simulateQ (restrictO (prims := prims) r) oa) (fun t => hkind t = K) n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | d | q
    · exact (isQueryBoundP_query_iff (spec := PSpec prims D') _ (.inl n) 1).2 fun _ => Nat.one_pos
    · cases hd : r d with
      | none =>
        simp only [restrictO, hd]
        exact isQueryBoundP_pure _ _ _
      | some d' =>
        simp only [restrictO, hd]
        exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | d | q
    · exact (isQueryBoundP_query_iff (spec := PSpec prims D') _ (.inl n) 0).2
        fun h => absurd h ht
    · cases hd : r d with
      | none =>
        simp only [restrictO, hd]
        exact isQueryBoundP_pure _ _ _
      | some d' =>
        simp only [restrictO, hd]
        exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => (ht (by cases q <;> exact h)).elim

#print axioms Reduction.Open.close_hashEmb
#print axioms Reduction.Open.close_restrictO
#print axioms Reduction.Open.hashEmb_kindBound
#print axioms Reduction.Open.restrictO_kindBound

end Open
end Reduction
