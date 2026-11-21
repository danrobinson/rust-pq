import Reduction.Basic

/-!
# Forgers over a general sampling spec: basic definitions

The forger's private randomness is `ds + unifSpec` for an arbitrary oracle spec `ds` with an
`AnswerMeasure` and finite answer types (e.g. quantum's `distSpec`: "sample from a given finite
distribution with real probabilities").  This file fixes the shapes shared by all `Gen` files:

* `gSpec ds = ds + unifSpec` — the general sampling interface (quantum's `privSpec` at
  `ds := distSpec`, definitionally);
* `liftR : ProbComp α → OracleComp (gSpec ds) α` — classical probabilistic code run over the
  general interface (quantum's `liftR`, same definition);
* `embed : OracleComp (us + X) α → OracleComp ((ds + us) + X) α` — a program that does not use
  `ds`, as a program over the bigger interface.
-/

open OracleComp OracleSpec ENNReal

namespace Reduction.Gen

variable {κ ιu ιx : Type}

/-- The general sampling interface: `ds`-sampling and uniform sampling. -/
abbrev gSpec (ds : OracleSpec κ) : OracleSpec (κ ⊕ ℕ) := ds + unifSpec

/-- Run classical probabilistic code over the general sampling interface. -/
def liftR (ds : OracleSpec κ) {α : Type} (oa : ProbComp α) : OracleComp (gSpec ds) α :=
  simulateQ (fun n ↦ liftM ((gSpec ds).query (Sum.inr n))) oa

/-- The query relabelling behind `embed`. -/
def embedImpl (ds : OracleSpec κ) (us : OracleSpec ιu) (X : OracleSpec ιx) :
    QueryImpl (us + X) (OracleComp ((ds + us) + X))
  | .inl n => liftM (((ds + us) + X).query (Sum.inl (Sum.inr n)))
  | .inr x => liftM (((ds + us) + X).query (Sum.inr x))

/-- A program over `us + X` as a program over `(ds + us) + X` (it makes no `ds`-query). -/
def embed (ds : OracleSpec κ) {us : OracleSpec ιu} {X : OracleSpec ιx} {α : Type}
    (t : OracleComp (us + X) α) : OracleComp ((ds + us) + X) α :=
  simulateQ (embedImpl ds us X) t

variable (ds : OracleSpec κ) {us : OracleSpec ιu} {X : OracleSpec ιx} {α β : Type}

@[simp] lemma liftR_pure (a : α) : liftR ds (pure a) = pure a := by simp [liftR]

@[simp] lemma liftR_bind (oa : ProbComp α) (f : α → ProbComp β) :
    liftR ds (oa >>= f) = liftR ds oa >>= fun a ↦ liftR ds (f a) := by simp [liftR]

@[simp] lemma liftR_map (oa : ProbComp α) (f : α → β) :
    liftR ds (f <$> oa) = f <$> liftR ds oa := by simp [liftR]

lemma liftR_query (n : ℕ) :
    liftR ds (liftM (unifSpec.query n)) = liftM ((gSpec ds).query (Sum.inr n)) := by
  simp [liftR]

@[simp] lemma embed_pure (a : α) : embed ds (pure a : OracleComp (us + X) α) = pure a := by
  simp [embed]

@[simp] lemma embed_bind (oa : OracleComp (us + X) α) (f : α → OracleComp (us + X) β) :
    embed ds (oa >>= f) = embed ds oa >>= fun a ↦ embed ds (f a) := by simp [embed]

@[simp] lemma embed_map (oa : OracleComp (us + X) α) (f : α → β) :
    embed ds (f <$> oa) = f <$> embed ds oa := by simp [embed]

lemma embed_query_inl (n : us.Domain) :
    embed ds (liftM ((us + X).query (Sum.inl n)) : OracleComp (us + X) _) =
      liftM (((ds + us) + X).query (Sum.inl (Sum.inr n))) := by
  simp [embed, embedImpl]

lemma embed_query_inr (x : X.Domain) :
    embed ds (liftM ((us + X).query (Sum.inr x)) : OracleComp (us + X) _) =
      liftM (((ds + us) + X).query (Sum.inr x)) := by
  simp [embed, embedImpl]

end Reduction.Gen
