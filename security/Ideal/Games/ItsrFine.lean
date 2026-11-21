import Ideal.Games.Itsr

/-!
# ITSR in the ideal-compression model with finer accounting of the adversary's queries

`Ideal.Itsr.itsr_le` counts EVERY compression query of the adversary as one coordinate of the
tape of digests.  That is vacuous for an adversary that itself evaluates many hashes which can
never be the final compression call of the keyed hash (the Reduction's ITSR adversary signs every
query itself, `≈ qs · 2^21` tweakable-hash evaluations).

Here the adversary has two kinds of compression access:

* raw compression queries `(c, b)`;
* **chain queries** `bs`: the Merkle–Damgård iteration `mdFold g IV bs` from the initial value
  (this is how every SHA-256 based evaluation — `Thash`, `PRF`, HMAC, MGF1, `H_msg` — uses the
  compression function).

and a predicate `P : Blk → Bool` that holds for the last block of the outer hash of the keyed
hash (`hobP`).  Only the following count as coordinates of the tape (`itsr_le_fine`):

* raw queries `(c, b)` with `P b`;
* chain queries whose SECOND block satisfies `P`;
* two calls per hash of the final check (as in `itsr_le`).

Why this is sound: the final cell of a hash is `(g (IV, b₀), b₁)` with `P b₁`.  A cell read
without being logged has chaining value `IV`, or a chaining value of depth at least two, or a
block not satisfying `P` (invariant `InvP`); unless the table is bad on the cells read (a repeated
value or the value `IV`, `≤ Q² / |St|`), none of these is a final cell.  In a chain query the
call at position 0 has chaining value `IV`, the calls at positions `≥ 2` have depth `≥ 2`, and
the call at position 1 is marked iff its block satisfies `P`.

`gameProgF_bound`: the counts of the experiment from the counts of the adversary.
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal.Itsr

open Ideal.HP Ideal.Prf AnswerTape

variable {St Blk K X Y Index : Type}

/-! ## Adversaries with chain queries -/

/-- Chain queries: `bs ↦ mdFold g IV bs`. -/
abbrev chS (St Blk : Type) : OracleSpec (List Blk) := List Blk →ₒ St

/-- The adversary's compression access: raw compression queries and chain queries. -/
abbrev aS (St Blk : Type) : OracleSpec ((St × Blk) ⊕ List Blk) := hS St Blk + chS St Blk

/-- An ideal-model ITSR adversary with chain queries. -/
abbrev ItsrAdvF (St Blk K X : Type) :=
  OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) (K × X)

/-- Answer raw compression queries with `g` and chain queries with the Merkle–Damgård iteration
of `g` from `IV`; forward uniform sampling and target queries. -/
def instImplF (IV : St) (g : CF St Blk) :
    QueryImpl (unifSpec + (aS St Blk + ITSRTargetSpec X K))
      (OracleComp (unifSpec + ITSRTargetSpec X K)) := fun
  | .inl n => (unifSpec + ITSRTargetSpec X K).query (.inl n)
  | .inr (.inl (.inl q)) => pure (g q)
  | .inr (.inl (.inr bs)) => pure (mdFold g IV bs)
  | .inr (.inr x) => (unifSpec + ITSRTargetSpec X K).query (.inr x)

/-- The adversary at a fixed compression table. -/
def ItsrAdvF.inst (A : ItsrAdvF St Blk K X) (IV : St) (prob : ITSRProblem K X Y Index)
    (g : CF St Blk) : ITSRAdversary prob where
  main := simulateQ (instImplF IV g) A

/-- Merkle–Damgård iteration issued as compression queries; the query at block position 1 is
marked iff its block satisfies `P`. -/
def mdP (P : Blk → Bool) (c : St) : List Blk → OracleComp (unifSpec + mS St Blk) St
  | [] => pure c
  | [b₀] => cq c b₀ false
  | b₀ :: b₁ :: bs => cq c b₀ false >>= fun c₁ => cq c₁ b₁ (P b₁) >>= fun c₂ => mdMF c₂ bs

/-- The second block of a chain query satisfies `P`. -/
def secondP (P : Blk → Bool) : List Blk → Bool
  | _ :: b₁ :: _ => P b₁
  | _ => false

/-- The target oracle over the marked compression oracle, with the fine marking: a raw query is
marked iff its block satisfies `P`; a chain query is issued through `mdP`. -/
def tgtImplF [SampleableType K] (P : Blk → Bool) (IV : St) :
    QueryImpl (unifSpec + (aS St Blk + ITSRTargetSpec X K))
      (StateT (List (K × X)) (OracleComp (unifSpec + mS St Blk))) := fun
  | .inl n => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + mS St Blk).query (.inl n)) :
        OracleComp (unifSpec + mS St Blk) _)
  | .inr (.inl (.inl q)) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + mS St Blk).query (.inr (q, P q.2))) :
        OracleComp (unifSpec + mS St Blk) _)
  | .inr (.inl (.inr bs)) => StateT.mk fun s => (fun u => (u, s)) <$> mdP P IV bs
  | .inr (.inr x) => StateT.mk fun s =>
      (fun k : K => (k, s ++ [(k, x)])) <$> (liftM ($ᵗ K : ProbComp K) :
        OracleComp (unifSpec + mS St Blk) K)

/-- The whole ITSR experiment as one program over the marked compression oracle, with the fine
marking of the adversary's queries. -/
def gameProgF [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (P : Blk → Bool) (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvF St Blk K X) : OracleComp (unifSpec + mS St Blk) Bool :=
  (simulateQ (tgtImplF P IV) A).run [] >>= finM IV ib ob od idx

/-! ## Evaluation at a table -/

theorem simulateQ_mdP (P : Blk → Bool) (g : CF St Blk) (c : St) (bs : List Blk) :
    simulateQ (markImpl g) (mdP P c bs) = pure (mdFold g c bs) := by
  match bs with
  | [] => simp [mdP, mdFold]
  | [b₀] => rw [mdP, simulateQ_cq]; rfl
  | b₀ :: b₁ :: bs => rw [mdP, simulateQ_cq_bind, simulateQ_cq_bind, simulateQ_mdMF]; rfl

theorem run_tgt_eqF [SampleableType K] (P : Blk → Bool) (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (idx : Y → List Index) (g : CF St Blk)
    (A : ItsrAdvF St Blk K X) (s : List (K × X)) :
    (simulateQ (ITSROracles (probI IV ib ob od idx g)) (simulateQ (instImplF IV g) A)).run s =
      simulateQ (markImpl g) ((simulateQ (tgtImplF P IV) A).run s) := by
  refine simulateQ_run_simulateQ_eq_of_step _ _ _ _ (fun t s => ?_) A s
  rcases t with n | (q | bs) | x
  · simp [instImplF, tgtImplF, ITSROracles]
  · simp [instImplF, tgtImplF, ITSROracles]
  · simp [instImplF, tgtImplF, ITSROracles, simulateQ_mdP]
  · simp [instImplF, tgtImplF, ITSROracles]
    exact (simulateQ_ansImpl_liftM (spec := mS St Blk) (fun t => g t.1) _).symm

/-- **The monadic game with fine marking, at a table, is VCVio's ITSR experiment.** -/
theorem simulateQ_gameProgF [SampleableType K] [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] (P : Blk → Bool)
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvF St Blk K X) (g : CF St Blk) :
    simulateQ (markImpl g) (gameProgF P IV ib ob od idx A) =
      ITSRExperiment (A.inst IV (probI IV ib ob od idx g) g) := by
  simp only [gameProgF, finM, simulateQ_bind, simulateQ_hashAllM, simulateQ_hashM, pure_bind,
    simulateQ_pure, ITSRExperiment, ITSRAdversary.run, ItsrAdvF.inst, run_tgt_eqF P]
  refine bind_congr fun z => ?_
  refine congrArg pure (decide_eq_decide.mpr ?_)
  simp only [ITSRProblem.Wins, ITSRProblem.indexSet, ITSRProblem.targetIndexSet, probI,
    List.flatMap_map]
  rfl

section Eqs

variable [SampleableType K] (P : Blk → Bool) (IV : St)

theorem tgtImplF_unif_bind {α : Type} (n : ℕ)
    (k : (unifSpec + (aS St Blk + ITSRTargetSpec X K)).Range (.inl n) →
      OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) α) (s₀ : List (K × X)) :
    (simulateQ (tgtImplF P IV)
      (liftM ((unifSpec + (aS St Blk + ITSRTargetSpec X K)).query (.inl n)) >>= k)).run s₀ =
      (liftM ((unifSpec + mS St Blk).query (.inl n)) : OracleComp (unifSpec + mS St Blk) _) >>=
        fun u => (simulateQ (tgtImplF P IV) (k u)).run s₀ := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImplF, StateT.run_mk,
    bind_map_left]
  rfl

theorem tgtImplF_raw_bind {α : Type} (q : St × Blk)
    (k : St → OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) α)
    (s₀ : List (K × X)) :
    (simulateQ (tgtImplF P IV)
      (liftM ((unifSpec + (aS St Blk + ITSRTargetSpec X K)).query (.inr (.inl (.inl q)))) >>=
        k)).run s₀ =
      (liftM ((unifSpec + mS St Blk).query (.inr (q, P q.2))) :
        OracleComp (unifSpec + mS St Blk) _) >>=
        fun u => (simulateQ (tgtImplF P IV) (k u)).run s₀ := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImplF, StateT.run_mk,
    bind_map_left]
  rfl

theorem tgtImplF_chain_bind {α : Type} (bs : List Blk)
    (k : St → OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) α)
    (s₀ : List (K × X)) :
    (simulateQ (tgtImplF P IV)
      (liftM ((unifSpec + (aS St Blk + ITSRTargetSpec X K)).query (.inr (.inl (.inr bs)))) >>=
        k)).run s₀ =
      mdP P IV bs >>= fun u => (simulateQ (tgtImplF P IV) (k u)).run s₀ := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImplF, StateT.run_mk,
    bind_map_left]
  rfl

theorem tgtImplF_tgt_bind {α : Type} (x : X)
    (k : K → OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) α)
    (s₀ : List (K × X)) :
    (simulateQ (tgtImplF P IV)
      (liftM ((unifSpec + (aS St Blk + ITSRTargetSpec X K)).query (.inr (.inr x))) >>=
        k)).run s₀ =
      (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + mS St Blk) K) >>=
        fun k' => (simulateQ (tgtImplF P IV) (k k')).run (s₀ ++ [(k', x)]) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tgtImplF, StateT.run_mk,
    bind_map_left]

end Eqs

/-! ## The invariant -/

section Log

set_option linter.unusedSectionVars false

variable [DecidableEq St] [DecidableEq Blk]

/-- Invariant: the log is among the cells read, and every cell read but not logged has chaining
value `IV`, or a chaining value at depth at least two, or a block not satisfying `P`. -/
def InvP (P : Blk → Bool) (IV : St) (g : CF St Blk)
    (st : List (St × Blk) × List (St × Blk)) : Prop :=
  (∀ c ∈ st.2, c ∈ st.1) ∧
    ∀ c ∈ st.1, c ∉ st.2 → c.1 = IV ∨ Val2 g st.1 c.1 ∨ P c.2 = false

theorem invP_nil (P : Blk → Bool) (IV : St) (g : CF St Blk) : InvP P IV g ([], []) := by
  constructor <;> simp

theorem invP_stepM_true (P : Blk → Bool) (IV : St) (g : CF St Blk) (c : St × Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : InvP P IV g st) :
    InvP P IV g (stepM (c, true) st) := by
  by_cases hc : c ∈ st.1
  · have e : stepM (c, true) st = st := by
      simp [stepM, logM, logU_of_mem (cell := Prod.fst) (t := (c, true)) hc, hc]
    rw [e]; exact h
  · have e : stepM (c, true) st = (st.1 ++ [c], st.2 ++ [c]) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := (c, true)) hc, hc]
    rw [e]
    constructor
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (h.1 x hx)
      · exact List.mem_append_right _ hx
    · intro x hx hxs
      rcases List.mem_append.mp hx with hx | hx
      · rcases h.2 x hx (fun h' => hxs (List.mem_append_left _ h')) with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (h1.mono (List.sublist_append_left _ _)))
        · exact Or.inr (Or.inr h1)
      · exact absurd (List.mem_append_right _ hx) hxs

theorem invP_stepM_false (P : Blk → Bool) (IV : St) (g : CF St Blk) (c : St × Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : InvP P IV g st)
    (hf : c.1 = IV ∨ Val2 g st.1 c.1 ∨ P c.2 = false) : InvP P IV g (stepM (c, false) st) := by
  by_cases hc : c ∈ st.1
  · have e : stepM (c, false) st = st := by
      simp [stepM, logM, logU_of_mem (cell := Prod.fst) (t := (c, false)) hc]
    rw [e]; exact h
  · have e : stepM (c, false) st = (st.1 ++ [c], st.2) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := (c, false)) hc]
    rw [e]
    constructor
    · exact fun x hx => List.mem_append_left _ (h.1 x hx)
    · intro x hx hxs
      rcases List.mem_append.mp hx with hx | hx
      · rcases h.2 x hx hxs with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (h1.mono (List.sublist_append_left _ _)))
        · exact Or.inr (Or.inr h1)
      · rw [List.mem_singleton.mp hx]
        rcases hf with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (h1.mono (List.sublist_append_left _ _)))
        · exact Or.inr (Or.inr h1)

/-- A read marked iff its block satisfies `P` preserves the invariant. -/
theorem invP_stepM_P (P : Blk → Bool) (IV : St) (g : CF St Blk) (c : St × Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : InvP P IV g st) :
    InvP P IV g (stepM (c, P c.2) st) := by
  cases hP : P c.2
  · exact invP_stepM_false P IV g c st h (Or.inr (Or.inr hP))
  · exact invP_stepM_true P IV g c st h

/-- A marked read of a cell `(g c₀, b)` with `c₀ = (IV, ·)` already read and `P b`: the cell is
in the log afterwards, or the table is bad on the cells read. -/
theorem key_trueP (P : Blk → Bool) (IV : St) (g : CF St Blk) (c₀ : St × Blk) (b : Blk)
    (st : List (St × Blk) × List (St × Blk)) (h : InvP P IV g st) (hc₀ : c₀ ∈ st.1)
    (hIV : c₀.1 = IV) (hb : P b = true) :
    (g c₀, b) ∈ (stepM ((g c₀, b), true) st).2 ∨ badV IV (st.1.map g) = true := by
  by_cases hs : (g c₀, b) ∈ st.2
  · exact Or.inl ((mono_stepM _ st).2 _ hs)
  by_cases hc : (g c₀, b) ∈ st.1
  · refine Or.inr ?_
    simp only [badV, decide_eq_true_eq]
    by_contra hbad
    simp only [not_or, not_not] at hbad
    rcases h.2 _ hc hs with h1 | ⟨c', hc', e, c'', hc'', e'⟩ | h1
    · exact hbad.2 (List.mem_map.mpr ⟨c₀, hc₀, h1⟩)
    · have : c' = c₀ := List.inj_on_of_nodup_map hbad.1 hc' hc₀ e
      rw [this, hIV] at e'
      exact hbad.2 (List.mem_map.mpr ⟨c'', hc'', e'⟩)
    · rw [hb] at h1
      exact absurd h1 (by simp)
  · refine Or.inl ?_
    have e : stepM ((g c₀, b), true) st = (st.1 ++ [(g c₀, b)], st.2 ++ [(g c₀, b)]) := by
      simp [stepM, logM, logU_of_not_mem (cell := Prod.fst) (t := ((g c₀, b), true)) hc, hc]
    rw [e]
    simp

theorem run_mdMF_P (P : Blk → Bool) (IV : St) (g : CF St Blk) (bs : List Blk) :
    ∀ (c : St) (st : List (St × Blk) × List (St × Blk)), InvP P IV g st → Val2 g st.1 c →
      ∃ st', (simulateQ (mImpl g) (mdMF c bs)).run st = pure (mdFold g c bs, st') ∧
        InvP P IV g st' ∧ Mono st st' ∧ ∀ x ∈ mdCells g c bs, x ∈ st'.1 := by
  induction bs with
  | nil =>
    intro c st hI _
    exact ⟨st, by simp [mdMF, mdFold], hI, Mono.refl _, by simp [mdCells]⟩
  | cons b bs ih =>
    intro c st hI hv
    have hI1 := invP_stepM_false P IV g (c, b) st hI (Or.inr (Or.inl hv))
    have hm1 := mono_stepM ((c, b), false) st
    have hv1 : Val2 g (stepM ((c, b), false) st).1 (g (c, b)) := by
      obtain ⟨c', hc', e, -⟩ := hv
      exact ⟨(c, b), mem_stepM ((c, b), false) st, rfl, c', hm1.1.subset hc', e⟩
    obtain ⟨st', hrun, hI', hm', hcells⟩ := ih (g (c, b)) _ hI1 hv1
    refine ⟨st', ?_, hI', hm1.trans hm', fun x hx => ?_⟩
    · rw [mdMF, run_cq_bind, hrun]; rfl
    · simp only [mdCells, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hm'.1.subset (mem_stepM ((c, b), false) st)
      · exact hcells x hx

/-- The final check's iteration (position 1 marked) under the invariant `InvP`. -/
theorem run_mdM_P (P : Blk → Bool) (IV : St) (g : CF St Blk) (bs : List Blk)
    (st : List (St × Blk) × List (St × Blk)) (hI : InvP P IV g st) :
    ∃ st', (simulateQ (mImpl g) (mdM IV bs)).run st = pure (mdFold g IV bs, st') ∧
      InvP P IV g st' ∧ Mono st st' ∧ (∀ x ∈ mdCells g IV bs, x ∈ st'.1) ∧
      ∀ b₀ b₁ rest, bs = b₀ :: b₁ :: rest → P b₁ = true →
        (g (IV, b₀), b₁) ∈ st'.2 ∨ badV IV (st'.1.map g) = true := by
  match bs with
  | [] =>
    exact ⟨st, by simp [mdM, mdFold], hI, Mono.refl _, by simp [mdCells], by simp⟩
  | [b₀] =>
    refine ⟨stepM ((IV, b₀), false) st, ?_,
      invP_stepM_false P IV g (IV, b₀) st hI (Or.inl rfl), mono_stepM _ st, fun x hx => ?_,
      by simp⟩
    · rw [mdM, run_cq]; rfl
    · simp only [mdCells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
      exact mem_stepM ((IV, b₀), false) st
  | b₀ :: b₁ :: rest =>
    have hI1 := invP_stepM_false P IV g (IV, b₀) st hI (Or.inl rfl)
    have hm1 := mono_stepM ((IV, b₀), false) st
    have h0 := mem_stepM ((IV, b₀), false) st
    set st₁ := stepM ((IV, b₀), false) st with hst₁
    have hI2 := invP_stepM_true P IV g (g (IV, b₀), b₁) st₁ hI1
    have hm2 := mono_stepM ((g (IV, b₀), b₁), true) st₁
    have h1 := mem_stepM ((g (IV, b₀), b₁), true) st₁
    have hk := fun hb : P b₁ = true => key_trueP P IV g (IV, b₀) b₁ st₁ hI1 h0 rfl hb
    set st₂ := stepM ((g (IV, b₀), b₁), true) st₁ with hst₂
    have hv : Val2 g st₂.1 (g (g (IV, b₀), b₁)) :=
      ⟨(g (IV, b₀), b₁), h1, rfl, (IV, b₀), hm2.1.subset h0, rfl⟩
    obtain ⟨st', hrun, hI', hm', hcells⟩ := run_mdMF_P P IV g rest _ st₂ hI2 hv
    refine ⟨st', ?_, hI', (hm1.trans hm2).trans hm', fun x hx => ?_,
      fun b₀' b₁' rest' e hb => ?_⟩
    · rw [mdM, run_cq_bind, run_cq_bind, hrun]; rfl
    · simp only [mdCells, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact (hm2.trans hm').1.subset h0
      · exact hm'.1.subset h1
      · exact hcells x hx
    · obtain ⟨rfl, e2⟩ := List.cons.inj e
      obtain ⟨rfl, -⟩ := List.cons.inj e2
      rcases hk hb with hk | hk
      · exact Or.inl (hm'.2 _ hk)
      · exact Or.inr (badV_mono IV _ _ ((hm2.trans hm').1.map g) hk)

/-- A chain query of the adversary (position 1 marked iff `P`) preserves the invariant. -/
theorem run_mdP (P : Blk → Bool) (IV : St) (g : CF St Blk) (bs : List Blk)
    (st : List (St × Blk) × List (St × Blk)) (hI : InvP P IV g st) :
    ∃ st', (simulateQ (mImpl g) (mdP P IV bs)).run st = pure (mdFold g IV bs, st') ∧
      InvP P IV g st' := by
  match bs with
  | [] => exact ⟨st, by simp [mdP, mdFold], hI⟩
  | [b₀] =>
    refine ⟨stepM ((IV, b₀), false) st, ?_,
      invP_stepM_false P IV g (IV, b₀) st hI (Or.inl rfl)⟩
    rw [mdP, run_cq]; rfl
  | b₀ :: b₁ :: rest =>
    have hI1 := invP_stepM_false P IV g (IV, b₀) st hI (Or.inl rfl)
    have h0 := mem_stepM ((IV, b₀), false) st
    set st₁ := stepM ((IV, b₀), false) st with hst₁
    have hI2 := invP_stepM_P P IV g (g (IV, b₀), b₁) st₁ hI1
    have hm2 := mono_stepM ((g (IV, b₀), b₁), P b₁) st₁
    have h1 := mem_stepM ((g (IV, b₀), b₁), P b₁) st₁
    set st₂ := stepM ((g (IV, b₀), b₁), P b₁) st₁ with hst₂
    have hv : Val2 g st₂.1 (g (g (IV, b₀), b₁)) :=
      ⟨(g (IV, b₀), b₁), h1, rfl, (IV, b₀), hm2.1.subset h0, rfl⟩
    obtain ⟨st', hrun, hI', -, -⟩ := run_mdMF_P P IV g rest _ st₂ hI2 hv
    refine ⟨st', ?_, hI'⟩
    rw [mdP, run_cq_bind, run_cq_bind, hrun]; rfl

theorem run_hashM_P (P : Blk → Bool) (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y)
    (hob2 : ∀ kx s, (ob kx s).length = 2)
    (hobP : ∀ kx s b₀ b₁, ob kx s = [b₀, b₁] → P b₁ = true)
    (g : CF St Blk) (kx : K × X) (st : List (St × Blk) × List (St × Blk))
    (hI : InvP P IV g st) :
    ∃ st', (simulateQ (mImpl g) (hashM IV ib ob od kx)).run st =
        pure (hashG IV ib ob od g kx, st') ∧
      InvP P IV g st' ∧ Mono st st' ∧ (∀ c ∈ cellsH IV ib ob g kx, c ∈ st'.1) ∧
      FinOK IV ib ob g kx st' := by
  obtain ⟨st₁, hr1, hI1, hm1, hc1, -⟩ := run_mdM_P P IV g (ib kx) st hI
  obtain ⟨st₂, hr2, hI2, hm2, hc2, hk⟩ :=
    run_mdM_P P IV g (ob kx (mdFold g IV (ib kx))) st₁ hI1
  refine ⟨st₂, ?_, hI2, hm1.trans hm2, fun c hc => ?_, fun as b e => ?_⟩
  · simp only [hashM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
      StateT.run_pure, hashG]
  · rcases List.mem_append.mp hc with h | h
    · exact hm2.1.subset (hc1 c h)
    · exact hc2 c h
  · have hl := hob2 kx (mdFold g IV (ib kx))
    rw [e] at hl
    obtain ⟨b₀, rfl⟩ := List.length_eq_one_iff.mp (show as.length = 1 by simpa using hl)
    exact hk b₀ b [] e (hobP kx _ b₀ b e)

theorem run_hashAllM_P (P : Blk → Bool) (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (hob2 : ∀ kx s, (ob kx s).length = 2)
    (hobP : ∀ kx s b₀ b₁, ob kx s = [b₀, b₁] → P b₁ = true)
    (g : CF St Blk) (l : List (K × X)) :
    ∀ st : List (St × Blk) × List (St × Blk), InvP P IV g st →
      ∃ st', (simulateQ (mImpl g) (hashAllM IV ib ob od l)).run st =
          pure (l.map (hashG IV ib ob od g), st') ∧
        InvP P IV g st' ∧ Mono st st' ∧
        ∀ kx ∈ l, (∀ c ∈ cellsH IV ib ob g kx, c ∈ st'.1) ∧ FinOK IV ib ob g kx st' := by
  induction l with
  | nil =>
    intro st hI
    exact ⟨st, by simp [hashAllM], hI, Mono.refl _, by simp⟩
  | cons kx l ih =>
    intro st hI
    obtain ⟨st₁, hr1, hI1, hm1, hc1, hf1⟩ := run_hashM_P P IV ib ob od hob2 hobP g kx st hI
    obtain ⟨st₂, hr2, hI2, hm2, hall⟩ := ih st₁ hI1
    refine ⟨st₂, ?_, hI2, hm1.trans hm2, fun kx' hkx' => ?_⟩
    · simp only [hashAllM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
        StateT.run_pure, List.map_cons]
    · rcases List.mem_cons.mp hkx' with rfl | h
      · exact ⟨fun c hc => hm2.1.subset (hc1 c hc), hf1.mono hm2⟩
      · exact hall kx' h

/-- The adversary phase preserves the invariant `InvP`. -/
theorem adv_invF [SampleableType K] (P : Blk → Bool) (IV : St) (g : CF St Blk)
    (A : ItsrAdvF St Blk K X) :
    ∀ (s₀ : List (K × X)) (st : List (St × Blk) × List (St × Blk)), InvP P IV g st →
      ∀ z ∈ support ((simulateQ (mImpl g) ((simulateQ (tgtImplF P IV) A).run s₀)).run st),
        InvP P IV g z.2 := by
  induction A using OracleComp.inductionOn with
  | pure x =>
    intro s₀ st hst z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hst
  | query_bind t k ih =>
    intro s₀ st hst z hz
    rcases t with n | (q | bs) | x
    · rw [tgtImplF_unif_bind, run_stImpl_inl_bind, mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      exact ih u s₀ st hst z hz
    · rw [tgtImplF_raw_bind, run_stImpl_inr_bind] at hz
      exact ih _ s₀ _ (invP_stepM_P P IV g q st hst) z hz
    · obtain ⟨st', hrun, hI'⟩ := run_mdP P IV g bs st hst
      rw [tgtImplF_chain_bind, simulateQ_bind, StateT.run_bind, hrun, pure_bind] at hz
      exact ih _ s₀ st' hI' z hz
    · rw [tgtImplF_tgt_bind, run_stImpl_liftM, mem_support_bind_iff] at hz
      obtain ⟨k', -, hz⟩ := hz
      exact ih k' _ st hst z hz

/-- **A winning run logs a covered digest or reads a bad table** (fine marking). -/
theorem win_logF [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (P : Blk → Bool)
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hob2 : ∀ kx s, (ob kx s).length = 2)
    (hobP : ∀ kx s b₀ b₁, ob kx s = [b₀, b₁] → P b₁ = true)
    (g : CF St Blk) (A : ItsrAdvF St Blk K X) :
    ∀ z ∈ support ((simulateQ (mImpl g) (gameProgF P IV ib ob od idx A)).run ([], [])),
      z.1 = true →
        covB idx (z.2.2.map fun c => od (g c)) = true ∨ badV IV (z.2.1.map g) = true := by
  intro z hz hwin
  simp only [gameProgF, simulateQ_bind, StateT.run_bind] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hI := adv_invF P IV g A [] ([], []) (invP_nil P IV g) w hw
  obtain ⟨st₁, hr1, hI1, -, hall⟩ := run_hashAllM_P P IV ib ob od hob2 hobP g w.1.2 w.2 hI
  obtain ⟨st₂, hr2, -, hm2, hc2, hf2⟩ := run_hashM_P P IV ib ob od hob2 hobP g w.1.1 st₁ hI1
  simp only [finM, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [decide_eq_true_eq] at hwin
  have hobne : ∀ kx s, ob kx s ≠ [] := fun kx s h => by
    have := hob2 kx s
    rw [h] at this
    simp at this
  have h := win_imp IV ib ob od idx hib hob hobne g st₂.1 st₂.2 w.1.1 w.1.2 hc2
    (fun kx hkx c hc => hm2.1.subset ((hall kx hkx).1 c hc))
    (fun hb kx hkx as b e => by
      have hf : FinOK IV ib ob g kx st₂ := by
        rcases hkx with rfl | hkx
        · exact hf2
        · exact (hall kx hkx).2.mono hm2
      exact (hf as b e).resolve_right hb)
    hwin.1 hwin.2
  rcases h with h | h
  · exact Or.inl (by simpa [covB] using h)
  · exact Or.inr h

end Log

/-! ## The bound -/

/-- **ITSR in the ideal-compression model with fine accounting.**  `P` holds for the last block
of every outer hash input (`hobP`).  `n` bounds the *marked* compression calls of the experiment
`gameProgF` — the adversary's raw queries whose block satisfies `P`, its chain queries whose
second block satisfies `P`, and two calls per hash of the final check — and `Q` bounds all its
compression calls.  The experiment is won with probability at most the probability that a tape
of `n` independent uniform digests has an entry whose indices are all covered by the other
entries, plus `Q² / |St|`. -/
theorem itsr_le_fine [DecidableEq St] [DecidableEq Blk] [Fintype St] [Finite Blk]
    [SampleableType St] [SampleableType Y] [SampleableType (CF St Blk)]
    [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (P : Blk → Bool)
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index)
    (hib : Function.Injective ib) (hob : ∀ kx kx' s s', ob kx s = ob kx' s' → s = s')
    (hob2 : ∀ kx s, (ob kx s).length = 2)
    (hobP : ∀ kx s b₀ b₁, ob kx s = [b₀, b₁] → P b₁ = true)
    (hod : ∀ p : Y → Prop, Pr{let u ← $ᵗ St}[p (od u)] = Pr{let y ← $ᵗ Y}[p y])
    (A : ItsrAdvF St Blk K X) (n Q : ℕ)
    (hn : IsQueryBoundP (gameProgF P IV ib ob od idx A) (fun i => lgB Prod.snd i = true) n)
    (hQ : IsQueryBoundP (gameProgF P IV ib ob od idx A) (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF St Blk) >>= fun g => ITSRExperiment (A.inst IV (probI IV ib ob od idx g) g)) ≤
      prT (tapeList Y n >>= fun r => pure (covB idx r)) +
        ((Q ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have h1 : prT ($ᵗ (CF St Blk) >>= fun g =>
        ITSRExperiment (A.inst IV (probI IV ib ob od idx g) g)) ≤
      prT ($ᵗ (CF St Blk) >>= fun g =>
        (simulateQ (mImpl g) (gameProgF P IV ib ob od idx A)).run ([], []) >>= fun z =>
          pure (covB idx (z.2.2.map fun c => od (g c)) || badV IV (z.2.1.map g))) := by
    refine prT_bind_mono _ _ _ fun g _ => ?_
    rw [← simulateQ_gameProgF P, markImpl_eq,
      ← fst_map_run_stImpl (spec := mS St Blk) (fun t => g t.1) (logM Prod.fst Prod.snd) _
        (([], []) : List (St × Blk) × List (St × Blk)),
      map_eq_bind_pure_comp]
    refine prT_bind_mono _ _ _ fun z hz => ?_
    simp only [Function.comp, prT_pure]
    have := win_logF P IV ib ob od idx hib hob hob2 hobP g A z hz
    cases hz1 : z.1
    · simp
    · rcases this hz1 with h | h <;> simp [h]
  refine h1.trans ?_
  refine (prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun z =>
    prT_pure_or_le _ _).trans (add_le_add ?_ ?_)
  · exact prT_tape_le_marked (spec := mS St Blk) Prod.fst Prod.snd (fun g t => g t.1)
      (fun g g' t h => h) od hod (covB idx) (covB_mono idx) _ n hn
  · have e : ∀ g : CF St Blk,
        ((simulateQ (mImpl g) (gameProgF P IV ib ob od idx A)).run ([], []) >>= fun z =>
          pure (badV IV (z.2.1.map g))) =
        ((simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1) (logU Prod.fst))
          (gameProgF P IV ib ob od idx A)).run [] >>= fun z => pure (badV IV (z.2.map g))) := by
      intro g
      rw [← fst_run_logM (spec := mS St Blk) (fun t => g t.1) Prod.fst Prod.snd _
        (([], []) : List (St × Blk) × List (St × Blk)), bind_map_left]
    simp only [e]
    refine (prT_tape_le (spec := mS St Blk) Prod.fst (fun g t => g t.1) (fun g g' t h => h) id
      (fun p => rfl) (badV IV) (badV_mono IV) _ Q hQ).trans ?_
    exact prT_tape_bad_le IV Q

/-! ## Query bounds of the experiment -/

section Bounds

variable {p : ℕ ⊕ ((St × Blk) × Bool) → Prop} [DecidablePred p]

theorem mdP_bound (P : Blk → Bool) (c : St) (bs : List Blk) :
    IsQueryBoundP (mdP P c bs) p bs.length := by
  match bs with
  | [] => simp [mdP]
  | [b₀] =>
    have := isQueryBoundP_cq_bind_succ (p := p) c b₀ false pure 0 (fun u => by simp)
    simpa [mdP] using this
  | b₀ :: b₁ :: bs =>
    exact isQueryBoundP_cq_bind_succ c b₀ false _ _ fun u =>
      isQueryBoundP_cq_bind_succ u b₁ (P b₁) _ _ fun u' => mdMF_bound u' bs

theorem mdP_bound1 (h0 : ∀ t, ¬ p (.inr (t, false))) (P : Blk → Bool) (c : St)
    (bs : List Blk) :
    IsQueryBoundP (mdP P c bs) p (if secondP P bs = true then 1 else 0) := by
  match bs with
  | [] => simp [mdP]
  | [b₀] =>
    have := isQueryBoundP_cq_bind_of_not (p := p) c b₀ false pure 0 (h0 _) (fun u => by simp)
    simpa [mdP, secondP] using this
  | b₀ :: b₁ :: bs =>
    cases hP : P b₁
    · simp only [secondP, hP, Bool.false_eq_true, ↓reduceIte]
      rw [mdP, hP]
      exact isQueryBoundP_cq_bind_of_not c b₀ false _ _ (h0 _) fun u =>
        isQueryBoundP_cq_bind_of_not u b₁ false _ _ (h0 _) fun u' => mdMF_bound0 h0 u' bs
    · simp only [secondP, hP, ↓reduceIte]
      rw [mdP, hP]
      exact isQueryBoundP_cq_bind_of_not c b₀ false _ _ (h0 _) fun u =>
        isQueryBoundP_cq_bind_succ u b₁ true _ _ fun u' => mdMF_bound0 h0 u' bs

/-- A raw compression query of the adversary satisfying `f`. -/
def rawB (f : St × Blk → Bool) : ℕ ⊕ (((St × Blk) ⊕ List Blk) ⊕ X) → Bool
  | .inr (.inl (.inl q)) => f q
  | _ => false

/-- A chain query of the adversary satisfying `f`. -/
def chB (f : List Blk → Bool) : ℕ ⊕ (((St × Blk) ⊕ List Blk) ⊕ X) → Bool
  | .inr (.inl (.inr bs)) => f bs
  | _ => false

/-- A target query of the adversary. -/
def isTgtF : ℕ ⊕ (((St × Blk) ⊕ List Blk) ⊕ X) → Bool
  | .inr (.inr _) => true
  | _ => false

/-- Every target query `x` satisfies `OK (k, x)` for all keys `k`. -/
def tgtOKF (OK : K × X → Prop) : ℕ ⊕ (((St × Blk) ⊕ List Blk) ⊕ X) → Prop
  | .inr (.inr x) => ∀ k, OK (k, x)
  | _ => True

/-- Every chain query satisfies `OKc`. -/
def chOK (OKc : List Blk → Prop) : ℕ ⊕ (((St × Blk) ⊕ List Blk) ⊕ X) → Prop
  | .inr (.inl (.inr bs)) => OKc bs
  | _ => True

theorem gameProgF_bound_aux [SampleableType K] [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] (hpl : ∀ n, ¬ p (.inl n)) (P : Blk → Bool)
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (c : ℕ) (OK : K × X → Prop)
    (hOK : ∀ kx, OK kx → IsQueryBoundP (hashM IV ib ob od kx) p c)
    (fr : St × Blk → Bool) (fc : List Blk → Bool) (w : ℕ) (OKc : List Blk → Prop)
    (hraw : ∀ q : St × Blk, p (.inr (q, P q.2)) → fr q = true)
    (hch : ∀ bs, OKc bs → IsQueryBoundP (mdP P IV bs) p (if fc bs = true then w else 0))
    (A : OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) (K × X)) :
    ∀ (q₁ q₂ qs : ℕ) (s : List (K × X)),
      IsQueryBoundP A (fun i => rawB (X := X) fr i = true) q₁ →
      IsQueryBoundP A (fun i => chB (St := St) (X := X) fc i = true) q₂ →
      IsQueryBoundP A (fun i => isTgtF (St := St) (Blk := Blk) (X := X) i = true) qs →
      AllQueriesSatisfy A (tgtOKF (St := St) (Blk := Blk) OK) →
      AllQueriesSatisfy A (chOK (St := St) (X := X) OKc) →
      (∀ kx ∈ support A, OK kx) → (∀ kx ∈ s, OK kx) →
      IsQueryBoundP ((simulateQ (tgtImplF P IV) A).run s >>= finM IV ib ob od idx) p
        (q₁ + q₂ * w + (qs + s.length + 1) * c) := by
  induction A using OracleComp.inductionOn with
  | pure x =>
    intro q₁ q₂ qs s _ _ _ _ _ hout hs
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, finM]
    refine (isQueryBoundP_bind (hashAllM_bound IV ib ob od c s fun kx h => hOK kx (hs kx h))
      fun ds _ => isQueryBoundP_bind (m := 0) (hOK x (hout x (by simp))) fun d _ => by
        simp).mono ?_
    have : (qs + s.length + 1) * c = qs * c + s.length * c + c := by ring
    omega
  | query_bind t k ih =>
    intro q₁ q₂ qs s hq₁ hq₂ hqs htgt hcok hout hs
    rw [isQueryBoundP_query_bind_iff] at hq₁ hq₂ hqs
    rw [allQueriesSatisfy_query_bind_iff] at htgt hcok
    have hout' : ∀ u, ∀ kx ∈ support (k u), OK kx := fun u kx h =>
      hout kx ((mem_support_bind_iff _ _ _).2 ⟨u, by simp, h⟩)
    rcases t with n | (q₀ | bs) | x
    · rw [tgtImplF_unif_bind, bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (hpl n), fun u => ?_⟩
      simp only [hpl n, ↓reduceIte]
      exact ih u q₁ q₂ qs s (hq₁.2 u) (hq₂.2 u) (hqs.2 u) (htgt.2 u) (hcok.2 u) (hout' u) hs
    · rw [tgtImplF_raw_bind, bind_assoc, isQueryBoundP_query_bind_iff]
      by_cases hp : p (.inr (q₀, P q₀.2))
      · have hf : fr q₀ = true := hraw q₀ hp
        have hpos : 0 < q₁ := hq₁.1.resolve_left (fun h => h (by simpa [rawB] using hf))
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        have h1 : IsQueryBoundP (k u) (fun i => rawB (X := X) fr i = true) (q₁ - 1) := by
          have := hq₁.2 u
          rw [ite_eq_left (show rawB (X := X) fr (.inr (.inl (.inl q₀))) = true from hf)] at this
          exact this
        have := ih u (q₁ - 1) q₂ qs s h1 (hq₂.2 u) (hqs.2 u) (htgt.2 u) (hcok.2 u) (hout' u) hs
        simp only [hp, ↓reduceIte]
        refine this.mono ?_
        omega
      · refine ⟨Or.inl hp, fun u => ?_⟩
        have h1 : IsQueryBoundP (k u) (fun i => rawB (X := X) fr i = true) q₁ :=
          (hq₁.2 u).mono (by split <;> omega)
        simp only [hp, ↓reduceIte]
        exact ih u q₁ q₂ qs s h1 (hq₂.2 u) (hqs.2 u) (htgt.2 u) (hcok.2 u) (hout' u) hs
    · rw [tgtImplF_chain_bind, bind_assoc]
      have hc0 := hch bs hcok.1
      by_cases hf : fc bs = true
      · have hpos : 0 < q₂ := hq₂.1.resolve_left (fun h => h (by simpa [chB] using hf))
        have h2 : ∀ u, IsQueryBoundP (k u) (fun i => chB (St := St) (X := X) fc i = true)
            (q₂ - 1) := fun u => by
          have := hq₂.2 u
          rw [ite_eq_left (show chB (St := St) (X := X) fc (.inr (.inl (.inr bs))) = true from hf)]
            at this
          exact this
        simp only [hf, ↓reduceIte] at hc0
        refine (isQueryBoundP_bind hc0 fun u _ =>
          ih u q₁ (q₂ - 1) qs s (hq₁.2 u) (h2 u) (hqs.2 u) (htgt.2 u) (hcok.2 u) (hout' u)
            hs).mono ?_
        have : q₂ * w = (q₂ - 1) * w + w := by
          rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left w hpos)]
        omega
      · have h2 : ∀ u, IsQueryBoundP (k u) (fun i => chB (St := St) (X := X) fc i = true) q₂ :=
          fun u => (hq₂.2 u).mono (by split <;> omega)
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hc0
        refine (isQueryBoundP_bind hc0 fun u _ =>
          ih u q₁ q₂ qs s (hq₁.2 u) (h2 u) (hqs.2 u) (htgt.2 u) (hcok.2 u) (hout' u) hs).mono ?_
        omega
    · have hpos : 0 < qs := hqs.1.resolve_left (fun h => h rfl)
      have h0 : IsQueryBoundP (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + mS St Blk) K)
          p 0 :=
        IsQueryBoundP.of_imp (p' := fun t => t.isRight)
          (fun t ht => by
            rcases t with n | t
            · exact absurd ht (hpl n)
            · rfl)
          (isQueryBoundP_liftM_isRight _)
      rw [tgtImplF_tgt_bind, bind_assoc]
      refine (isQueryBoundP_bind (m := q₁ + q₂ * w + (qs + s.length + 1) * c) h0 fun k' _ =>
        (ih k' q₁ q₂ (qs - 1) (s ++ [(k', x)]) (hq₁.2 k') (hq₂.2 k') (hqs.2 k') (htgt.2 k')
          (hcok.2 k') (hout' k')
          (fun kx h => by
            rcases List.mem_append.mp h with h | h
            · exact hs kx h
            · rw [List.mem_singleton.mp h]; exact htgt.1 k')).mono ?_).mono (by omega)
      simp only [List.length_append, List.length_cons, List.length_nil]
      have : qs - 1 + (s.length + (0 + 1)) + 1 = qs + s.length + 1 := by omega
      rw [this]

/-- **Query bound of the experiment with fine marking.**  `fr`-raw queries cost at most one
`p`-query each (other raw queries none), `fc`-chain queries at most `w` (other chain queries
none), each hash of the final check at most `c`. -/
theorem gameProgF_bound [SampleableType K] [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] (hpl : ∀ n, ¬ p (.inl n)) (P : Blk → Bool)
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (c : ℕ) (OK : K × X → Prop)
    (hOK : ∀ kx, OK kx → IsQueryBoundP (hashM IV ib ob od kx) p c)
    (fr : St × Blk → Bool) (fc : List Blk → Bool) (w : ℕ) (OKc : List Blk → Prop)
    (hraw : ∀ q : St × Blk, p (.inr (q, P q.2)) → fr q = true)
    (hch : ∀ bs, OKc bs → IsQueryBoundP (mdP P IV bs) p (if fc bs = true then w else 0))
    (A : OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X K)) (K × X)) (q₁ q₂ qs : ℕ)
    (hq₁ : IsQueryBoundP A (fun i => rawB (X := X) fr i = true) q₁)
    (hq₂ : IsQueryBoundP A (fun i => chB (St := St) (X := X) fc i = true) q₂)
    (hqs : IsQueryBoundP A (fun i => isTgtF (St := St) (Blk := Blk) (X := X) i = true) qs)
    (htgt : AllQueriesSatisfy A (tgtOKF (St := St) (Blk := Blk) OK))
    (hcok : AllQueriesSatisfy A (chOK (St := St) (X := X) OKc))
    (hout : ∀ kx ∈ support A, OK kx) :
    IsQueryBoundP (gameProgF P IV ib ob od idx A) p (q₁ + q₂ * w + (qs + 1) * c) := by
  have h := gameProgF_bound_aux hpl P IV ib ob od idx c OK hOK fr fc w OKc hraw hch A q₁ q₂ qs []
    hq₁ hq₂ hqs htgt hcok hout (by simp)
  simpa [gameProgF] using h

end Bounds

end Ideal.Itsr

#print axioms Ideal.Itsr.simulateQ_gameProgF
#print axioms Ideal.Itsr.win_logF
#print axioms Ideal.Itsr.itsr_le_fine
#print axioms Ideal.Itsr.gameProgF_bound
