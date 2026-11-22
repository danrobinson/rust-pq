import Ct.Rel
import Mathlib.Tactic.CasesM
import Ct.Facts
import Ct.Arith

/-!
# Lockstep tactic for `Rel`

`ct_step` performs one step of the relational proof of `Rel X X' R` where `X` and `X'` are the
same instrumented program text applied to (possibly) different arguments:

* `bind m f` / `bind m' f'`:
  1. if `m` and `m'` are syntactically the same computation (it only depends on public data):
     `Rel.bind_refl` (same trace, same result: the bound variable is shared by both sides);
  2. if `m` is a call with a `@[ct_rel]` lemma: that lemma (`Rel.bind_of`), whose
     hypotheses are tried with `ct_side` and otherwise left as goals;
  3. an instrumented primitive (`Leak.prim t r` vs `Leak.prim t' r'`): `Rel.bind_prim`, with
     the side goal `t = t'` (equal indices / lengths / ranges) tried with `ct_side`;
  4. a lifted `Result` operation (no events): `Rel.bind_liftM`;
  5. `pure`/`lift`: `Rel.bind_pure`;
  6. otherwise (e.g. a nested `cond` whose result is secret): `Rel.bind` with the trivial
     intermediate relation, and the first computation is stepped on its own;
* a call in tail position with a `@[ct_rel]` lemma: the lemma, then `Rel.mono`;
* a primitive in tail position: `Rel.prim`, then `Rel.mono`;
* `cond c a b` / `cond c' a' b'`: `Rel.cond`, with the side goal `decide c = decide c'`;
* `pure a` / `pure b`: `Rel.pure`, leaving the postcondition;
* tuple destructuring `uncurry f p` / `uncurry f' p'`: both pairs are destructured (variables:
  by cases; explicit pairs, e.g. from `Array.to_slice_mut`: by projection);
* `let`: zeta-reduction (and `let (s, back) := Array.to_slice_mut a`: destructured).

Side conditions are tried with `ct_side`, which may use `ct_facts` (lengths of the results of
`push`, `extend_from_slice`, `copy_from_slice`, range indexing, the back function of
`Slice.index_mut_usize`, and of checked arithmetic, read
off the hypotheses `prim args = ok a`). After each step the hypotheses on the new variables are
split and `subst`ed. `ct_steps` repeats
`ct_step` on all goals. The goals it leaves are exactly the conditions that public values agree
(tests, indices, lengths) that `ct_side` could not prove, and the final postconditions.
-/

open Lean Meta Elab Tactic
open Aeneas Aeneas.Std

namespace Ct

/-- Forward facts: for every hypothesis `h : prim args = ok a` about a primitive with a known
result length (or arithmetic result), add the fact. -/
elab "ct_facts" : tactic => withMainContext do
  let facts := [``Ct.Facts.push_ok, ``Ct.Facts.extend_ok, ``Ct.Facts.copy_ok,
    ``Ct.Facts.range_ok, ``Ct.Facts.slice_index_mut_ok, ``Ct.Facts.array_range_index_mut_ok,
    ``Ct.Facts.array_range_index_ok, ``Ct.Arith.add_ok, ``Ct.Arith.sub_ok, ``Ct.Arith.mul_ok]
  let mut g ← getMainGoal
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    for F in facts do
      try
        let e ← mkAppM F #[ld.toExpr]
        let t ← inferType e
        let (_, g') ← (← g.assert (← mkFreshUserName `fact) t e).intro1P
        g := g'
      catch _ => pure ()
  replaceMainGoal [g]

/-- Discharge a side condition (equality of public values, of traces, of tests). -/
macro "ct_side" : tactic => `(tactic| first
  | rfl
  | assumption
  | trivial
  | (simp only [Aeneas.Std.Array.length_to_slice, Ct.Facts.deref_length]; done)
  | (simp only [List.cons.injEq, Event.index.injEq, Event.range.injEq, Event.copy.injEq,
      Event.extend.injEq, Event.div.injEq, Event.rem.injEq, Event.cmp.injEq, and_true,
      true_and, decide_eq_decide] at *; done)
  | (simp_all; done)
  | omega
  | (ct_facts; simp_all; done)
  | (ct_facts; simp_all; omega))

/-- Split conjunctions in hypotheses and substitute equalities of variables. -/
macro "ct_clean" : tactic => `(tactic| ((try casesm* _ ∧ _) <;> (try subst_vars)))

/-- Try `ct_side` on `g`; return whether it closed it. -/
def trySide (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try
    let gs ← Tactic.run g (evalTactic (← `(tactic| ct_side)))
    if gs.isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

/-- Apply a `@[ct_rel]` lemma to the computation in head position: the first computation of a
`bind` (rule `Rel.bind_of`; the continuation's variables are then introduced), or the whole
computation (rule `Rel.mono`; the implication between postconditions is tried with `ct_side`
and left as a goal otherwise). The lemma's hypotheses are tried with `ct_side`. -/
elab "ct_call" : tactic => do
  let lemmas ← Lean.labelled `ct_rel
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let isBind ← match_expr ty with
    | Ct.Rel _ _ m _ _ => pure ((← whnfR m).isAppOfArity ``Ct.Leak.bind 4)
    | _ => pure false
  let mut errs : Array MessageData := #[]
  for L in lemmas do
    let s ← saveState
    try
      let rule := if isBind then ``Rel.bind_of else ``Rel.mono
      let gs ← g.apply (← mkConstWithFreshMVarLevels rule)
      let hR :: hk :: _ := gs | throwError "ct_call: unexpected goals"
      let sides ← withReducible (hR.apply (← mkConstWithFreshMVarLevels L))
      let mut rest := #[]
      for sg in sides do
        unless ← trySide sg do rest := rest.push sg
      let (_, hk') ← hk.introN 3
      let mut remaining := rest.toList
      if isBind then
        remaining := remaining ++ [hk']
      else
        unless ← trySide hk' do remaining := remaining ++ [hk']
      remaining ← remaining.filterM fun g => return !(← g.isAssigned)
      replaceMainGoal remaining
      return
    catch e =>
      errs := errs.push m!"{L}: {e.toMessageData}"
      s.restore
  throwError m!"ct_call: no @[ct_rel] lemma applies" ++
    (if errs.size ≤ 3 then m!"\n" ++ MessageData.joinSep errs.toList "\n" else m!"")

/-- Tuple destructuring: `Rel (uncurry f p) (uncurry f' p') S` with `p`, `p'` variables. -/
elab "ct_uncurry" : tactic => do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (m, m') := (match_expr ty with
    | Ct.Rel _ _ m m' _ => some (m, m')
    | _ => none) | throwError "ct_uncurry: not a Rel goal"
  unless m.isAppOfArity ``Aeneas.Std.uncurry 5 && m'.isAppOfArity ``Aeneas.Std.uncurry 5 do
    throwError "ct_uncurry: not uncurry"
  let p := m.appArg!
  let p' := m'.appArg!
  unless p.isFVar && p'.isFVar do throwError "ct_uncurry: not variables"
  if p == p' then
    let gs ← g.cases p.fvarId!
    let [c] := gs.toList | throwError "ct_uncurry"
    replaceMainGoal [c.mvarId]
  else
    let gs ← g.cases p.fvarId!
    let [c] := gs.toList | throwError "ct_uncurry"
    let p'' := c.subst.apply p'
    let gs' ← c.mvarId.cases p''.fvarId!
    let [c'] := gs'.toList | throwError "ct_uncurry"
    replaceMainGoal [c'.mvarId]
  evalTactic (← `(tactic|
    (simp only [Aeneas.Std.uncurry_apply_pair, Prod.mk.injEq] at *; ct_clean)))

/-- One lockstep step. -/
macro "ct_step" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (ct_call; try ct_clean)
  | (with_reducible refine Rel.bind_prim (by ct_side) (fun _ _ _ _ => ?_))
  | (with_reducible refine Rel.bind_prim ?_ (fun _ _ _ _ => ?_))
  | (with_reducible refine Rel.bind_liftM (fun _ _ _ _ => ?_))
  | (with_reducible refine Rel.bind_pure ?_)
  | (with_reducible refine Rel.cond (by ct_side) (fun _ _ => ?_) (fun _ _ => ?_))
  | (with_reducible refine Rel.cond ?_ (fun _ _ => ?_) (fun _ _ => ?_))
  | (with_reducible refine Rel.pure ?_)
  | (with_reducible refine Rel.mono (Rel.prim (by ct_side)) (fun _ _ _ => ?_); try ct_clean)
  | (with_reducible refine Rel.mono (Rel.prim ?_) (fun _ _ _ => ?_); try ct_clean)
  | (with_reducible refine Rel.bind (R := fun _ _ => True) ?_ (fun _ _ _ => ?_))
  | ct_uncurry
  | (with_reducible refine Rel.uncurry ?_; dsimp only)
  | fail_if_no_progress dsimp +zetaHave only [Aeneas.Std.Array.to_slice_mut])

/-- Repeat `ct_step` on all goals. -/
macro "ct_steps" : tactic => `(tactic| repeat' ct_step)

end Ct
