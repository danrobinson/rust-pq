import Ct.Tactic

/-!
# The address part of the blocks of `chain_blocks`

`hash::chain_blocks` works on blocks built by `short_block`/`pair_block`: a 22-byte compressed
address, a 16-byte value at bytes 22..38 and the padding. The hardware kernel of the `hw-sha2`
build keeps a cache of the first rounds keyed on the first 16 bytes of a block, the *head*, and
compares the head of each block it starts with the cached one; the outcome and the length of the
common prefix are in the trace. The head is the layer, tree address, type, key-pair address and
the two high bytes of the chain address: public at every call site.

The constant-time lemma of `chain_blocks` (`Ct/ChainTop.lean`, the same statement in both
builds) therefore requires the two runs' blocks to have the same heads, `heads b = heads b'`,
and guarantees it of its results (it only writes bytes 18..38). This file has the definitions
and the facts used to carry the relation through the callers.
-/

open Aeneas Aeneas.Std

namespace Ct

/-- A block of `chain_blocks`. -/
abbrev Block := Array U8 64#usize

/-- The first 16 bytes of a block. -/
def head (b : Block) : List U8 := b.val.take 16

/-- The heads of a list of blocks. -/
def heads (l : List Block) : List (List U8) := l.map head

/-- The relation of the two runs' blocks: the same heads. (A definition, so that the lockstep
tactics do not rewrite with it.) -/
def HeadsEq (l l' : List Block) : Prop := heads l = heads l'

/-- The relation of two blocks: the same head. -/
def HeadEq (b b' : Block) : Prop := head b = head b'

@[refl] theorem HeadsEq.refl (l : List Block) : HeadsEq l l := rfl

@[refl] theorem HeadEq.refl (b : Block) : HeadEq b b := rfl

namespace Heads

theorem length_eq {l l' : List Block} (h : heads l = heads l') :
    l.length = l'.length := by
  simpa [heads] using congrArg List.length h

theorem slice_length_eq {s s' : Slice Block} (h : heads s.val = heads s'.val) :
    s.length = s'.length := length_eq h

theorem set {l l' : List Block} {x x' : Block} (i : Nat)
    (h : heads l = heads l') (hx : head x = head x') :
    heads (l.set i x) = heads (l'.set i x') := by
  simp only [heads, List.map_set] at *
  rw [h, hx]

/-- Replacing a block by one with the same head. -/
theorem set_self {l : List Block} {x : Block} (i : Nat)
    (hx : head x = head l[i]!) : heads (l.set i x) = heads l := by
  simp only [heads, List.map_set]
  by_cases hi : i < l.length
  · rw [hx]
    have : (l.map head)[i]'(by simpa using hi) = head l[i]! := by
      simp [hi]
    rw [← this, List.set_getElem_self]
  · simp only [not_lt] at hi
    exact List.set_eq_of_length_le (by simpa using hi)

/-- Normal form of the heads of an updated list (for `heads_tac`). -/
theorem heads_set (l : List Block) (i : Nat) (x : Block) :
    heads (l.set i x) = (heads l).set i (x.val.take 16) := by
  simp [heads, List.map_set, head]

theorem set_head_self (l : List Block) (i : Nat) :
    (heads l).set i ((l[i]!).val.take 16) = heads l := by
  have := set_self (l := l) (x := l[i]!) i rfl
  rwa [heads_set] at this

theorem replicate (n : Nat) (b : Array U8 64#usize) :
    heads (List.replicate n b) = List.replicate n (head b) := by
  simp [heads]

theorem take {l l' : List Block} (n : Nat) (h : heads l = heads l') :
    heads (l.take n) = heads (l'.take n) := by
  simp only [heads, List.map_take] at *; rw [h]

theorem drop {l l' : List Block} (n : Nat) (h : heads l = heads l') :
    heads (l.drop n) = heads (l'.drop n) := by
  simp only [heads, List.map_drop] at *; rw [h]

theorem slice {l l' : List Block} (a b : Nat) (h : heads l = heads l') :
    heads (l.slice a b) = heads (l'.slice a b) := by
  unfold List.slice; exact take _ (drop _ h)

theorem app {l l' m m' : List Block} (h : heads l = heads l')
    (hm : heads m = heads m') : heads (l ++ m) = heads (l' ++ m') := by
  simp only [heads, List.map_append] at h hm ⊢; rw [h, hm]

theorem setSlice {l l' m m' : List Block} (i : Nat) (h : heads l = heads l')
    (hm : heads m = heads m') : heads (l.setSlice! i m) = heads (l'.setSlice! i m') := by
  have hl := length_eq h
  have hml := length_eq hm
  simp only [List.setSlice!]
  rw [hl, hml]
  exact app (app (take _ h) (take _ hm)) (drop _ h)

/-! ## Bytes of a block -/

/-- Writing a byte at position `≥ 16` leaves the head. -/
theorem head_set {b : List U8} {i : Nat} (x : U8) (hi : 16 ≤ i) :
    (b.set i x).take 16 = b.take 16 := List.take_set_of_le hi

/-- Writing bytes from position `≥ 16` on leaves the head. -/
theorem head_setSlice {b : List U8} {i : Nat} (s : List U8) (hi : 16 ≤ i) :
    (b.setSlice! i s).take 16 = b.take 16 := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact List.setSlice!_getElem?_prefix _ _ _ _ (by omega)
  · rfl

/-- Writing the same byte below 16 in two blocks with the same head. -/
theorem head_set_same {b b' : List U8} {i : Nat} (x : U8) (h : b.take 16 = b'.take 16) :
    (b.set i x).take 16 = (b'.set i x).take 16 := by
  rw [List.take_set, List.take_set, h]

/-- Two runs write the same byte into the same block of two lists with the same heads. -/
theorem set_byte {l l' : List Block} (h : HeadsEq l l') (i : Nat) {x x' : Block} (j : Nat)
    (y : U8) (hx : x.val = l[i]!.val.set j y) (hx' : x'.val = l'[i]!.val.set j y) :
    HeadsEq (l.set i x) (l'.set i x') := by
  unfold HeadsEq at *
  by_cases hi : i < l.length
  · have hi' : i < l'.length := length_eq h ▸ hi
    refine set i h ?_
    unfold head
    rw [hx, hx']
    apply head_set_same
    have e := List.getElem_of_eq h (i := i) (by simpa [heads] using hi)
    simp only [heads, List.getElem_map, head] at e
    have g : l[i]! = l[i] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have g' : l'[i]! = l'[i] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
    rw [g, g']; exact e
  · have hi' : ¬ i < l'.length := length_eq h ▸ hi
    rw [List.set_eq_of_length_le (by omega), List.set_eq_of_length_le (by omega)]
    exact h

/-! ## Results of primitives (inversion) -/

theorem array_update_ok {α : Type} {n : Usize} {a : Array α n} {i : Usize} {x : α}
    {b : Array α n} (h : Array.update a i x = .ok b) : b.val = a.val.set i.val x := by
  simp only [Array.update] at h
  split at h
  · simp at h
  · simp only [Result.ok.injEq] at h; subst h; simp [Array.from_val]

theorem array_index_ok {α : Type} [Inhabited α] {n : Usize} {a : Array α n} {i : Usize} {x : α}
    (h : Array.index_usize a i = .ok x) : x = a.val[i.val]! ∧ i.val < a.length := by
  simp only [Array.index_usize] at h
  split at h
  · simp at h
  · rename_i y hy
    simp only [Result.ok.injEq] at h; subst h
    simp only [Array.getElem?_Usize_eq, List.getElem?_eq_some_iff] at hy
    obtain ⟨hi, rfl⟩ := hy
    exact ⟨by rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl, hi⟩

theorem slice_index_ok {α : Type} [Inhabited α] {s : Slice α} {i : Usize} {x : α}
    (h : Slice.index_usize s i = .ok x) : x = s.val[i.val]! ∧ i.val < s.length := by
  simp only [Slice.index_usize] at h
  split at h
  · simp at h
  · rename_i y hy
    simp only [Result.ok.injEq] at h; subst h
    simp only [Slice.getElem?_Usize_eq, List.getElem?_eq_some_iff] at hy
    obtain ⟨hi, rfl⟩ := hy
    exact ⟨by rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl, hi⟩

theorem array_index_mut_ok {α : Type} [Inhabited α] {n : Usize} {a : Array α n} {i : Usize} {x : α}
    {back : α → Array α n} (h : Array.index_mut_usize a i = .ok (x, back)) :
    x = a.val[i.val]! ∧ i.val < a.length ∧ ∀ y, (back y).val = a.val.set i.val y := by
  simp only [Array.index_mut_usize, Aeneas.Std.bind_tc_eq, bind_eq_ok] at h
  obtain ⟨y, hy, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h1, h2⟩ := array_index_ok hy
  exact ⟨h1, h2, fun y => Array.set_val_eq _ _ _⟩

theorem slice_index_mut_ok {α : Type} [Inhabited α] {s : Slice α} {i : Usize} {x : α}
    {back : α → Slice α} (h : Slice.index_mut_usize s i = .ok (x, back)) :
    x = s.val[i.val]! ∧ i.val < s.length ∧ ∀ y, (back y).val = s.val.set i.val y := by
  simp only [Slice.index_mut_usize, Aeneas.Std.bind_tc_eq, bind_eq_ok] at h
  obtain ⟨y, hy, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h1, h2⟩ := slice_index_ok hy
  exact ⟨h1, h2, fun y => Slice.set_val_eq _ _ _⟩

theorem array_range_index_mut_ok {α : Type} {N : Usize} {a : Array α N}
    {r : core.ops.range.Range Usize} {s : Slice α} {back : Slice α → Array α N}
    (h : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice α)) a r =
        .ok (s, back)) :
    s.val = a.val.slice r.start.val r.end.val ∧
      ∀ y, (back y).val = a.val.setSlice! r.start.val y.val := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Aeneas.Std.bind_tc_eq] at h
  split at h
  · rw [bind_ok] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [Array.to_slice], fun y => ?_⟩
    rw [Array.from_slice_val _ _ (by simp [Array.to_slice])]
    simp [Array.to_slice]
  · simp at h

theorem from_slice_val {α : Type} {n : Usize} (a : Array α n) (s : Slice α) :
    (Array.from_slice a s).val = if s.val.length = n.val then s.val else a.val := by
  unfold Array.from_slice
  split <;> simp_all

/-- The back function of `to_slice_mut`, on blocks with the same heads. -/
theorem from_slice {n : Usize} {a a' : Array Block n}
    {s s' : Slice Block} (h : HeadsEq a.val a'.val)
    (hs : HeadsEq s.val s'.val) :
    HeadsEq (Array.from_slice a s).val (Array.from_slice a' s').val := by
  unfold HeadsEq at *
  rw [from_slice_val, from_slice_val, length_eq hs]
  split
  · exact hs
  · exact h

/-- Forward facts on the values of successful primitives: for each hypothesis
`prim args = ok r` about an update, an indexing or a range borrow, add the equation for the
value of `r` (and of its back function). -/
elab "heads_facts" : tactic => Lean.Elab.Tactic.withMainContext do
  let facts := [``Ct.Heads.array_update_ok, ``Ct.Heads.array_range_index_mut_ok,
    ``Ct.Heads.array_index_mut_ok, ``Ct.Heads.slice_index_mut_ok, ``Ct.Heads.slice_index_ok,
    ``Ct.Heads.array_index_ok, ``Ct.Facts.copy_ok]
  let mut g ← Lean.Elab.Tactic.getMainGoal
  for ld in ← Lean.getLCtx do
    if ld.isImplementationDetail then continue
    for F in facts do
      try
        let e ← Lean.Meta.mkAppM F #[ld.toExpr]
        let t ← Lean.Meta.inferType e
        let (_, g') ← (← g.assert (← Lean.mkFreshUserName `hfact) t e).intro1P
        g := g'
      catch _ => pure ()
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- Side conditions of `heads_tac`: positions `≥ 16`, indices in bounds. -/
macro "heads_disch" : tactic => `(tactic| first
  | omega
  | (simp; done)
  | (simp; omega)
  | (simp only [List.length_set, and_true]; simp_all [Aeneas.Std.Slice.length]; done)
  | (simp only [List.length_set, and_true]; simp_all [Aeneas.Std.Slice.length]; omega))

/-- Close a goal about heads (of blocks or of lists of blocks) after a lockstep proof: turn
the hypotheses on the primitives into equations for the values, rewrite, and remove the writes
at positions `≥ 16`. -/
macro "heads_core" : tactic => `(tactic| (
  try simp only [Ct.HeadsEq, Ct.HeadEq]
  try simp only [Ct.Leak.erase_prim, Ct.Facts.erase_liftM] at *
  heads_facts
  ct_facts
  try simp only [Aeneas.Std.Slice.set_val_eq, Aeneas.Std.Array.set_val_eq, *]
  try simp (disch := heads_disch) only
    [Ct.head, List.set_set, Ct.Heads.heads_set, Ct.Heads.set_head_self, Ct.Heads.head_set,
      Ct.Heads.head_setSlice, List.set_getElem!_eq, List.length_set, Aeneas.Std.Array.set_val_eq,
      Aeneas.Std.Slice.set_val_eq, *]
  try (simp only [Ct.HeadsEq, Ct.HeadEq, Ct.head, Aeneas.Std.Array.val_to_slice] at *; simp_all; done)))

/-- Sub-slices and their back functions, on blocks with the same heads. -/
theorem slice' {l l' : List Block} (a b : Nat) (h : HeadsEq l l') :
    HeadsEq (l.slice a b) (l'.slice a b) := slice a b h

theorem setSlice' {l l' m m' : List Block} (i : Nat) (h : HeadsEq l l') (hm : HeadsEq m m') :
    HeadsEq (l.setSlice! i m) (l'.setSlice! i m') := setSlice i h hm

/-- Close `HeadsEq` goals on sub-slices (`blocks[0..n]`) and their back functions. -/
macro "heads_range" : tactic => `(tactic| (
  try simp only [Ct.Leak.erase_prim, Ct.Facts.erase_liftM] at *
  heads_facts
  simp only [*]
  first
    | (apply Ct.Heads.slice'; assumption)
    | (apply Ct.Heads.setSlice' <;> assumption)))

/-- Close a goal `HeadsEq _ _` or `HeadEq _ _` (see `heads_core`), also through the back
function of `to_slice_mut`. -/
macro "heads_tac" : tactic => `(tactic| first
  | (heads_range; done)
  | (apply Ct.Heads.from_slice <;> heads_core <;> done)
  | (heads_core; done)
  | (try simp only [Ct.Leak.erase_prim, Ct.Facts.erase_liftM] at *
     heads_facts
     simp only [Aeneas.Std.Array.set_val_eq, Aeneas.Std.Slice.set_val_eq, *]
     apply Ct.Heads.set_byte (by assumption) <;> (try simp only [*]) <;> rfl))

/-- `ct_step`, but a nested conditional whose result is an array of blocks is stepped with the
intermediate relation `HeadsEq` (instead of the trivial one), so that the heads are kept. -/
macro "ct_step_h" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Aeneas.Std.Array Ct.Block _) => Ct.HeadsEq x.val y.val) ?_ (fun _ _ _ => ?_))
  | ct_step)

macro "ct_steps_h" : tactic => `(tactic| repeat' ct_step_h)

end Heads

end Ct
