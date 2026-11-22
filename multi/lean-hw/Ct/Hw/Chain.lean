import Ct.Hw.Lanes

/-!
# Constant time: `sha256::hw::chain_all` and `sha256::hw::chain_blocks` (generic in `N`)

Adapted from the main tree's `../../lean-hw/Ct/Hw/Chain.lean` (copied and edited, not linked:
every function of this tree's kernel takes the hash length `N`; `enter` also loads bytes 38..54
for `N > 16` and `leave` writes them back).

The kernel keeps up to four blocks in flight in `slots`. Which block enters which slot when,
and how many steps each `run` takes, is decided by the step ranges `start`/`end` (public) and
by the slots' counters, which are computed from them: the slots' public parts `t`, `end`,
`lane` (`SlotsRel`). The values stay in vector registers.

The one place where block contents reach the trace is `enter`: it compares the first 16 bytes
of the block it starts (its *head*) with those of the block it last computed the first round
for, `first.head`, and recomputes the first round if they differ; the trace has the length of
their common prefix and the outcome. So the two runs' blocks must have the same heads
(`HeadsEq`), and then the cache (`first.known`, `first.head`) is the same in both runs too.

For every `N` the head is the same bytes `block[0..16]` (the Rust code copies `&block[0..16]`
whatever `N` is): the first 16 of the 22 bytes of the compressed address, which precede the
step counter (bytes 18..22) and the value (bytes 22..22 + N). The value's position and length
change with `N`; the head does not. `leave` writes bytes 18..22, 22..38 and, for `N > 16`,
38..54, all at or after byte 16, so the heads are again equal afterwards (`HeadsEq` is the
loop invariant, for every `N`). The other branches added for `N > 16` are on `N` itself.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Hw

open slhdsa_leak

/-- The cache of the first round: its public part. -/
def FirstRel (f f' : slhdsa.sha256.hw.First) : Prop := f.known = f'.known ∧ f.head = f'.head

theorem store_be_ok {b r : Slice U8} {at' : Usize} {v : Vec}
    (h : slhdsa.sha256.hw.arm.store_be b at' v = .ok r) :
    r.val = b.val.setSlice! at'.val (slhdsa.sha256.hw.arm.be_bytes v) := by
  simp only [slhdsa.sha256.hw.arm.store_be] at h
  split at h
  · split at h
    · simp only [Result.ok.injEq] at h; subst h; simp [Slice.setSlice!]
    · simp at h
  · simp at h

theorem take_ite_setSlice (c : Prop) [Decidable c] (l s : List U8) (i : Nat) (hi : 16 ≤ i) :
    List.take 16 (if c then l.setSlice! i s else l) = l.take 16 := by
  split
  · exact Heads.head_setSlice s hi
  · rfl

/-- Storing a vector at a position `≥ 16` of two blocks with the same head, through
`to_slice_mut` and its back function: the heads stay equal. -/
theorem headEq_of_store_be {a a' : Block} {r r' : Slice U8} {at' : Usize} {v v' : Vec}
    (h1 : slhdsa.sha256.hw.arm.store_be a.to_slice at' v = .ok r)
    (h2 : slhdsa.sha256.hw.arm.store_be a'.to_slice at' v' = .ok r')
    (hat : 16 ≤ at'.val) (h : HeadEq a a') :
    HeadEq (Aeneas.Std.Array.from_slice a r) (Aeneas.Std.Array.from_slice a' r') := by
  have e1 := store_be_ok h1
  have e2 := store_be_ok h2
  simp only [HeadEq, head] at h ⊢
  rw [Heads.from_slice_val, Heads.from_slice_val, e1, e2]
  simp only [Aeneas.Std.Array.val_to_slice, List.length_setSlice!]
  rw [take_ite_setSlice _ _ _ _ hat, take_ite_setSlice _ _ _ _ hat]
  exact h

/-- `ct_step`, but the conditional of `leave` (on `N > 16`, public) is stepped keeping the
heads of its result, a block. -/
macro "ct_step_l" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Aeneas.Std.Array Aeneas.Std.U8 64#usize) => Ct.HeadEq x y) ?_ (fun _ _ _ => ?_))
  | ct_step)

/-- `leave`: writes the step counter (bytes 18..22), the value (bytes 22..38) and, for
`N > 16`, bytes 38..54 at fixed positions; the head is unchanged. -/
@[ct_rel] theorem leave (N : Usize) (slot slot' : Slot) (block block' : Array U8 64#usize)
    (h : HeadEq block block') :
    Rel (sha256.hw.leave N slot block) (sha256.hw.leave N slot' block')
      (fun r r' => HeadEq r r') := by
  unfold sha256.hw.leave
  repeat' ct_step_l
  all_goals first
    | (apply headEq_of_store_be (by assumption) (by assumption) (by simp)
       first | assumption | (heads_core; done))
    | (heads_core; done)

theorem array_range_index_val {N : Usize} {a : Array U8 N} {r : core.ops.range.Range Usize}
    {s : Slice U8}
    (h : Aeneas.Std.core.array.Array.index
      (Aeneas.Std.core.ops.index.IndexSlice (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice U8))
      a r = .ok s) :
    s.val = a.val.slice r.start.val r.end.val := by
  simp only [Aeneas.Std.core.array.Array.index, Aeneas.Std.core.ops.index.IndexSlice,
    Aeneas.Std.core.slice.index.Slice.index,
    Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice,
    Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h; simp [Array.to_slice]
  · simp at h

/-- The head of a block, as `enter` copies it: the same in both runs. -/
theorem head_range {b b' : Array U8 64#usize} (h : HeadEq b b') :
    Rel (slhdsa_leak.core.array.Array.index
        (slhdsa_leak.core.ops.index.IndexSlice (slhdsa_leak.core.slice.index.SliceIndexRangeUsizeSlice U8))
        b { start := 0#usize, «end» := 16#usize })
      (slhdsa_leak.core.array.Array.index
        (slhdsa_leak.core.ops.index.IndexSlice (slhdsa_leak.core.slice.index.SliceIndexRangeUsizeSlice U8))
        b' { start := 0#usize, «end» := 16#usize })
      (fun x x' => x = x') := by
  intro s t s' t' h1 h2
  obtain ⟨e1, rfl⟩ := Leak.prim_eq_ok.mp h1
  obtain ⟨e2, rfl⟩ := Leak.prim_eq_ok.mp h2
  refine ⟨by simp [Array.to_slice], ?_⟩
  apply Slice.ext
  rw [array_range_index_val e1, array_range_index_val e2]
  simp only [HeadEq, head] at h
  simpa [List.slice] using h

/-- `ct_step`, but the nested conditional of `enter` (on the cache) is stepped keeping the
public part of its result: the new `known` flag and cached head. -/
macro "ct_step_e" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Bool × Aeneas.Std.Array U8 16#usize × Ct.Hw.Vec × Ct.Hw.Vec) => x.1 = y.1 ∧ x.2.1 = y.2.1) ?_ (fun _ _ _ => ?_))
  | ct_step)

section
attribute [local ct_rel] head_range

/-- `enter`: the trace depends on the block only through its head, and on the cache only
through its public part. -/
@[ct_rel] theorem enter (N : Usize) (state state' : Array U32 8#usize)
    (block block' : Array U8 64#usize)
    (t e : U32) (lane : Usize) (first first' : slhdsa.sha256.hw.First) (hb : HeadEq block block')
    (hf : FirstRel first first') :
    Rel (sha256.hw.enter N state block t e lane first)
      (sha256.hw.enter N state' block' t e lane first')
      (fun r r' => pub r.1 = pub r'.1 ∧ FirstRel r.2 r'.2) := by
  obtain ⟨hk, hh⟩ := hf
  unfold sha256.hw.enter
  repeat' ct_step_e
  all_goals simp_all [pub, FirstRel]

end

/-- Reading a slot, the public fields separately (for the lockstep tactic). -/
theorem slots_index' {a a' : Array Slot 4#usize} (h : SlotsRel a a') (j : Usize) :
    Rel (slhdsa_leak.Array.index_usize a j) (slhdsa_leak.Array.index_usize a' j)
      (fun s s' => s.t = s'.t ∧ s.«end» = s'.«end» ∧ s.lane = s'.lane) :=
  (slots_index h j).mono fun _ _ h => pub_eq h

/-- A subtraction of public values. -/
theorem sub_rel {x x' y y' : U32} (hx : x = x') (hy : y = y') :
    Rel (liftM (x - y) : Ct.Leak U32) (liftM (x' - y') : Ct.Leak U32) (fun a b => a = b) := by
  subst hx hy
  exact (Rel.refl _).mono fun _ _ h => h.1

theorem heads_getElem {l l' : List Block} (h : HeadsEq l l') (i : Nat) (hi : i < l.length) :
    HeadEq l[i]! l'[i]! := by
  have hi' : i < l'.length := Heads.length_eq h ▸ hi
  have e := List.getElem_of_eq h (i := i) (by simpa [heads] using hi)
  simp only [heads, List.getElem_map] at e
  have g : l[i]! = l[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have g' : l'[i]! = l'[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  rw [g, g']; exact e

/-- A block borrowed from the blocks: same head in both runs. -/
theorem head_of_index_mut {s s' : Slice Block} (h : HeadsEq s.val s'.val) {i : Usize}
    {x x' : Block} {back back' : Block → Slice Block}
    (h1 : Aeneas.Std.Slice.index_mut_usize s i = .ok (x, back))
    (h2 : Aeneas.Std.Slice.index_mut_usize s' i = .ok (x', back')) : HeadEq x x' := by
  obtain ⟨rfl, hi, -⟩ := Heads.slice_index_mut_ok h1
  obtain ⟨rfl, -, -⟩ := Heads.slice_index_mut_ok h2
  exact heads_getElem h _ hi

theorem head_of_index {s s' : Slice Block} (h : HeadsEq s.val s'.val) {i : Usize}
    {x x' : Block}
    (h1 : Aeneas.Std.Slice.index_usize s i = .ok x)
    (h2 : Aeneas.Std.Slice.index_usize s' i = .ok x') : HeadEq x x' := by
  obtain ⟨rfl, hi⟩ := Heads.slice_index_ok h1
  obtain ⟨rfl, -⟩ := Heads.slice_index_ok h2
  exact heads_getElem h _ hi

/-- Borrowing a block (public index): same heads, and putting back blocks with the same heads
gives slices with the same heads. -/
theorem blocks_index_mut {s s' : Slice Block} (h : HeadsEq s.val s'.val) {i i' : Usize}
    (hi : i = i') :
    Rel (slhdsa_leak.Slice.index_mut_usize s i) (slhdsa_leak.Slice.index_mut_usize s' i')
      (fun p q => HeadEq p.1 q.1 ∧ ∀ y y', HeadEq y y' → HeadsEq (p.2 y).val (q.2 y').val) := by
  subst hi
  intro p t q t' h1 h2
  obtain ⟨e1, rfl⟩ := Leak.prim_eq_ok.mp h1
  obtain ⟨e2, rfl⟩ := Leak.prim_eq_ok.mp h2
  refine ⟨by rw [Heads.slice_length_eq h], head_of_index_mut h e1 e2, fun y y' hy => ?_⟩
  obtain ⟨-, -, b1⟩ := Heads.slice_index_mut_ok e1
  obtain ⟨-, -, b2⟩ := Heads.slice_index_mut_ok e2
  rw [b1, b2]
  exact Heads.set _ h hy

/-- Reading a block. -/
theorem blocks_index {s s' : Slice Block} (h : HeadsEq s.val s'.val) (i : Usize) :
    Rel (slhdsa_leak.Slice.index_usize s i) (slhdsa_leak.Slice.index_usize s' i)
      (fun x x' => HeadEq x x') := by
  intro p t q t' h1 h2
  obtain ⟨e1, rfl⟩ := Leak.prim_eq_ok.mp h1
  obtain ⟨e2, rfl⟩ := Leak.prim_eq_ok.mp h2
  exact ⟨by rw [Heads.slice_length_eq h], head_of_index h e1 e2⟩

section
attribute [local ct_rel] slots_index' sub_rel blocks_index_mut blocks_index

theorem chain_all_loop0_loop0_body (slots slots' : Array Slot 4#usize) (n : Usize) (r : U32)
    (j : Usize) (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop0.body slots n r j)
      (sha256.hw.chain_all_loop0_loop0.body slots' n r j)
      (CFRel (fun a b => a = b) (fun a b => a = b)) := by
  unfold sha256.hw.chain_all_loop0_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem chain_all_loop0_loop0 (slots slots' : Array Slot 4#usize) (n : Usize) (r : U32)
    (j : Usize) (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop0 slots n r j)
      (sha256.hw.chain_all_loop0_loop0 slots' n r j) (fun a b => a = b) := by
  unfold sha256.hw.chain_all_loop0_loop0
  refine Rel.loop (fun a b => a = b) ?_ rfl
  rintro ⟨x, i⟩ _ rfl
  exact chain_all_loop0_loop0_body slots slots' n x i h

theorem chain_all_loop0_loop2_body (slots slots' : Array Slot 4#usize) (n : Usize) (r : U32)
    (j : Usize) (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop2.body slots n r j)
      (sha256.hw.chain_all_loop0_loop2.body slots' n r j)
      (CFRel (fun a b => a = b) (fun a b => a = b)) := by
  unfold sha256.hw.chain_all_loop0_loop2.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem chain_all_loop0_loop2 (slots slots' : Array Slot 4#usize) (n : Usize) (r : U32)
    (j : Usize) (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop2 slots n r j)
      (sha256.hw.chain_all_loop0_loop2 slots' n r j) (fun a b => a = b) := by
  unfold sha256.hw.chain_all_loop0_loop2
  refine Rel.loop (fun a b => a = b) ?_ rfl
  rintro ⟨x, i⟩ _ rfl
  exact chain_all_loop0_loop2_body slots slots' n x i h

/-- The invariant of the loops that retire finished slots. -/
def RetireRel (p q : Slice Block × Array Slot 4#usize × Usize × Usize) : Prop :=
  HeadsEq p.1.val q.1.val ∧ SlotsRel p.2.1 q.2.1 ∧ p.2.2 = q.2.2

def RetireOut (p q : Slice Block × Array Slot 4#usize × Usize) : Prop :=
  HeadsEq p.1.val q.1.val ∧ SlotsRel p.2.1 q.2.1 ∧ p.2.2 = q.2.2

theorem chain_all_loop0_loop1_body (N n : Usize) (blocks blocks' : Slice Block)
    (slots slots' : Array Slot 4#usize) (k j : Usize) (hb : HeadsEq blocks.val blocks'.val)
    (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop1.body N n blocks slots k j)
      (sha256.hw.chain_all_loop0_loop1.body N n blocks' slots' k j)
      (CFRel RetireRel RetireOut) := by
  have hl := Heads.slice_length_eq hb
  unfold sha256.hw.chain_all_loop0_loop1.body
  ct_steps
  all_goals simp only [CFRel_cont_cont, CFRel_done_done, RetireRel, RetireOut]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | assumption
    | rfl
    | (apply_assumption <;> assumption)
    | slots_tac

@[ct_rel] theorem chain_all_loop0_loop1 (N : Usize) (blocks blocks' : Slice Block)
    (slots slots' : Array Slot 4#usize) (n k j : Usize) (hb : HeadsEq blocks.val blocks'.val)
    (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop1 N blocks slots n k j)
      (sha256.hw.chain_all_loop0_loop1 N blocks' slots' n k j)
      (fun p q => HeadsEq p.1.val q.1.val ∧ SlotsRel p.2.1 q.2.1 ∧ p.2.2 = q.2.2) := by
  unfold sha256.hw.chain_all_loop0_loop1
  refine Rel.loop RetireRel ?_ ⟨hb, h, rfl⟩
  rintro ⟨b, sl, k1, j1⟩ ⟨b', sl', k1', j1'⟩ ⟨hb1, hs1, he⟩
  obtain ⟨rfl, rfl⟩ : k1 = k1' ∧ j1 = j1' := by simpa using he
  exact chain_all_loop0_loop1_body N n b b' sl sl' k1 j1 hb1 hs1

theorem chain_all_loop0_loop3_body (N n : Usize) (blocks blocks' : Slice Block)
    (slots slots' : Array Slot 4#usize) (k j : Usize) (hb : HeadsEq blocks.val blocks'.val)
    (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop3.body N n blocks slots k j)
      (sha256.hw.chain_all_loop0_loop3.body N n blocks' slots' k j)
      (CFRel RetireRel RetireOut) := by
  have hl := Heads.slice_length_eq hb
  unfold sha256.hw.chain_all_loop0_loop3.body
  ct_steps
  all_goals simp only [CFRel_cont_cont, CFRel_done_done, RetireRel, RetireOut]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | assumption
    | rfl
    | (apply_assumption <;> assumption)
    | slots_tac

@[ct_rel] theorem chain_all_loop0_loop3 (N : Usize) (blocks blocks' : Slice Block)
    (slots slots' : Array Slot 4#usize) (n k j : Usize) (hb : HeadsEq blocks.val blocks'.val)
    (h : SlotsRel slots slots') :
    Rel (sha256.hw.chain_all_loop0_loop3 N blocks slots n k j)
      (sha256.hw.chain_all_loop0_loop3 N blocks' slots' n k j)
      (fun p q => HeadsEq p.1.val q.1.val ∧ SlotsRel p.2.1 q.2.1 ∧ p.2.2 = q.2.2) := by
  unfold sha256.hw.chain_all_loop0_loop3
  refine Rel.loop RetireRel ?_ ⟨hb, h, rfl⟩
  rintro ⟨b, sl, k1, j1⟩ ⟨b', sl', k1', j1'⟩ ⟨hb1, hs1, he⟩
  obtain ⟨rfl, rfl⟩ : k1 = k1' ∧ j1 = j1' := by simpa using he
  exact chain_all_loop0_loop3_body N n b b' sl sl' k1 j1 hb1 hs1

/-- `ct_step` for `chain_all`'s main loop: the nested conditionals that pick a slot array, or
a new (slots, cache, count), are stepped with the public parts kept. -/
macro "ct_step_c" : tactic => `(tactic| first
  | (with_reducible refine Rel.bind_refl (fun _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Aeneas.Std.Array Ct.Hw.Slot 4#usize) => Ct.Hw.SlotsRel x y) ?_ (fun _ _ _ => ?_))
  | (with_reducible refine Rel.bind (m := Ct.Leak.cond _ _ _) (R := fun (x y : Aeneas.Std.Array Ct.Hw.Slot 4#usize × slhdsa.sha256.hw.First × Usize) => Ct.Hw.SlotsRel x.1 y.1 ∧ Ct.Hw.FirstRel x.2.1 y.2.1 ∧ x.2.2 = y.2.2) ?_ (fun _ _ _ => ?_))
  | ct_step)

/-- The invariant of `chain_all`'s main loop. -/
def MainRel (p q : Slice Block × Array Slot 4#usize × slhdsa.sha256.hw.First × Usize × Usize) :
    Prop :=
  HeadsEq p.1.val q.1.val ∧ SlotsRel p.2.1 q.2.1 ∧ FirstRel p.2.2.1 q.2.2.1 ∧ p.2.2.2 = q.2.2.2

theorem chain_all_loop0_body (N : Usize) (state state' : Array U32 8#usize) (start e : Slice U32)
    (blocks blocks' : Slice Block) (slots slots' : Array Slot 4#usize)
    (first first' : slhdsa.sha256.hw.First) (n next : Usize)
    (hb : HeadsEq blocks.val blocks'.val) (h : SlotsRel slots slots') (hf : FirstRel first first') :
    Rel (sha256.hw.chain_all_loop0.body N state start e blocks slots first n next)
      (sha256.hw.chain_all_loop0.body N state' start e blocks' slots' first' n next)
      (CFRel MainRel (fun p q => HeadsEq p.val q.val)) := by
  have hl := Heads.slice_length_eq hb
  unfold sha256.hw.chain_all_loop0.body
  simp only [(Ct.Facts.slice_len_congr hl).symm]
  repeat' ct_step_c
  all_goals (try simp only [CFRel_cont_cont, CFRel_done_done, MainRel])
  all_goals (repeat' apply And.intro)
  all_goals first
    | assumption
    | rfl
    | slots_tac
    | (simp_all [FirstRel]; done)

@[ct_rel] theorem chain_all_loop0 (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice Block)
    (start e : Slice U32) (slots slots' : Array Slot 4#usize)
    (first first' : slhdsa.sha256.hw.First) (n next : Usize)
    (hb : HeadsEq blocks.val blocks'.val) (h : SlotsRel slots slots') (hf : FirstRel first first') :
    Rel (sha256.hw.chain_all_loop0 N state blocks start e slots first n next)
      (sha256.hw.chain_all_loop0 N state' blocks' start e slots' first' n next)
      (fun p q => HeadsEq p.val q.val) := by
  unfold sha256.hw.chain_all_loop0
  refine Rel.loop MainRel ?_ ⟨hb, h, hf, rfl⟩
  rintro ⟨b, sl, f, k, j⟩ ⟨b', sl', f', k', j'⟩ ⟨hb1, hs1, hf1, he⟩
  obtain ⟨rfl, rfl⟩ : k = k' ∧ j = j' := by simpa using he
  exact chain_all_loop0_body N state state' start e b b' sl sl' f f' k j hb1 hs1 hf1

/-- `chain_all`: the trace depends on `N`, the step ranges, the number of blocks and the
blocks' heads only. -/
@[ct_rel] theorem chain_all (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice Block)
    (start e : Slice U32) (hb : HeadsEq blocks.val blocks'.val) :
    Rel (sha256.hw.chain_all N state blocks start e)
      (sha256.hw.chain_all N state' blocks' start e)
      (fun p q => HeadsEq p.val q.val) := by
  unfold sha256.hw.chain_all
  ct_steps
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | assumption

/-- `sha256::hw::chain_blocks::<N>`: the test of `N`, the feature test and the length checks
are on public data; for every `N` (in particular 16, 24 and 32, the values for which the kernel
runs) the only precondition on the blocks is that their heads agree. -/
@[ct_rel] theorem hw_chain_blocks (N : Usize) (state state' : Array U32 8#usize)
    (blocks blocks' : Slice Block)
    (start e : Slice U32) (hb : HeadsEq blocks.val blocks'.val) :
    Rel (sha256.hw.chain_blocks N state blocks start e)
      (sha256.hw.chain_blocks N state' blocks' start e)
      (fun p q => p.1 = q.1 ∧ HeadsEq p.2.val q.2.val) := by
  have hl := Heads.slice_length_eq hb
  unfold sha256.hw.chain_blocks
  simp only [(Ct.Facts.slice_len_congr hl).symm]
  ct_steps
  all_goals simp_all

end

end Ct.Hw
