import Parallel.ForsReducedReceipt
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

def Owner.tree : Owner → Nat | .low first lane _ | .direct first lane _ => first+lane | .reduced t _ => t
def Owner.col : Owner → Nat | .low _ _ c => c | .direct _ _ h | .reduced _ h => h+1

theorem owner_fields (policy : Policy) (a t c : Nat) :
    (owner policy a t c).tree=t ∧ (owner policy a t c).col=c := by
  unfold owner
  split
  · simp [Owner.tree,Owner.col,group_lane]
  · rename_i upper
    split <;> simp [Owner.tree,Owner.col,group_lane] <;> omega

/-- Each constructor names the actual computation used to write one owner’s row. -/
inductive Receipt {N : Usize} (mode : Mode) (d : Data N) : Owner → Result (Cell N) → Prop
  | scalarLow (t depth : U32) (journal : ParallelScalarFors.Journal N) (c : Nat)
      (fallback : mode.policy=.scalar) (tree : t.val<d.p.k.val) (within : c≤depth.val)
      (stop : depth.val=low mode.policy d.p.a.val) :
      Receipt mode d (.low t.val 0 c) (RawFors.scalarLow mode.host d t depth journal c)
  | scalarDirect (t j : U32) (plain : mode.policy≠.three)
      (tree : t.val<d.p.k.val) (height : j.val<d.p.a.val) :
      Receipt mode d (.direct t.val 0 j.val) (RawFors.scalarDirect mode.host d t j)
  | groupedLow (first : U16) (active depth : U8) (col lane : Nat) (grouped : mode.policy≠.scalar)
      (count : active.val=min (d.choices.length-first.val) (width mode.policy))
      (inside : lane<active.val) (height : depth.val=low mode.policy d.p.a.val) (field : col≤depth.val) :
      Receipt mode d (.low first.val lane col) (RawFors.groupedLow mode d first active depth col lane)
  | groupedDirect (first : U16) (active h : U8) (lane : Nat) (linux : mode.policy=.three)
      (count : active.val=min (d.choices.length-first.val) 3) (inside : lane<active.val) (height : h.val<d.p.a.val) :
      Receipt mode d (.direct first.val lane h.val) (RawFors.groupedDirect d first active h lane)
  | scalarMerge (plan : ScalarMerge N) (plain : mode.policy≠.three)
      (targetAt : plan.sub.val=target mode.policy d.p.a.val)
      (ready : plan.Ready mode.host d (decide (mode.policy=.eight))) :
      Receipt mode d (.reduced plan.t.val plan.j.val) (plan.action mode.host d (decide (mode.policy=.eight)))
  | groupedMerge (plan : GroupMerge N) (lane : Nat) (linux : mode.policy=.three) (inside : lane<plan.active.val)
      (targetAt : plan.sub.val=target mode.policy d.p.a.val)
      (count : plan.active.val=min (d.choices.length-plan.first.val) 3) (ready : plan.Ready d) :
      Receipt mode d (.reduced (plan.first.val+lane) plan.j.val) (plan.action d lane)

theorem Receipt.correct {N} {mode : Mode} {d : Data N} {own : Owner} {action : Result (Cell N)}
    (receipt : Receipt mode d own action) (valid : Valid d) : action ⦃ w => Value d own.tree own.col w ⦄ := by
  have depth : low mode.policy d.p.a.val≤d.p.a.val := by unfold low;split <;> exact Nat.min_le_left ..
  cases receipt with
  | scalarLow t D journal c _ tree within stop =>
    simpa [Owner.tree,Owner.col] using scalar_low mode.host d valid t D journal c tree within (stop ▸ depth)
  | scalarDirect t j plain tree height =>
    simpa [Owner.tree,Owner.col] using scalar_direct mode.host d valid t j tree height
  | groupedLow first active D col lane grouped count inside height field =>
    have part : active.val≤d.choices.length-first.val := count ▸ Nat.min_le_left ..
    have capacity : first.val+active.val≤d.choices.length := by omega
    apply grouped_low mode d valid first active D col lane grouped (count ▸ Nat.min_le_right ..) capacity inside (height ▸ depth) _ field
    cases mode with
    | fallback h => exact False.elim (grouped rfl)
    | linux => exact Or.inl rfl
    | apple b | x86 b => right;rw [height];exact Nat.min_le_right ..
  | groupedDirect first active h lane linux count inside height =>
    have part : active.val≤d.choices.length-first.val := count ▸ Nat.min_le_left ..
    exact grouped_direct d valid first active h lane (count ▸ Nat.min_le_right ..) (by omega) inside height
  | scalarMerge m plain sub r => exact m.correct mode.host d valid _ r
  | groupedMerge m lane _ inside sub _ r => exact m.correct d valid lane inside r

/-- The receipt carries only work-item geometry and, for a reduction, its native child writes. -/
structure Packet {N : Usize} (mode : Mode) (d : Data N) where
  action : Nat → Nat → Result (Cell N)
  issued : ∀ t<d.p.k.val, ∀ c≤d.p.a.val, Receipt mode d (owner mode.policy d.p.a.val t c) (action t c)

abbrev fieldAction {N} {mode : Mode} {d : Data N} (packet : Packet mode d) (t c : Nat) := packet.action t c

theorem fieldAction_spec {N} {mode : Mode} {d : Data N} (packet : Packet mode d) (valid : Valid d)
    (t c : Nat) (tree : t<d.p.k.val) (col : c≤d.p.a.val) :
    fieldAction packet t c ⦃ w => Value d t c w ⦄ := by
  obtain ⟨row,column⟩ := owner_fields mode.policy d.p.a.val t c
  simpa only [row,column] using (packet.issued t tree c col).correct valid

/-- A raw post-join cell must contain the row returned by its designated worker.
No postcondition in this contract describes the bytes of a hash or a signature. -/
def Publications {N} (mode : Mode) (d : Data N) (cells : Cells N) :=
  ∀ t<d.p.k.val, ∀ c≤d.p.a.val, ∃ action,
    Receipt mode d (owner mode.policy d.p.a.val t c) action ∧ Agrees cells action

def pack {N : Usize} (_host : ParallelRootWalk.Host) (p : params.Params) (_md : Slice U8)
    (_sk _seed : Array U8 N) (_a : address.Adrs) (cells : Cells N) := ParallelForestPack.pack_fors p cells

def Mode.rootHost : Mode → ParallelRootWalk.Host
  | .fallback (.apple b) | .apple b => .apple b
  | .fallback .linux | .linux => .linuxArm
  | .fallback .x86 | .x86 _ => .x86

theorem pack_spec {N} (mode : Mode) (d : Data N) (valid : Valid d) (md : Slice U8)
    (decode : nats d.choices.val=Spec.base2b (bytes md.val) d.p.a.val d.p.k.val)
    (cells : Cells N) (size : cells.length=d.p.k.val*(1+d.p.a.val)) (pub : Publications mode d cells) :
    pack mode.rootHost d.p md d.sk d.seed d.addr cells ⦃ out =>
      bytes out.val=Spec.forsSign (Shake.params d.p) (bytes md.val) (bytes d.sk.val) (bytes d.seed.val) (adrsS d.addr) ⦄ := by
  apply ParallelForestPack.pack_fips d.p valid.pn cells (bytes md.val) (bytes d.sk.val) (bytes d.seed.val) (adrsS d.addr) size
  intro q inside
  have bound : q<d.p.k.val*(d.p.a.val+1) := by simpa [size,Nat.add_comm] using inside
  obtain ⟨t,tree,c,col,whereAt⟩ := complete mode.policy d.p.a.val d.p.k.val q bound
  rw [ownership] at whereAt
  obtain ⟨action,receipt,stored⟩ := pub t tree c col
  obtain ⟨w,run,pos,val⟩ := spec_imp_exists (receipt.correct valid)
  obtain ⟨row,column⟩ := owner_fields mode.policy d.p.a.val t c
  change w.1.val = _ at pos
  rw [row,column,whereAt] at pos
  rw [row,column] at val
  have saved := stored w run
  refine ⟨w.2,pos ▸ saved,?_⟩
  rw [←whereAt,←field_eq d.p md d.sk d.seed d.addr d.choices decode valid.count t c tree col,val]

end slhdsa.RawFors
