import Parallel.ForsCover
import Parallel.ForsMetaMerge
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

inductive Mode where
  | fallback (host : ParallelScalarFors.Platform)
  | linux
  | apple (sha3 : Bool)
  | x86 (available : GatherRust.avx512Available=true)

def Mode.policy : Mode → Policy
  | .fallback _ => .scalar | .linux => .three | .apple _ | .x86 _ => .eight

def Mode.host : Mode → ParallelScalarFors.Platform
  | .fallback h => h | .linux => .linux | .apple b => .apple b | .x86 _ => .x86

structure Data (N : Usize) where
  p : params.Params
  sk : Array U8 N
  seed : Array U8 N
  addr : address.Adrs
  choices : alloc.vec.Vec U32
  stride : Usize

structure Valid {N} (d : Data N) : Prop where
  pn : PN d.p N
  domain : ForsHorizontal.Domain d.addr
  count : d.choices.length=d.p.k.val
  digits : ∀ t<d.choices.length, d.choices.val[t]!.val<2^d.p.a.val
  stride : d.stride.val=d.p.a.val+1

abbrev Cell (N : Usize) := Usize × Array U8 N
abbrev Cells (N : Usize) := alloc.vec.Vec (Option (Array U8 N))

def Writes {N} (cells : Cells N) (w : Cell N) := cells.val[w.1.val]! = some w.2

def Agrees {N} (cells : Cells N) (computation : Result (Cell N)) :=
  ∀ w, computation=ok w → Writes cells w

noncomputable def scalarLow {N} (host : ParallelScalarFors.Platform) (d : Data N) (t depth : U32)
    (journal : ParallelScalarFors.Journal N) (c : Nat) : Result (Cell N) :=
  Std.bind (ParallelScalarFors.hostedLow host d.p d.sk d.seed d.addr d.choices t d.p.a depth d.stride journal)
    (fun r => ok (if c=0 then r.1 else r.2.val[c-1]!))

noncomputable def scalarDirect {N} (host : ParallelScalarFors.Platform) (d : Data N) (t j : U32) :=
  ParallelScalarFors.run (ParallelScalarFors.actions host d.p d.sk d.seed d.addr).1
    (ParallelScalarFors.prepare_direct t d.p.a j d.choices.val[t.val]!)

def unreachableLow : ParallelLowFors.Wide := ⟨fun _ _ _ _ _ => fail .panic⟩
def unreachableHigh : ParallelForsTicket.Wide := ⟨fun _ _ _ _ _ => fail .panic⟩

noncomputable def lowJournal {N} (mode : Mode) (d : Data N) (first : U16) (active depth : U8) : Result (ParallelLowFors.Journal N) :=
  let action := match mode with
    | .linux => @ParallelLowFors.ticket Kldisp.machine ParallelLowFors.linuxHost unreachableLow N
    | .apple b => @ParallelLowFors.ticket (AppleHybrid.machine b) (ParallelLowFors.appleHost b) (ParallelLowFors.appleWide b d.p) N
    | .x86 _ => @ParallelLowFors.ticket Kxdispatch.machine ParallelLowFors.x86Host (ParallelLowFors.x86Wide d.p) N
    | .fallback _ => fun _ _ _ _ _ _ _ _ _ => fail .panic
  action d.sk d.seed d.addr d.choices d.p.a first active depth d.stride

noncomputable def groupedLow {N} (mode : Mode) (d : Data N) (first : U16) (active depth : U8)
    (col lane : Nat) : Result (Cell N) :=
  Std.bind (lowJournal mode d first active depth) (fun rows => ok rows.val[col*active.val+lane]!)

noncomputable def groupedDirect {N} (d : Data N) (first : U16) (active h : U8) (lane : Nat) : Result (Cell N) :=
  Std.bind (@ParallelForsTicket.direct_ticket unreachableHigh N d.sk d.seed d.addr d.choices d.p.a first active h d.stride)
    (fun rows => ok rows.val[lane]!)

def Value {N} (d : Data N) (t col : Nat) (w : Cell N) :=
  w.1.val=t*(d.p.a.val+1)+col ∧ bytes w.2.val=ParallelLowFors.field d.p d.sk d.seed d.addr d.choices t col

theorem scalar_low {N} (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d) (t depth : U32)
    (journal : ParallelScalarFors.Journal N) (col : Nat) (tree : t.val<d.p.k.val) (within : col≤depth.val)
    (height : depth.val≤d.p.a.val) : scalarLow host d t depth journal col ⦃ w => Value d t.val col w ⦄ := by
  have inside : t.val<d.choices.length := valid.count.symm ▸ tree
  obtain ⟨r,run,whereAt,value,fields⟩ := spec_imp_exists (ParallelScalarFors.low_published host d.p valid.pn d.sk d.seed d.addr valid.domain
    d.choices t d.p.a depth d.stride journal inside (lt_of_lt_of_le tree valid.pn.valid.k_le) valid.pn.valid.a_le (valid.digits _ inside) height valid.stride)
  unfold scalarLow
  rw [run,bind_ok]
  cases col with
  | zero => simpa [Value,ParallelLowFors.field,ParallelLowFors.absolute] using And.intro whereAt value
  | succ j =>
    obtain ⟨pos,val⟩ := fields j (by omega)
    simpa [Value,ParallelLowFors.field,ForsDriver.sibling_local _ _ _ _ (show j<d.p.a.val by omega),
      ParallelScalarFors.sibling,alloc.vec.Vec.val,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using And.intro pos val

theorem scalar_direct {N} (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d) (t j : U32)
    (tree : t.val<d.p.k.val) (height : j.val<d.p.a.val) : scalarDirect host d t j ⦃ w => Value d t.val (j.val+1) w ⦄ := by
  apply WP.spec_mono (ParallelScalarFors.direct_published host d.p valid.pn d.sk d.seed d.addr valid.domain t d.p.a j d.choices.val[t.val]!
    (lt_of_lt_of_le tree valid.pn.valid.k_le) valid.pn.valid.a_le height (valid.digits _ (valid.count.symm ▸ tree)))
  intro w out
  simpa only [Value,ParallelLowFors.field,ForsDriver.sibling_local _ _ _ _ height,ParallelScalarFors.sibling,
    alloc.vec.Vec.val,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using out

theorem grouped_direct {N} (d : Data N) (valid : Valid d) (first : U16) (active h : U8) (lane : Nat) (bounded : active.val≤3)
    (capacity : first.val+active.val≤d.choices.length) (inside : lane<active.val) (height : h.val<d.p.a.val) :
    groupedDirect d first active h lane ⦃ w => Value d (first.val+lane) (h.val+1) w ⦄ := by
  obtain ⟨rows,call,values⟩ := spec_imp_exists (@ParallelForsTicket.direct_ticket_spec unreachableHigh N d.p valid.pn d.sk d.seed d.addr
    d.choices first active h d.stride valid.domain valid.pn.valid.a_le height (valid.count.symm ▸ valid.pn.valid.k_le)
    (by omega) bounded capacity valid.digits valid.stride)
  unfold groupedDirect
  rw [call,bind_ok]
  simpa [Value,ParallelLowFors.field,valid.stride,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using values lane inside

theorem grouped_low {N} (mode : Mode) (d : Data N) (valid : Valid d) (first : U16) (active depth : U8) (col lane : Nat)
    (grouped : mode.policy≠.scalar) (bounded : active.val≤width mode.policy)
    (capacity : first.val+active.val≤d.choices.length) (inside : lane<active.val) (height : depth.val≤d.p.a.val)
    (narrow : mode.policy=.three ∨ depth.val≤3) (field : col≤depth.val) :
    groupedLow mode d first active depth col lane ⦃ w => Value d (first.val+lane) col w ⦄ := by
  have count : d.choices.length≤35 := by rw [valid.count];exact valid.pn.valid.k_le
  have pos : 0<active.val := by omega
  have finish (run : Result (ParallelLowFors.Journal N))
      (spec : run ⦃ out => ParallelLowFors.Fields first.val active.val d.stride.val (depth.val+1)
        (ParallelLowFors.field d.p d.sk d.seed d.addr d.choices) out ⦄) :
      Std.bind run (fun rows => ok rows.val[col*active.val+lane]!) ⦃ w => Value d (first.val+lane) col w ⦄ := by
    obtain ⟨rows,call,_,rowsAt⟩ := spec_imp_exists spec
    rw [call,bind_ok];simpa [Value,valid.stride] using rowsAt col (by omega) lane inside
  cases mode with
  | fallback h => exact False.elim (grouped rfl)
  | linux => exact finish _ (@ParallelLowFors.linux_spec unreachableLow N d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height valid.stride)
  | apple b => exact finish _ (ParallelLowFors.apple_spec b d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height (narrow.resolve_left (by simp [Mode.policy])) valid.stride)
  | x86 flag => exact finish _ (ParallelLowFors.x86_spec flag d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height (narrow.resolve_left (by simp [Mode.policy])) valid.stride)

end slhdsa.RawFors
