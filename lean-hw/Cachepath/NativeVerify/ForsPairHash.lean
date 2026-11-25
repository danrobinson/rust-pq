import Cachepath.NativeVerify.ForsParents
import Cachepath.NativeVerify.ForsPairPad

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1400000
variable [machine : Machine] [accelerator : ActiveKernel machine]

def hashParents (N : Usize) (i : U64) (sig : Slice U8) (n offset pad_pair stride : Usize)
    (sw aw : Array U64 4#usize) (first active : Usize) (lvl : U32)
    (state : Matrix machine.width) (indices : Array U32 machine.width) :
    Result (Matrix machine.width × Array U32 machine.width) := do
  let a := Array.repeat machine.width 0#u64
  let cur := Array.repeat 4#usize a
  let (state1, cur1) ←
    recover_loop0_loop4_loop0
      { start := 0#usize, «end» := n } sw state cur
  let i1 ← Array.index_usize aw 0#usize
  let a1 := Array.repeat machine.width i1
  let state2 ← Array.update state1 n a1
  let i2 ← Array.index_usize aw 1#usize
  let i3 ← n + 1#usize
  let a2 := Array.repeat machine.width i2
  let state3 ← Array.update state2 i3 a2
  let i4 ← Array.index_usize aw 2#usize
  let i5 ← n + 2#usize
  let a3 := Array.repeat machine.width i4
  let a4 ← Array.update state3 i5 a3
  let i6 ← lvl + 1#u32
  let i7 ← ShakeBatch.core.num.U32.swap_bytes i6
  let lvl_lo ← lift (core.convert.num.FromU64U32.from i7)
  let (state4, indices1) ←
    recover_loop0_loop4_loop1 N
      { start := 0#usize, «end» := active } sig n offset stride a4 first
      indices lvl cur1 lvl_lo
  let prepared ← pairPad state4 pad_pair i
  let out ← accelerator.run prepared active
  ok (out,indices1)

theorem split_level (N : Usize) (marker : U64) (sig : Slice U8) (n offset pad stride : Usize)
    (sw aw : Array U64 4#usize) (first active : Usize) (it : core.ops.range.Range U32)
    (state : Matrix machine.width) (ix : Array U32 machine.width) :
    recover_loop0_loop4.body N marker sig n offset pad stride sw aw first active it state ix = (do
      let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepU32 it
      match o with
      | none => ok (done state)
      | some lvl =>
        let (out,updated) ← hashParents N marker sig n offset pad stride sw aw first active lvl state ix
        ok (cont (next,out,updated))) := by
  unfold recover_loop0_loop4.body hashParents pairPad
  congr 1
  funext ⟨o,next⟩
  cases o <;> simp [Std.bind_assoc]
  simp only [uncurry,bind_tc_eq,Std.bind_assoc,bind_ok]
  repeat' congr 1

def parentInput (sw aw : Array U64 4#usize) (state : Matrix machine.width) (idx : U32)
    (n offset pad : Nat) (height : U32) (sig : Slice U8) (N block : Nat) (k l : Nat) : BitVec 64 :=
  let par : U32 := ⟨idx.bv >>> 1⟩
  let even := idx.val%2=0
  let prior := fun w => cell state w l
  let sibling := blockWords sig N block
  let raw := if k=pad then 31 else if pad<k then 0 else if k=n+3 then addressLow height ||| wordTag par
    else if k<n then sw.val[k]!.bv else if k<offset then aw.val[k-n]!.bv else
    if k<offset+n then (if even then prior else sibling) (k-offset)
    else (if even then sibling else prior) (k-(offset+n))
  if k=16 then raw ||| 0x8000000000000000 else raw

theorem parent_layout (N : Usize) (sig : Slice U8) (n offset pad stride first active : Usize)
    (sw aw : Array U64 4#usize) (lvl : U32) (s : Matrix machine.width) (ix : Array U32 machine.width)
    (small : n.val≤4) (size : n.val*8=N.val) (off : offset.val=n.val+4) (padEq : pad.val=offset.val+2*n.val)
    (live : active.val≤machine.width.val) (depth : lvl.val+2≤stride.val) (heightBound : lvl.val<32)
    (fit : (first.val+active.val)*stride.val*N.val≤sig.length) (pos : 0<N.val)
    (permutes : ActiveCorrect machine accelerator.run) :
    hashParents N 0x8000000000000000#u64 sig n offset pad stride sw aw first active lvl s ix ⦃ out updated =>
      (∀ l<active.val, updated.val[l]! = ⟨ix.val[l]!.bv >>> 1⟩) ∧
      ∃ before : Matrix machine.width, ∃ height : U32, height.val=lvl.val+1 ∧
      (∀ l<active.val, ShakeBatch.lane out l=Spec.Keccak.permute (ShakeBatch.lane before l)) ∧
      ∀ k<25, ∀ l<active.val, cell before k l = parentInput sw aw s ix.val[l]! n.val offset.val pad.val height
        sig N.val ((first.val+l)*stride.val+lvl.val+1) k l ⦄ := by
  unfold hashParents
  step with snapshot s _ n sw small as ⟨st,cur,seeded,saved⟩
  step as ⟨w0,r0⟩
  step as ⟨s0,u0⟩
  step as ⟨w1,r1⟩
  step as ⟨n1,v1⟩
  step as ⟨s1,u1⟩
  step as ⟨w2,r2⟩
  step as ⟨n2,v2⟩
  step as ⟨st2,u2⟩
  step as ⟨height,hv⟩
  simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
  step with parent_lanes N sig n offset stride first active lvl cur _ st2 ix size off small live depth fit pos as ⟨s3,updated,indices,cells⟩
  step with pair_pad s3 pad 0x8000000000000000#u64 (by omega) as ⟨prepared,padded⟩
  step with permutes prepared active live as ⟨out,hashed⟩
  refine ⟨fun l hl => (indices l (by omega)).trans (ite_eq_left hl),prepared,height,hv,hashed,?_⟩
  intro k hk l hl
  have within := hl.trans_le live
  rw [padded k hk l within,cells k hk l within,ite_eq_left hl]
  unfold parentInput orderedCell
  rw [u2,write_tag _ _ _ (by omega) k l within,u1,write_tag _ _ _ (by omega) k l within,
    u0,write_tag _ _ _ (by omega) k l within,seeded k hk l within,r0,r1,r2,
    ← getElem!_pos,← getElem!_pos,← getElem!_pos,v1,v2]
  have same (j : Nat) (less : j<n.val) : cur.val[j]!.val[l]!.bv=cell s j l := by rw [saved j less];rfl
  have finish (x y : BitVec 64) (eq : x=y) :
      (if k=16 then x ||| 0x8000000000000000 else x) = (if k=16 then y ||| 0x8000000000000000 else y) := eq ▸ rfl
  apply finish
  by_cases even : ix.val[l]!.val%2=0 <;> simp only [even,ite_true,ite_false]
  all_goals split_ifs <;> first | rfl | omega | (exact same _ (by omega)) |
    (subst_vars; simp only [Nat.add_sub_cancel_left,Nat.sub_self] <;> rfl)
  
end slhdsa.NativeVerify.Fors
