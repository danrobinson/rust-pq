import Cachepath.NativeVerify.ForsLeaf
import Cachepath.WotsFusedOuter

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1200000
variable [machine : Machine]

private abbrev State := Matrix machine.width
private abbrev Saved := Array (Array U64 machine.width) 4#usize
private abbrev Indices := Array U32 machine.width

def orderedCell (N n offset stride first lvl : Nat) (cur : Saved) (sig : Slice U8)
    (initial : Indices) (low : BitVec 64) (s : State) (k l : Nat) :=
  let idx := initial.val[l]!
  let par : U32 := ⟨idx.bv >>> 1⟩
  let prior := fun i : Nat => cur.val[i]!.val[l]!.bv
  let sib := blockWords sig N ((first+l)*stride+lvl+1)
  let even := idx.val%2=0
  if k=n+3 then low ||| wordTag par else
  if offset ≤ k ∧ k<offset+n then (if even then prior else sib) (k-offset) else
  if offset+n ≤ k ∧ k<offset+n+n then (if even then sib else prior) (k-(offset+n)) else cell s k l

theorem parent_lanes (N : Usize) (sig : Slice U8) (n offset stride first active : Usize) (lvl : U32)
    (cur : Saved) (lo : U64) (state : State) (indices : Indices)
    (size : n.val*8=N.val) (off : offset.val=n.val+4) (cap : n.val≤4)
    (width : active.val≤machine.width.val) (depth : lvl.val+2≤stride.val)
    (fits : (first.val+active.val)*stride.val*N.val ≤ sig.length) (npos : 0<N.val) :
    recover_loop0_loop4_loop1 N ⟨0#usize,active⟩ sig n offset stride state first indices lvl cur lo ⦃ st ix =>
      (∀ l<machine.width.val, ix.val[l]! = if l<active.val then ⟨indices.val[l]!.bv >>> 1⟩ else indices.val[l]!) ∧
      (∀ k<25, ∀ l<machine.width.val, cell st k l = if l<active.val then
        orderedCell N.val n.val offset.val stride.val first.val lvl.val cur sig indices lo.bv state k l else cell state k l) ⦄ := by
  unfold recover_loop0_loop4_loop1
  apply range_fold (fun it (v : State × Indices) => recover_loop0_loop4_loop1.body N sig n offset stride first lvl cur lo it v.1 v.2)
    active (state,indices) (fun count v =>
      (∀ l<machine.width.val, v.2.val[l]! = if l<count then ⟨indices.val[l]!.bv >>> 1⟩ else indices.val[l]!) ∧
      (∀ k<25, ∀ l<machine.width.val, cell v.1 k l = if l<count then
        orderedCell N.val n.val offset.val stride.val first.val lvl.val cur sig indices lo.bv state k l else cell state k l))
  · simp
  · rintro it ⟨st,ix⟩ stop live ⟨indicesAt,cells⟩
    dsimp only at indicesAt cells
    have inside : it.start.val<machine.width.val := by omega
    have old := indicesAt it.start.val inside
    simp only [lt_self_iff_false,ite_false] at old
    unfold recover_loop0_loop4_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨idx,idxRead⟩
    rw [← getElem!_pos,old] at idxRead
    step as ⟨parent,pv,pbits⟩
    have par : parent=(⟨(indices.val[it.start.val]!).bv >>> 1⟩ : U32) := by
      apply UScalar.eq_of_val_eq
      exact congrArg BitVec.toNat (idxRead ▸ pbits)
    step as ⟨_,putIdx,_,idxBack⟩
    simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
    step as ⟨hi,_,hiBits⟩
    have tagVal : hi.bv=wordTag parent := hiBits
    step as ⟨r,rv⟩
    step as ⟨row,putRow,read,rowBack⟩
    step as ⟨_,putWord,_,wordBack⟩
    try simp only [lift,bind_ok]
    have treeBound := Nat.mul_le_mul_right stride.val (show first.val+it.start.val+1≤first.val+active.val by omega)
    rw [Nat.add_mul,one_mul] at treeBound
    have upper : (first.val+it.start.val)*stride.val+lvl.val+1+1≤(first.val+active.val)*stride.val := by omega
    have blockFit := (Nat.mul_le_mul_right N.val upper).trans fits
    have maxN : sig.length≤Usize.max := by simp
    have dom := Nat.mul_le_mul_left ((first.val+it.start.val)*stride.val+lvl.val+1+1) npos
    have tdom := Nat.mul_le_mul_left (first.val+it.start.val) (show 1≤stride.val by omega)
    simp only [Nat.mul_one] at dom tdom
    step as ⟨tree,tv⟩
    step as ⟨base,bv⟩
    try simp only [lift,bind_ok]
    have cv : (UScalar.cast .Usize lvl).val=lvl.val := by scalar_tac
    step as ⟨addressed,av⟩
    step as ⟨block,blockv⟩
    have blockEq : block.val=(first.val+it.start.val)*stride.val+lvl.val+1 := by rw [blockv,av,cv,bv,tv]
    have endFits : (block.val+1)*N.val≤sig.length := by rw [blockEq];exact blockFit
    have startFits : block.val*N.val≤sig.length := by rw [Nat.add_mul,one_mul] at endFits;omega
    step as ⟨pos,posv⟩
    step as ⟨limit,lv⟩
    have endOk : limit.val*N.val≤sig.length := by rw [lv];exact endFits
    step as ⟨endPos,ev⟩
    have rangeEq : pos.val+N.val=endPos.val := by rw [posv,ev,lv,Nat.add_mul,one_mul]
    step as ⟨sib,sibBytes,sibLen⟩
    try simp only [lift,bind_ok]
    have sibEq : inputWord sib.val = blockWords sig N.val ((first.val+it.start.val)*stride.val+lvl.val+1) := by
      unfold blockWords
      rw [sibBytes]
      simp only [List.slice,← rangeEq,Nat.add_sub_cancel_left,posv,blockEq]
    let tagged := putRow (putWord (lo ||| hi))
    have cellsTagged (k l : Nat) : cell tagged k l =
        if k=n.val+3 ∧ l=it.start.val then lo.bv ||| wordTag parent else cell st k l := by
      unfold tagged
      rw [rowBack,wordBack,read,← getElem!_pos,cell_write st r it.start (lo ||| hi) (by omega) inside,rv,← tagVal];rfl
    have bit : (idx &&& 1#u32).val = indices.val[it.start.val]!.val%2 := by rw [idxRead];simp [Nat.and_one_is_mod]
    have finish (odd : Bool) :=
      pair_payloads tagged n offset it.start cur sib odd cap (by omega) inside (by omega)
    let odd := decide (indices.val[it.start.val]!.val%2≠0)
    have chosen := finish odd
    have branchEq : (idx &&& 1#u32 = 0#u32) ↔ odd=false := by
      change _ ↔ decide _ = false
      rw [decide_eq_false_iff_not,not_not]
      constructor
      · intro e;rw [← bit,e];rfl
      · intro e;apply UScalar.eq_of_val_eq;rw [bit,e];rfl
    apply cache.builder.nativeShake.Vector.Fused.ofProgramEq (g := (do
      let result ← if odd then recover_loop0_loop4_loop1_loop1 ⟨0#usize,n⟩ n offset tagged cur it.start sib
                    else recover_loop0_loop4_loop1_loop0 ⟨0#usize,n⟩ n offset tagged cur it.start sib
      ok (cont (next,result,putIdx parent))))
    · by_cases e : idx &&& 1#u32 = 0#u32
      · simp [e,branchEq.mp e,tagged]
      · have neq : odd=true := by cases eq : odd with
          | false => exact False.elim (e (branchEq.mpr eq))
          | true => rfl
        simp [e,neq,tagged]
    apply WP.spec_bind chosen
    intro result changed
    simp only [WP.spec_ok]
    refine ⟨next,(result,putIdx parent),rfl,ends.trans stop,inc,?_,?_⟩
    · intro l hl
      rw [idxBack,Array.set_val_eq]
      by_cases same : l=it.start.val
      · subst l; rw [setSame _ _ _ (by simpa),ite_eq_left (by omega),par]
      · rw [setOther _ _ _ _ (Ne.symm same),indicesAt l hl,if_congr (show l < it.start.val ↔ l < next.start.val by omega) rfl rfl]
    · intro k hk l hl
      rw [changed k hk l hl]
      simp only [payload,cellsTagged,cells k hk l hl]
      by_cases same : l=it.start.val
      · subst l
        simp only [orderedCell,odd,decide_eq_true_eq,sibEq,par,inc,Nat.lt_succ_self,lt_self_iff_false,ite_true,ite_false,and_true,true_and]
        split_ifs <;> first | rfl | omega
      · simp [same,show (l < next.start.val) ↔ l < it.start.val by omega]
  · rintro it ⟨st,ix⟩ last stop
    unfold recover_loop0_loop4_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Fors
