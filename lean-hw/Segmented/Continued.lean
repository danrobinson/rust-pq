import Segmented.Loop
open Aeneas Aeneas.Std Result
namespace slhdsa.Segmented

def FinishRule {T R D H B} (model : Hash T R D) (alg : Impl H T R B) (total : Nat) :=
  ∀ st (pre : Usize) (bytes : Slice U8), pre.val%B.val=0 → pre.val+bytes.length=total →
    alg.finish st pre bytes ⦃ out => model.output out = model.digest st pre.val bytes.val ⦄

theorem continued_spec {T R D H} (model : Hash T R D) (B : Usize) (width : 0<B.val)
    (alg : Impl H T R B) (stepBlock : BlockRule model alg)
    (initial : T) (pre : Usize) (front msg : Slice U8)
    (alignment : pre.val%B.val=0)
    (room : pre.val+front.length+msg.length≤Usize.max)
    (finish : FinishRule model alg (pre.val+front.length+msg.length)) :
    SegmentedRust.slh.message.continued alg initial pre front msg ⦃ out =>
      model.output out = model.digest initial pre.val (front.val ++ msg.val) ⦄ := by
  unfold SegmentedRust.slh.message.continued
  step with prefix_loop model B width alg stepBlock initial pre.val front msg as ⟨st,pos,bound,short,aligned,loopOk⟩
  step as ⟨used,usedVal⟩
  step as ⟨tail,tailVal⟩
  have ht : tail.length = front.length-pos.val := by simp [Slice.length,tailVal]
  have hu : used.val%B.val=0 := by rw [usedVal,Nat.add_mod,alignment,aligned]; simp
  split
  · rename_i empty
    have he : tail.val=[] := by apply List.length_eq_zero_iff.mp; exact congrArg UScalar.val empty
    have hz : tail.length=0 := by simp [Slice.length,he]
    step with finish st used msg hu (by omega) as ⟨out,ok⟩
    rw [ok,usedVal,←loopOk,←tailVal,he,List.nil_append]
  · step as ⟨s,back,sv,sl,sb⟩
    step as ⟨s1,copy1⟩
    step as ⟨left,leftVal⟩
    simp only [core.cmp.impls.OrdUsize.min,lift,bind_ok]
    let n := if msg.len < left then msg.len else left
    have nVal : n.val=min msg.length (B.val-tail.length) := by
      dsimp [n]
      split <;> simp_all [UScalar.lt_equiv] <;> omega
    change (do let count ← tail.len + n; _) ⦃ _ ⦄
    step as ⟨count,countVal⟩
    step as ⟨s2,back2,sv2,sl2,sb2⟩
    step as ⟨s3,v3,l3⟩
    change s3.length=n.val at l3
    change s3.val=List.slice 0 n.val msg.val at v3
    have lens : s2.length=s3.length := by omega
    step as ⟨s4,copy4⟩
    have ns : n.val≤msg.length := by omega
    change count.val=tail.length+n.val at countVal
    have nBound : n.val≤B.val-tail.length := by omega
    have filled : (back2 s4).val = tail.val ++ msg.val.take n.val ++
        (Array.repeat B 0#u8).val.drop count.val := by
      rw [sb2,sb,copy4,copy1,v3]
      simp only [List.slice, List.drop_zero, Nat.sub_zero]
      generalize hzeros : (Array.repeat B 0#u8).val=z
      have len : z.length=B.val := by simp [←hzeros]
      rw [show z=[]++z by simp,setSlice_gen [] z tail.val 0 rfl (by change tail.length≤_; omega),List.nil_append]
      rw [setSlice_gen tail.val (z.drop tail.val.length) (msg.val.take n.val) tail.len.val rfl (by simp only [List.length_take,List.length_drop,len]; change min n.val msg.length≤B.val-tail.length; omega)]
      simp [List.drop_drop,countVal,List.length_take,Nat.min_eq_left ns,Slice.length]
    split
    · rename_i small
      have whole : n.val=msg.length := by change count.val<B.val at small; omega
      step as ⟨last,lv,ll⟩
      change last.length=count.val at ll
      step with finish st used last hu (by omega) as ⟨out,ok⟩
      rw [ok,usedVal,←loopOk,←tailVal,lv]
      simp [Array.val_to_slice,filled, List.slice,whole,List.take_append,countVal,Slice.length, List.take_of_length_le]
    · rename_i full
      have widthEq : count.val=B.val := by change ¬count.val<B.val at full; omega
      have headOk : (back2 s4).val = tail.val ++ msg.val.take n.val := by
        rw [filled,widthEq]; simp
      step with stepBlock st (back2 s4).to_slice 0#usize (by simp) as ⟨next,consume⟩
      step as ⟨used2,used2Val⟩
      step as ⟨last,lv,ll⟩
      change last.val=msg.val.drop n.val at lv
      have lastLen : last.length=msg.length-n.val := by simp [Slice.length,lv]
      have aligned2 : used2.val%B.val=0 := by rw [used2Val,Nat.add_mod,hu]; simp
      step with finish next used2 last aligned2 (by omega) as ⟨out,ok⟩
      rw [ok,used2Val,consume]
      simp only [Array.val_to_slice, show (0#usize).val=0 by rfl, List.drop_zero]
      rw [headOk,lv]
      rw [List.take_of_length_le (by simp [List.length_take, ns,←widthEq,countVal,Slice.length])]
      rw [List.append_assoc,List.take_append_drop,usedVal,←loopOk,←tailVal]
end slhdsa.Segmented
