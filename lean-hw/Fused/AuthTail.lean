import Fused.Program
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
variable [kernel : Kernel]
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000

def SiblingAt {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (idx height : Nat) :=
  Spec.xmssNode (Shake.params p) (bytes sk.val) ((idx/2^height) ^^^ 1) height (bytes seed.val) (adrsS a)

def authPrefix (sibling : Nat → Spec.Bytes) (height : Nat) := (List.range height).flatMap sibling

/-- A write extends the already assembled front by the entire output row. -/
theorem copy_prefix (before : alloc.vec.Vec U8) (after : alloc.vec.Vec U8) {N : Usize}
    (node : Array U8 N) (start : Nat) (inside : start+N.val ≤ before.length)
    (store : after.val=before.val.setSlice! start node.val) :
    after.length=before.length ∧ bytes (after.val.take (start+N.val)) =
      bytes (before.val.take start) ++ bytes node.val := by
  refine ⟨by change after.val.length=_;rw [store];simp,?_⟩
  have h : start+node.val.length≤before.val.length := by simpa using inside
  have front : (before.val.setSlice! start node.val).take (start+node.val.length) =
    before.val.take start ++ node.val := by
    rw [List.setSlice!,min_eq_left (by omega),List.take_length]
    have len : start+node.val.length = (before.val.take start ++ node.val).length := by
      simp [List.length_take,min_eq_left (by omega : start≤before.val.length)]
    rw [len,List.take_append_length]
  rw [store,← node.property,front]
  simp [bytes]

def SubtreeAt {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) :=
  ∀ (i z : U32), 3≤z.val → z.val≤9 → (i.val+1)*2^z.val≤512 →
    kernel.subtree sk seed i z a ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄

theorem auth_tail {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (idx : U32)
    (a : address.Adrs) (sig : alloc.vec.Vec U8) (pos : Usize) (base : Nat) (start : U32) (front : Spec.Bytes)
    (nodes : SubtreeAt p sk seed a) (range : idx.val < 2^p.hp.val) (lo : start.val ≤ p.hp.val) (startAt : 3≤start.val)
    (size : sig.length=base+p.hp.val*N.val) (atPos : pos.val=base+start.val*N.val)
    (before : bytes (sig.val.take pos.val)=front ++ authPrefix (SiblingAt p sk seed a idx.val) start.val) :
    xmss_sign_batch_loop5 ⟨start,p.hp⟩ sk idx seed a sig pos ⦃ out =>
      bytes out.val=front ++ authPrefix (SiblingAt p sk seed a idx.val) p.hp.val ⦄ := by
  unfold xmss_sign_batch_loop5
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × alloc.vec.Vec U8 × Usize =>
      p.hp.val-q.1.start.val)
    (inv := fun q => q.1.end=p.hp ∧ 3≤q.1.start.val ∧ q.1.start.val≤p.hp.val ∧ q.2.1.length=base+p.hp.val*N.val ∧
      q.2.2.val=base+q.1.start.val*N.val ∧ bytes (q.2.1.val.take q.2.2.val)=front ++
      authPrefix (SiblingAt p sk seed a idx.val) q.1.start.val)
  · rintro ⟨it,st,cur⟩ ⟨stop,low,limit,length,location,doneRows⟩
    simp only at stop low limit length location doneRows ⊢
    unfold xmss_sign_batch_loop5.body
    have maxHeight : p.hp.val≤9 := hp.valid.hp_le
    by_cases more : it.start.val<p.hp.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [stop];exact more) as ⟨_,next,tag,inc,last⟩
      simp only [tag]
      step as ⟨v,shift,_⟩
      simp only [lift,bind_ok]
      have vval : (v ^^^ 1#u32).val=(idx.val/2^it.start.val)^^^1 := by
        simp [UScalar.val_xor,shift,Nat.shiftRight_eq_div_pow]
      have pow : 2^(p.hp.val-it.start.val)*2^it.start.val = 2^p.hp.val := by
        rw [← Nat.pow_add,Nat.sub_add_cancel (by omega)]
      have q := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos it.start.val)).2 (pow.symm ▸ range)
      have one : 1<2^(p.hp.val-it.start.val) := lt_of_lt_of_le (by decide : 1<2^1)
        (Nat.pow_le_pow_right (by decide) (by omega))
      have fit : ((v ^^^ 1#u32).val+1)*2^it.start.val≤512 := by
        rw [vval]
        exact (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Nat.xor_lt_two_pow q one))).trans
          (pow ▸ Nat.pow_le_pow_right (by decide : 0<2) maxHeight)
      step with nodes _ it.start low (by omega) fit as ⟨node,value⟩
      have bound := Nat.mul_le_mul_right N.val (Nat.succ_le_of_lt more)
      rw [Nat.succ_mul] at bound
      have capacity : st.length ≤ Usize.max := by simp
      step as ⟨endPos,ev⟩
      step as ⟨s,back,data,slen,store⟩
      try simp only [lift,bind_ok]
      step as ⟨w,cp⟩
      all_goals try scalar_tac
      have put : (back w).val=st.val.setSlice! cur.val node.val := by rw [store,cp];simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice]
      obtain ⟨sz,content⟩ := copy_prefix st (back w) node cur.val (by omega) put
      refine ⟨last.trans stop,by omega,by omega,sz.trans length,?_,?_,by omega⟩
      · rw [inc,Nat.add_mul,one_mul,ev,location];omega
      · rw [inc,authPrefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,ev,content,doneRows,
          value,vval,List.append_assoc]
        rfl
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by rw [stop];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      have endHeight : it.start.val=p.hp.val := by omega
      rw [endHeight] at location doneRows
      have exactLen : cur.val=st.val.length := location.trans length.symm
      simpa [exactLen] using doneRows
  · exact ⟨rfl,startAt,lo,size,atPos,before⟩

end slhdsa.Fused
