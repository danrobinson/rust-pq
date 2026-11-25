import Cachepath.NativeShakeWots.SignState
import Cachepath.NativeShakeWots.KeyUtils
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch NativeVerify NativeVerify.Wots
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [machine : Machine]

/-- Scattering one positive-digit chain's secret writes exactly the first N/8
words of its row in the 67-row table. -/
theorem scatter_secret (secrets : Secrets) (state : Matrix machine.width) (n lane id : Usize)
    (cap : n.val≤4) (valid : lane.val<machine.width.val) (bound : id.val<67) :
    sign_loop0_loop0_loop0 ⟨0#usize,n⟩ secrets state lane id ⦃ out =>
      ∀ k j, laneWord out k j = if k=id.val ∧ j<n.val then cell state j lane.val else laneWord secrets k j ⦄ := by
  unfold sign_loop0_loop0_loop0
  apply range_fold (sign_loop0_loop0_loop0.body state lane id) n secrets (fun stop out =>
    ∀ k j, laneWord out k j = if k=id.val ∧ j<stop then cell state j lane.val else laneWord secrets k j)
  · simp
  · intro it st last live prior
    unfold sign_loop0_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [last] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨row,rw0⟩
    step as ⟨v,rw1⟩
    step as ⟨dst,back,get,write⟩
    step as ⟨newVal,upd⟩
    refine ⟨next,back newVal,rfl,ends.trans last,inc,?_⟩
    intro k j
    rw [write,upd,get,← getElem!_pos,storeWord _ _ _ _ bound (by omega),prior]
    by_cases h : k=id.val ∧ j=it.start.val
    · obtain ⟨rfl,rfl⟩ := h
      simp only [and_self,ite_true,inc,Nat.lt_succ_self]
      rw [rw1,← getElem!_pos,rw0,← getElem!_pos]; rfl
    · rw [ite_eq_right h,if_congr (show (k=id.val ∧ j < it.start.val) ↔ (k=id.val ∧ j < next.start.val) by omega) rfl rfl]
  · intro it st stop last
    unfold sign_loop0_loop0_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last,stop]))
    simp [no,tag]

def Prepared (N : Usize) (digits : Slice U32) (secret : Nat → Spec.Bytes)
    (stop : Nat) (sig : Signature) (table : Secrets) : Prop :=
  sig.length=digits.length*N.val ∧
  ∀ i<stop, (digits.val[i]!.val=0 → ∀ b<N.val, Block sig N.val i b=(secret i)[b]!) ∧
    (digits.val[i]!.val≠0 → Words (N:=N) table.val[i]! (secret i))

/-- Scatter every live lane into its production destination. A zero digit publishes
its final signature block immediately. A positive digit saves the PRF for the refill engine. -/
theorem scatter_chunk (N : Usize) (digits : Slice U32) (secret : Nat → Spec.Bytes)
    (n active first : Usize) (state : Matrix machine.width) (sig : Signature) (table : Secrets)
    (count : n.val=N.val/8) (align : N.val%8=0) (small : N.val≤32) (limit : digits.length≤67)
    (valid : active.val≤machine.width.val) (bound : first.val+active.val≤digits.length)
    (hashed : ∀ l<active.val, digest N state l=secret (first.val+l))
    (prior : Prepared N digits secret first.val sig table) :
    sign_loop0_loop0 N ⟨0#usize,active⟩ digits n sig table state first ⦃ result =>
      Prepared N digits secret (first.val+active.val) result.1 result.2 ⦄ := by
  unfold sign_loop0_loop0
  apply range_fold (fun it (st : Signature × Secrets) =>
    sign_loop0_loop0.body N digits n state first it st.1 st.2) active (sig,table)
    (fun i st => Prepared N digits secret (first.val+i) st.1 st.2)
  · simpa using prior
  · rintro it ⟨sig,tab⟩ stop live ⟨size,old⟩
    simp only at size old
    unfold sign_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨id,idv⟩
    step as ⟨digit,read⟩
    rw [← getElem!_pos] at read
    have within : id.val<digits.length := by omega
    have cap : digits.length*N.val≤67*32 := Nat.mul_le_mul limit small
    have fits := Nat.mul_le_mul_right N.val within
    split
    · rename_i zero
      step as ⟨beginAt,bv⟩ <;> try scalar_tac
      step as ⟨after,av⟩
      step as ⟨endAt,ev⟩ <;> try scalar_tac
      step as ⟨part,back,_,plen,backEq⟩
      step with extract_digest N state it.start small align (by omega) as ⟨value,valueBytes⟩
      simp only [lift,bind_ok]
      step as ⟨copy,cp⟩
      all_goals try (simp [bv,ev,av,Nat.add_mul] at *;omega)
      have update : (back copy).val=sig.val.setSlice! (id.val*N.val) value.val := by
        rw [backEq,cp]
        simp [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,bv]
      obtain ⟨length,blocks⟩ := block_store value sig (back copy) _ id.val size within update
      refine ⟨next,(back copy,tab),rfl,ends.trans stop,inc,length,?_⟩
      intro i hi
      by_cases eq : i=id.val
      · subst i
        have z : digits.val[id.val]!.val=0 := by rw [← read,zero];rfl
        refine ⟨fun _ b hb => ?_,fun h => False.elim (h z)⟩
        rw [blocks _ within _ hb,ite_eq_left rfl,valueBytes,hashed _ live,idv]
      · have prev := old i (by omega)
        refine ⟨fun z b hb => ?_,prev.2⟩
        rw [blocks i (by omega) b hb,ite_eq_right eq,prev.1 z b hb]
    · rename_i nonzero
      step with scatter_secret tab state n it.start id (by omega) (by omega) (by omega) as ⟨out,words⟩
      refine ⟨next,(sig,out),rfl,ends.trans stop,inc,size,?_⟩
      intro i hi
      by_cases eq : i=id.val
      · subst i
        have nz : digits.val[id.val]!.val≠0 := by
          intro z
          exact nonzero (UScalar.eq_of_val_eq (by rw [read];exact z))
        refine ⟨fun z => False.elim (nz z),fun _ => ?_⟩
        obtain ⟨buf,vals,packed⟩ := digest_words (N:=N) state (by omega) align
        refine ⟨buf.val[it.start.val]!,?_,?_⟩
        · rw [vals _ (by omega),idv]
          exact hashed _ live
        · intro k hk
          change laneWord out id.val k = _
          rw [words,ite_eq_left ⟨rfl,by omega⟩,packed _ (by omega) _ hk]
      · obtain ⟨z,w⟩ := old i (by omega)
        refine ⟨z,fun nz => ?_⟩
        obtain ⟨value,bytesEq,packed⟩ := w nz
        refine ⟨value,bytesEq,fun k hk => ?_⟩
        change laneWord out i k = _
        rw [words,ite_eq_right (by omega)]
        exact packed k hk
  · rintro it ⟨s,t⟩ last stop
    unfold sign_loop0_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeShakeWots.Signer
