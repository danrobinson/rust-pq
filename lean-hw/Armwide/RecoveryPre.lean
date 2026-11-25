import Armwide.RecoveryPreProgram
import Armwide.RecoveryFrame
import Slhdsa.Proofs.Util
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Armwide.Recovery
open WotsRefill
set_option maxHeartbeats 1200000
abbrev digit (ds : Slice U32) (i : Nat) := ds.val[i]!.val
def signatureRow (n : Nat) (sig : Slice U8) (i : Nat) := ((slhdsa.bytes sig.val).drop (i*n)).take n
def copied (n : Nat) (sig : Slice U8) (ds : Slice U32) (done i : Nat) :=
  if i<done ∧ digit ds i=15 then signatureRow n sig i else []

theorem sig_row_size (n : Nat) (sig : Slice U8) (count : Nat) (fits : count*n≤sig.length) (i : Nat) (hi : i<count) :
    (signatureRow n sig i).length=n := by
  have b := Nat.mul_le_mul_right n (show i+1≤count by omega)
  rw [Nat.succ_mul] at b
  simp [signatureRow,slhdsa.bytes_length,Nat.min_eq_left (show n≤sig.length-i*n by omega)]

private theorem bytes_store (s data : List U8) (idx : Nat) :
    slhdsa.bytes (s.setSlice! idx data) = (slhdsa.bytes s).setSlice! idx (slhdsa.bytes data) := by
  simp [slhdsa.bytes,List.setSlice!,List.map_take,List.map_drop]

theorem prepare_spec (N : Usize) (width : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (ds : Slice U32) (sig buf : Slice U8) (count : ds.length=2*N.val+3)
    (valid : ∀ i<ds.length, digit ds i≤15) (fits : ds.length*N.val≤sig.length)
    (zero : buf.val=List.replicate (Keygen.total N.val) 0#u8) :
    prepare N ds sig buf ⦃ r =>
      (∀ j<ds.length, r.1.val[j]!.val=15-digit ds j) ∧
      slhdsa.bytes r.2.val=frame N.val ds.length (copied N.val sig ds ds.length) ∧ r.2.length=Keygen.total N.val ⦄ := by
  let n := N.val
  have cap : ds.length≤67 := by rcases width with h|h|h <;> omega
  have space : 22+ds.length*N.val≤Keygen.total N.val := by
    rw [count];rcases width with h|h|h <;> rw [h] <;> decide
  have total : Keygen.total N.val≤2304 := by rcases width with h|h|h <;> rw [h] <;> decide
  unfold prepare prepare_loop
  let I (i : Nat) (b : Slice U8) (w : Array U32 67#usize) :=
    b.length=Keygen.total n ∧ slhdsa.bytes b.val=frame n ds.length (copied n sig ds i) ∧
    ∀ j<ds.length, w.val[j]!.val=if j < i then 15-digit ds j else 0
  apply loop.spec_decr_nat (measure := fun (q : core.ops.range.Range Usize × Slice U8 × Array U32 67#usize) => ds.length-q.1.start.val)
    (inv := fun q => q.1.end=ds.len ∧ q.1.start.val≤ds.length ∧ I q.1.start.val q.2.1 q.2.2)
  · rintro ⟨it,b,w⟩ ⟨stop,bound,blen,data,weights⟩
    dsimp only at stop bound blen data weights ⊢
    unfold prepare_loop.body
    by_cases more : it.start.val<ds.length
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rwa [stop]) as ⟨_,it',tag,idx,ends⟩
      simp only [tag]
      step with Slice.index_usize_spec ds it.start more as ⟨d,read⟩
      have dv : d.val=digit ds it.start.val := by simp [digit,read,more]
      have wt := valid it.start.val more
      by_cases max : d=15#u32
      · have d15 : digit ds it.start.val=15 := by rw [←dv,max];rfl
        simp only [max,↓reduceIte]
        have upto := Nat.mul_le_mul_right N.val (show it.start.val+1≤ds.length by omega)
        rw [Nat.succ_mul] at upto
        have positive : 0<N.val := by omega
        step as ⟨start,startEq⟩
        step as ⟨dest,destEq⟩
        step as ⟨k,kEq⟩
        step as ⟨finish,finishEq⟩
        have finishVal : finish.val=start.val+N.val := by rw [finishEq,kEq,Nat.add_mul,startEq];simp
        step as ⟨finishDest,finishDestEq⟩
        step as ⟨s,back,_,sz,write⟩
        step as ⟨finish',finishEq'⟩
        step as ⟨src,srcEq,srcLen⟩
        step as ⟨cop,eq⟩
        case h => omega
        refine ⟨ends.trans stop,by omega,⟨?_,?_,?_⟩,by omega⟩
        · change (back cop).val.length=_
          rw [write];simpa using blen
        · have js : slhdsa.bytes cop.val=signatureRow n sig it.start.val := by
            rw [eq,srcEq]
            simp [signatureRow,List.slice,slhdsa.bytes,n,startEq,finishEq',kEq,Nat.add_mul]
          have copyEq := write_frame n ds.length (copied n sig ds it.start.val) it.start.val _ more
            (sig_row_size _ _ _ fits _ more)
          have acc : setOut (copied n sig ds it.start.val) it.start.val (signatureRow n sig it.start.val) =
              copied n sig ds it'.start.val := by
            funext j
            by_cases same : j=it.start.val
            · subst j;simp [copied,setOut,idx,d15]
            · have equiv : j < it'.start.val ↔ j < it.start.val := by omega
              simp [copied,setOut,same,equiv]
          rw [←acc,←copyEq]
          rw [write,Slice.setSlice!_val,bytes_store,data,js]
          simp [writeAt,n,destEq,startEq]
        · intro j hj
          rw [weights j hj]
          by_cases eq : j=it.start.val
          · subst j;simp [d15,idx]
          · have h : j < it'.start.val ↔ j < it.start.val := by omega
            simp [h]
      · have ne : digit ds it.start.val≠15 := by
          intro eq;apply max;apply UScalar.eq_of_val_eq;exact dv.trans eq
        simp only [ite_eq_right max]
        step as ⟨new,val⟩
        step with Array.update_spec w it.start new (by simp;omega) as ⟨w',upd⟩
        refine ⟨ends.trans stop,by omega,⟨blen,?_,?_⟩,by omega⟩
        · rw [data];congr 1;funext j
          by_cases same : j=it.start.val
          · subst j;simp [copied,ne]
          · have equiv : j < it'.start.val ↔ j < it.start.val := by omega
            simp [copied,equiv]
        · intro j hj
          rw [upd,Array.set_val_eq]
          by_cases same : j=it.start.val
          · subst j;rw [List.set_getElem!_eq _ _ _ _ ⟨by simp;omega,rfl⟩];simp [val,dv,idx]
          · have h : j < it'.start.val ↔ j < it.start.val := by omega
            rw [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm same)]
            simpa only [List.getElem!_eq_getElem?_getD,h] using weights j hj
    · have done : it.start.val=ds.length := by omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop];change ds.length ≤ it.start.val;omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact ⟨fun j hj => by simpa [done,hj] using weights j hj,done ▸ data,blen⟩
  · refine ⟨rfl,by simp,?_,?_,?_⟩
    · change buf.val.length=_;rw [zero,List.length_replicate]
    · change slhdsa.bytes buf.val=frame n ds.length (copied n sig ds 0)
      have out : copied n sig ds 0=(fun _ => []) := by funext j;simp [copied]
      rw [out,count,frame_zero _ width,zero];simp [slhdsa.bytes,n]
    · intro j hj
      change ((Array.repeat 67#usize 0#u32).val[j]!).val = if j < 0 then _ else 0
      rw [Array.repeat_val,List.getElem!_replicate _ (by change j<67;omega)]
      simp

end slhdsa.Armwide.Recovery
