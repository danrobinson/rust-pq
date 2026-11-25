import Parallel.ForsMetaProgram
import Parallel.ForsTicketIndices
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsMetadata
open ParallelForsMerge (Meta)
instance : Inhabited Meta := ⟨⟨0#u32,0#u32,0#u32,0#u32,0#usize,0#usize⟩⟩
abbrev Table := alloc.vec.Vec Meta

def target (simd : Bool) (a : Nat) := if a≥10 then 9 else if simd && a≥9 then 8 else a

theorem targets (a : U32) :
    target_wide a ⦃ z => z.val=target true a.val ⦄ ∧ target_group a ⦃ z => z.val=target true a.val ⦄ ∧
    target_scalar a ⦃ z => z.val=target false a.val ⦄ := by
  have t : (a≥10#u32) ↔ a.val≥10 := Iff.rfl
  have n : (a≥9#u32) ↔ a.val≥9 := Iff.rfl
  by_cases ten : 10≤a.val <;> by_cases nine : 9≤a.val <;>
    simp [target_wide,target_group,target_scalar,t,n,ten,nine,target,step_simps]

def Record (choices : alloc.vec.Vec U32) (a j sub : U32) (t start : Nat) (m : Meta) :=
  m.tree.val=t ∧ m.height=j ∧ m.root_idx.val=ForsDriver.sibling choices.slice a t j.val ∧ m.sub_h=sub ∧
    m.slot_start.val=start ∧ m.chunks.val=2^(j.val-sub.val)

def Emitted (choices : alloc.vec.Vec U32) (a j sub : U32) (first n start : Nat) (old new : Table) :=
  new.length=old.length+n ∧ (∀ i < old.length, new.val[i]! = old.val[i]!) ∧
  ∀ l<n, Record choices a j sub (first+l) (start+l*2^(j.val-sub.val)) new.val[old.length+l]!

theorem append_record (choices : alloc.vec.Vec U32) (a j sub : U32) (f n start : Nat) (old cur out : Table)
    (m : Meta) (prev : Emitted choices a j sub f n start old cur)
    (record : Record choices a j sub (f+n) (start+n*2^(j.val-sub.val)) m)
    (push : out.val=cur.val++[m]) : Emitted choices a j sub f (n+1) start old out := by
  obtain ⟨len,frame,previous⟩ := prev
  refine ⟨?_,?_,?_⟩
  · change out.val.length=_
    rw [push,List.length_append];change cur.length+1=_;omega
  · intro i bound
    rw [push,List.getElem!_append_left _ _ _ (by change i<cur.length;omega),frame i bound]
  · intro i bound
    rw [push]
    by_cases same : i=n
    · subst i
      rw [←len,List.getElem!_append_right _ _ _ (by rfl)]
      simpa [alloc.vec.Vec.length] using record
    · rw [List.getElem!_append_left _ _ _ (by change _<cur.length;omega)]
      exact previous i (by omega)

theorem offset (t h j : U32) (d : U32) (low : d.val=h.val-j.val) (tree : t.val<35) (height : h.val≤14) :
    t <<< d ⦃ b => b.val=t.val*2^(h.val-j.val) ⦄ := by
  obtain ⟨sh,_⟩ := fors_shl_arith d.val t.val (by omega) tree
  step with U32.ShiftLeft_spec t d (by omega) as ⟨_,eq,_⟩
  rw [eq];simpa [U32.size,U32.numBits,low] using sh

theorem root_value (choices : alloc.vec.Vec U32) (a j : U32) (t : Nat) (base digit : U32)
    (ha : a.val≤14) (below : j.val<a.val) (count : choices.length≤35) (live : t<choices.length)
    (selected : choices.val[t]!.val<2^a.val) (bv : base.val=t*2^(a.val-j.val))
    (read : digit=choices.val[t]!) :
    (do let high ← digit >>> j; let f ← lift (high ^^^ 1#u32);base+f)
      ⦃ out => out.val=ForsDriver.sibling choices.slice a t j.val ⦄ := by
  have room := ParallelForsTicket.sibling_room choices a j t ha below count live selected
  have small := Nat.le_mul_of_pos_right (ParallelForsTicket.sibling choices a j t+1) (Nat.two_pow_pos j.val)
  have eq := ForsDriver.sibling_local choices.slice a t j.val below
  change ParallelForsTicket.sibling choices a j t=t*2^(a.val-j.val)+((choices.val[t]!.val/2^j.val)^^^1) at eq
  step as ⟨high,hv,_⟩
  simp only [lift,bind_ok]
  have flip : (high^^^1#u32).val=(choices.val[t]!.val/2^j.val)^^^1 := by simp [UScalar.val_xor,hv,read,Nat.shiftRight_eq_div_pow]
  have fit : base.val+(high^^^1#u32).val≤U32.max := by rw [bv,flip,←eq,U32.max_eq];omega
  step as ⟨out,res⟩
  rw [res,bv,flip];exact eq.symm

theorem chunk_count (j sub d : U32) (diff : d.val=j.val-sub.val) (height : j.val<14) :
    1#usize <<< d ⦃ out => out.val=2^(j.val-sub.val) ⦄ := by
  have platform := System.Platform.le_numBits
  have small := Nat.pow_le_pow_right (by decide : 0<2) (show d.val≤14 by omega)
  step as ⟨groups,eq,_⟩
  all_goals first | (rw [eq,Nat.one_shiftLeft,diff,Nat.mod_eq_of_lt];scalar_tac) | scalar_tac

theorem scalar (sat : Bool) (choices : alloc.vec.Vec U32) (a j sub : U32) (start : Usize) (t : U32)
    (old : Table) (ha : a.val≤14) (below : j.val<a.val) (count : choices.length≤35) (live : t.val<choices.length)
    (selected : choices.val[t.val]!.val<2^a.val) (lower : sub.val<j.val)
    (space : start.val+2^(j.val-sub.val)≤Usize.max) (capacity : old.length<Usize.max) :
    (if sat then meta_wide else meta_scalar) choices a j sub start t old ⦃ next out =>
      next.val=start.val+2^(j.val-sub.val) ∧ Emitted choices a j sub t.val 1 start.val old out ⦄ := by
  have subSpec : (j-sub) ⦃ d => d.val=j.val-sub.val ⦄ := by step <;> scalar_tac
  obtain ⟨d,run,diff⟩ := spec_imp_exists subSpec
  have satVal : (core.num.U32.saturating_sub j sub).val=j.val-sub.val := by
    change (0 ⊔ (j.val-sub.val)) % 2^32=_
    rw [Nat.max_eq_right (Nat.zero_le _),Nat.mod_eq_of_lt (by omega)]
  have ds : core.num.U32.saturating_sub j sub=d := UScalar.eq_of_val_eq (satVal.trans diff.symm)
  have cast := U32.cast_Usize_val_eq t
  cases sat <;> simp only [Bool.false_eq_true,ite_false,ite_true,meta_wide,meta_scalar,lift,bind_ok,run,ds]
  all_goals
    step as ⟨digit,read⟩
    step as ⟨shift,sv⟩
    step with offset t a j shift sv (by omega) ha as ⟨base,bv⟩
    have rd : digit=choices.val[t.val]! := by rw [read,←getElem!_pos,cast]
    obtain ⟨root,rootRun,rv⟩ := spec_imp_exists (root_value choices a j t.val base digit ha below count live selected bv rd)
    have joined {α} (f : U32 → Result α) : (do let high ← digit >>> j;let r ← base+(high^^^1#u32);f r)=f root := by
      simpa only [Std.bind_assoc,bind_tc_eq,lift,bind_ok] using congrArg (fun v : Result U32 => v >>= f) rootRun
    rw [joined]
    step with chunk_count j sub d diff (by omega) as ⟨chunks,cv⟩
    step as ⟨next,nv⟩
    step as ⟨out,push⟩
    refine ⟨by rw [nv,cv],?_⟩
    apply append_record choices a j sub t.val 0 start.val old old out ⟨t,j,root,sub,start,chunks⟩ (by simp [Emitted])
    · simp [Record,rv,cv]
    · exact push
end slhdsa.ForsMetadata
