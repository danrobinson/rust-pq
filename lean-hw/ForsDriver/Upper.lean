import ForsDriver.Fields
import ForsDriver.ForsIndices
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsDriver
open ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1200000
variable [trees : Trees]

def UpperNodes {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) :=
  ∀ i z : U32, 3≤z.val → z.val≤14 → (i.val+1)*2^z.val≤1048576 →
    trees.node sk seed a i z ⦃ row => bytes row.val=Spec.forsNode (Shake.params p) (bytes sk.val)
      i.val z.val (bytes seed.val) (adrsS a) ⦄

omit trees in
private theorem sibling_room (leaf z : Nat) (small : leaf<2^20) (height : z≤14) :
    (((leaf/2^z)^^^1)+1)*2^z≤1048576 := by
  have split : 2^z*2^(20-z)=2^20 := by rw [←Nat.pow_add];congr 1;omega
  have divides : leaf/2^z<2^(20-z) := Nat.div_lt_of_lt_mul (by rw [split];exact small)
  have one : 1<2^(20-z) := by
    exact lt_of_lt_of_le (by decide : 1<2^1) (Nat.pow_le_pow_right (by decide) (by omega))
  have bound := Nat.mul_le_mul_right (2^z) (Nat.succ_le_of_lt (Nat.xor_lt_two_pow divides one))
  rwa [Nat.mul_comm (2^(20-z)),split] at bound

private theorem upper_row {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) (stride t : Usize) (leaf : U32) (sig : Buffer)
    (shape : stride.val=(p.a.val+1)*N.val) (lo : 3≤p.a.val) (okTree : t.val<choices.length)
    (leafEq : leaf.val=t.val*2^p.a.val+choices.val[t.val]!.val) (small : leaf.val<2^20)
    (nodes : UpperNodes p sk seed a)
    (old : Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed a choices)
      (fun i z => z≤3 ∨ i<t.val) sig) :
    sign_loop8_loop0 ⟨3#u32,p.a⟩ sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 stride sig t leaf
      ⦃ out => Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed a choices)
        (fun i z => z≤3 ∨ i<t.val+1) out ⦄ := by
  let P := fun (n : Nat) (out : Buffer) => Fields N.val choices.length (p.a.val+1) stride.val
    (treeBlock p sk seed a choices) (fun i z => z≤3 ∨ i<t.val ∨ i=t.val ∧ z≤n) out
  unfold sign_loop8_loop0
  apply WP.spec_mono (P₀ := fun out => P p.a.val out) ?_ (by
    intro out post
    exact Fields.mono post (by intros;omega))
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Buffer => p.a.val-q.1.start.val)
    (inv := fun q => q.1.end=p.a ∧ 3≤q.1.start.val ∧ q.1.start.val≤p.a.val ∧ P q.1.start.val q.2)
  · rintro ⟨it,cur⟩ ⟨he,minH,maxH,prior⟩
    simp only at he minH maxH prior ⊢
    unfold sign_loop8_loop0.body
    by_cases more : it.start.val < it.end.val
    · have inside : it.start.val<p.a.val := he ▸ more
      have boundH : it.start.val≤14 := (Nat.le_of_lt inside).trans hp.valid.a_le
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨q,shift,_⟩
      simp only [lift,bind_ok]
      let sib := q ^^^ 1#u32
      have eq : sib.val=(leaf.val/2^it.start.val)^^^1 := by simp [sib,UScalar.val_xor,shift,Nat.shiftRight_eq_div_pow]
      step with nodes sib it.start minH boundH (eq ▸ sibling_room _ _ small boundH) as ⟨row,digest⟩
      have len := prior.1
      have max : cur.length≤Usize.max := by simp
      have block := Nat.mul_le_mul_right stride.val okTree
      rw [Nat.succ_mul] at block
      have within := Nat.mul_le_mul_right N.val (show it.start.val+1<p.a.val+1 by omega)
      rw [Nat.succ_mul,←shape] at within
      have cast : (UScalar.cast .Usize it.start).val=it.start.val :=
        UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
      step as ⟨base,bv⟩
      step as ⟨col,cv⟩
      step as ⟨offset,ov⟩
      step as ⟨pos,pv⟩
      step as ⟨stop,sv⟩
      step as ⟨dst,back,data,length,save⟩
      step as ⟨w,cp⟩
      all_goals try scalar_tac
      refine ⟨ends.trans he,by omega,by omega,?_,by omega⟩
      apply Fields.store _ _ _ cur _ row t.val (it.start.val+1) okTree (by omega) shape prior
      · rw [save,cp,Array.val_to_slice]
        simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,pv,bv,ov,cv,cast]
      · rw [auth_block _ _ _ _ _ _ _ inside,digest,eq,leafEq]
      · intro i z hi hz was
        omega
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      have eq : it.start.val=p.a.val := by rw [he] at more;omega
      simpa only [eq] using prior
  · exact ⟨rfl,by change 3≤3;decide,lo,old.mono (by intro i z hi hz present;change z≤3 ∨ i<t.val ∨ i=t.val ∧ z≤3 at present;omega)⟩

theorem upper {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) (stride : Usize) (sig : Buffer)
    (shape : stride.val=(p.a.val+1)*N.val) (lo : 3≤p.a.val) (size : choices.length≤35)
    (digits : ∀ i<choices.length, choices.val[i]!.val<2^p.a.val) (nodes : UpperNodes p sk seed a)
    (old : Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed a choices)
      (fun _ z => z≤3) sig) :
    sign_loop8 ⟨0#usize,Slice.len choices⟩ choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride sig
      ⦃ out => Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed a choices)
        (fun _ _ => True) out ⦄ := by
  let P := fun (n : Nat) (cur : Buffer) => Fields N.val choices.length (p.a.val+1) stride.val
    (treeBlock p sk seed a choices) (fun i z => z≤3 ∨ i<n) cur
  unfold sign_loop8
  apply WP.spec_mono (P₀ := fun out => P choices.length out) ?_ (by intro out post;exact Fields.mono post (by intros;omega))
  apply range_fold (sign_loop8.body choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride)
    (Slice.len choices) sig P (old.mono (by simp))
  · intro it cur stop live prior
    change it.start.val<choices.length at live
    unfold sign_loop8.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    obtain ⟨leaf,run,eq,bound⟩ := read_absolute choices p.a it.start hp.valid.a_le live size (digits _ live)
    rw [read_bind choices p.a it.start run]
    step with upper_row p hp choices sk seed a stride it.start leaf cur shape lo live eq bound nodes prior as ⟨out,post⟩
    exact ⟨next,out,rfl,ends.trans stop,inc,by simpa [P,inc] using post⟩
  · intro it cur last stop
    obtain ⟨_,no⟩ := range_done it _ stop last
    simp [sign_loop8.body,no]

end slhdsa.ForsDriver
