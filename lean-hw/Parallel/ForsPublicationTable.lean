import Parallel.ForsFieldPack
import Parallel.RawSlotOrder
namespace slhdsa.RawFors
open Aeneas Aeneas.Std Result WidthEight.Ticket

abbrev Action (N : Usize) := Nat → Nat → Result (Cell N)

def Issued {N} (mode : Mode) (d : Data N) (actions : Action N) :=
  ∀ t<d.p.k.val, ∀ c≤d.p.a.val, Receipt mode d (owner mode.policy d.p.a.val t c) (actions t c)

/-- Each physical write checks its returned destination against the owner’s
physical slot. The checked counter trace may complete tickets in any order. -/
def fieldAt {N} (p : params.Params) (actions : Action N) (index : Nat) : Result (Array U8 N) := do
  let stride := p.a.val+1
  let (dest,row) ← actions (index/stride) (index%stride)
  if dest.val=index then ok row else fail .panic

def publish {N} (p : params.Params) (actions : Action N) (schedule : ∀ n, Schedule n) : Result (Cells N) := do
  let count := p.k.val*(p.a.val+1)
  let rows ← writeRows count (fieldAt p actions) (schedule count).completed
  if fit : rows.length≤Usize.max then ok (alloc.vec.Vec.from rows fit) else fail .panic

theorem published {N} (mode : Mode) (d : Data N) (valid : Valid d) (actions : Action N)
    (issued : Issued mode d actions) (schedule : ∀ n, Schedule n) :
    publish d.p actions schedule ⦃ cells => cells.length=d.p.k.val*(1+d.p.a.val) ∧ Publications mode d cells ⦄ := by
  let stride := d.p.a.val+1
  let count := d.p.k.val*stride
  let post := fun (i : Nat) (r : Array U8 N) =>
    ∃ w, actions (i/stride) (i%stride)=ok w ∧ w.1.val=i ∧ w.2=r
  have total (i : Nat) (inside : i<count) : ∃ row, fieldAt d.p actions i=ok row ∧ post i row := by
    have h : i/stride<d.p.k.val := (Nat.div_lt_iff_lt_mul (by simp [stride])).mpr inside
    have c : i%stride≤d.p.a.val := Nat.lt_succ_iff.mp (Nat.mod_lt i (by simp [stride]))
    have ownerEq := owner_fields mode.policy d.p.a.val (i/stride) (i%stride)
    obtain ⟨⟨dest,row⟩,run,index,value⟩ := spec_imp_exists ((issued _ h _ c).correct valid)
    change dest.val=_ at index
    rw [ownerEq.1,ownerEq.2] at index
    have loc : dest.val=i := index.trans (by change i/stride*stride+i%stride=i;rw [Nat.mul_comm,Nat.div_add_mod])
    exact ⟨row,by simp only [fieldAt,←show stride=d.p.a.val+1 from rfl,run,bind_tc_eq,bind_ok];simp [loc],
      ⟨(dest,row),run,loc,rfl⟩⟩
  obtain ⟨unique,cover⟩ := ((schedule count).trace.joined (schedule count).drained).exactly_once
  obtain ⟨rs,ran,len,written⟩ := writes count (fieldAt d.p actions) post total (schedule count).completed unique
    (fun i h => (cover i).mp h)
  have cap : count≤Usize.max := by
    have bound : count≤35*15 := Nat.mul_le_mul valid.pn.valid.k_le (Nat.add_le_add_right valid.pn.valid.a_le 1)
    exact bound.trans (by scalar_tac)
  unfold publish
  change (do let rows ← writeRows count (fieldAt d.p actions) (schedule count).completed; if fit : rows.length≤Usize.max then ok (alloc.vec.Vec.from rows fit) else fail .panic) ⦃ _ => _ ⦄
  rw [ran]
  simp only [bind_ok,dite_eq_left (len ▸ cap),WP.spec_ok]
  refine ⟨by change (alloc.vec.Vec.from _ _).val.length=_;rw [alloc.vec.Vec.from_val,len];simp [count,stride,Nat.add_comm],?_⟩
  intro t tree c hc
  let i := t*stride+c
  have col : c<stride := by omega
  have hi : i<count := by have h := Nat.mul_le_mul_right stride tree;rw [Nat.succ_mul] at h;unfold i count;omega
  have ti : i/stride=t := by rw [show i=c+t*stride by simp [i,Nat.add_comm],Nat.add_mul_div_right _ _ (by simp [stride]),Nat.div_eq_of_lt col,Nat.zero_add]
  have ci : i%stride=c := by simp [i,Nat.add_mod,Nat.mod_eq_of_lt col]
  obtain ⟨r,stored,w,ran,atSlot,returnRow⟩ := (ite_eq_left ((cover i).mpr hi)) ▸ written i hi
  rw [ti,ci] at ran
  refine ⟨actions t c,issued t tree c hc,?_⟩
  intro got exec
  rw [ran] at exec
  cases Result.ok_injective exec
  simp only [Writes,alloc.vec.Vec.from_val,atSlot,returnRow,List.getElem!_eq_getElem?_getD,stored,Option.getD_some]

theorem packed {N} (mode : Mode) (d : Data N) (valid : Valid d) (md : Slice U8)
    (decoded : nats d.choices.val=Spec.base2b (bytes md.val) d.p.a.val d.p.k.val)
    (actions : Action N) (issued : Issued mode d actions) (schedule : ∀ n, Schedule n) :
    (do let cells ← publish d.p actions schedule; pack mode.rootHost d.p md d.sk d.seed d.addr cells)
      ⦃ out => bytes out.val=Spec.forsSign (Shake.params d.p) (bytes md.val) (bytes d.sk.val) (bytes d.seed.val) (adrsS d.addr) ⦄ := by
  step with published mode d valid actions issued schedule as ⟨cells,count,pub⟩
  exact pack_spec mode d valid md decoded cells count pub

end slhdsa.RawFors
