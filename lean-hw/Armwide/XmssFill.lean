import Armwide.XmssLeafValues
import Armwide.XmssFillProgram
import Armwide.Xmss.Levels
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves
open Keygen ArmXmss
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def slot (n h i : Nat) := ((slots[group n]!)[h-1]!)[i]!
private def gCount (h : Nat) := if h=1 then 2 else 4
private def baseOffset (h i : Nat) := i/gCount h*gCount h

private theorem slot_shape (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) (h : Nat)
    (pos : 0<h) (height : h≤4) :
    ∀ i : Fin (2^h), slot n h i = some ⟨h,i,h,baseOffset h i,gCount h,i%gCount h⟩ := by
  rcases width with rfl|rfl|rfl <;> interval_cases h <;> decide

private def as32 (v : Nat) : U32 := ⟨BitVec.ofNat _ v⟩
private def asSize (v : Nat) : Usize := ⟨BitVec.ofNat _ v⟩
private theorem as32_val (v : Nat) (small : v<2^32) : (as32 v).val=v :=
  Nat.mod_eq_of_lt small
private theorem asSize_val (v : Nat) (small : v<2^32) : (asSize v).val=v := by
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with x|x <;> change v<2^System.Platform.numBits <;> rw [x] <;> omega

private def preparedRow (n : Nat) (L : Usize) (a : slhdsa.address.Adrs) (key : U32) :=
  prepare (Array.repeat L 0#u8) a key (asSize (22+payLen n)) (asSize (if n=16 then 64 else 128))

private def returned {α} (m : Result α) (fallback : α) : α := by
  classical
  exact if h : ∃ r, m=ok r then h.choose else fallback

private theorem returned_ok {α} (r fallback : α) : returned (ok r) fallback=r := by
  unfold returned
  split
  · rename_i h
    simpa only [ok.injEq] using h.choose_spec.symm
  · rename_i h
    exact False.elim (h ⟨r,rfl⟩)

private def sourceRow (n : Nat) (L : Usize) (a : slhdsa.address.Adrs) (id h i : Nat) : Array U8 L :=
  match slot n h i with
  | none => Array.repeat L 0#u8
  | some s =>
    returned (preparedRow n L a (as32 (id*2^s.headerShift+s.headerOffset))) (Array.repeat L 0#u8)

/-- Each successful preparation covers the exact physical row read by its digest. -/
theorem sourceRow_prepared (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) (L : Usize) (layout : L.val=total n)
    (a : slhdsa.address.Adrs) (id h i : Nat) (pos : 0<h) (height : h≤4) (index : i<2^h)
    (bound : (id+1)*2^h≤2^32) :
    ∃ buf, preparedRow n L a (as32 (id*2^h+i)) = ok buf ∧
      sourceRow n L a id h i=buf ∧ prepared n (slhdsa.adrsS a) (id*2^h+i) buf := by
  have key : (as32 (id*2^h+i)).val=id*2^h+i := by apply as32_val; rw [Nat.add_one_mul] at bound;omega
  have size : 22+payLen n<2^32 := by rcases width with rfl|rfl|rfl <;> decide
  have block : (if n=16 then 64 else 128)<2^32 := by split <;> decide
  obtain ⟨buf,okbuf,data⟩ := spec_imp_exists (prepare_spec n width L _ _ layout (asSize_val _ size)
    (asSize_val _ block) a (as32 (id*2^h+i)))
  change preparedRow n L a (as32 (id*2^h+i)) = ok buf at okbuf
  exact ⟨buf,okbuf,by simp only [sourceRow,slot_shape n width h pos height ⟨i,index⟩,okbuf,returned_ok],
    by rwa [key] at data⟩

def messagesFor (n : Nat) (G L : Usize) (a : slhdsa.address.Adrs) (id h base : Nat) : Rows G L :=
  .from (List.ofFn (fun j : Fin G.val => sourceRow n L a id h (base+j.val))) (by simp)

def physicalLeaf {N : Usize} (L : Usize) (hard : Bool) (seed : hash.Seed N) (sk : Array U8 N)
    (a : slhdsa.address.Adrs) (id h i : Nat) : Array U8 N :=
  match slot N.val h i with
  | none => Array.repeat N 0#u8
  | some s =>
    let G := asSize s.groupSize
    let base := as32 (id*2^s.baseShift+s.baseOffset)
    let msgs := messagesFor N.val G L a id h s.baseOffset
    let data := endpoints seed.state sk a base msgs
    row N <| if N.val=16 then digest256 seed.state data s.lane else digest512 (N:=N) hard seed.state512 data s.lane

def leafBuffer {N : Usize} (L : Usize) (hard : Bool) (seed : hash.Seed N) (sk : Array U8 N)
    (a : slhdsa.address.Adrs) (id h : Nat) : Nodes N :=
  .from (List.ofFn (fun i : Fin 16 => physicalLeaf L hard seed sk a id h i.val)) (by simp)

theorem fill_correct {N : Usize} (p : params.Params) (hp : PN p N) (L : Usize) (layout : L.val=total N.val)
    (hard : Bool) (seed : hash.Seed N) (hs : SeedOk seed) (sk : Array U8 N) (a : slhdsa.address.Adrs)
    (id h : Nat) (pos : 0<h) (height : h≤4) (bound : (id+1)*2^h≤2^32) :
    levelSpec p seed sk a id h 0 (leafBuffer L hard seed sk a id h) := by
  intro i hi
  simp only [Nat.sub_zero] at hi ⊢
  have sz : 2^h≤16 := by interval_cases h <;> decide
  have lt : i<16 := by omega
  simp only [leafBuffer,Array.from_val,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,lt,↓reduceDIte,Option.getD_some]
  unfold physicalLeaf
  rw [slot_shape N.val hp.nok h pos height ⟨i,hi⟩]
  let g:=gCount h
  let off:=baseOffset h i
  let k:=i%g
  have groups : g=2 ∨ g=4 := by unfold g gCount; split <;> simp
  have lane : k<g := Nat.mod_lt _ (by omega)
  have geom : off+k=i := by unfold off baseOffset k g; rw [Nat.mul_comm,Nat.div_add_mod]
  have groupVal : (asSize g).val=g := asSize_val _ (by omega)
  have keyVal : (as32 (id*2^h+off)).val=id*2^h+off := by
    apply as32_val; rw [Nat.add_one_mul] at bound;omega
  have kl : k < (asSize g).val := by rwa [groupVal]
  obtain ⟨buf,_,out,correct⟩ := sourceRow_prepared N.val hp.nok L layout a id h i pos height hi bound
  let msgs:=messagesFor N.val (asSize g) L a id h off
  have prep : prepared N.val (slhdsa.adrsS a) ((as32 (id*2^h+off)).val+k) msgs.val[k]! := by
    simp only [msgs,messagesFor,Array.from_val,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,kl,↓reduceDIte,
      Option.getD_some,geom,out,keyVal,Nat.add_assoc]
    exact correct
  have value:=leafValue p hp seed hs sk a (as32 (id*2^h+off)) msgs (by rwa [groupVal]) layout k kl hard prep
  rw [keyVal,Nat.add_assoc,geom] at value
  change slhdsa.bytes (row N _).val = _
  rw [value,row_eq N _ (by rw [Spec.xmssNode_length _ hp.valid,hp.n])]

end
end slhdsa.Armwide.XmssLeaves
