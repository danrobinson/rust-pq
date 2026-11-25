import ForsDriver.LowSource
import Cachepath.NativeVerify.ForsWideRowsLeaves
import Cachepath.NativeVerify.ForsWideRowsPairs
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option maxHeartbeats 1300000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]

def nodeValue {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (h i : Nat) :=
  Spec.forsNode (Shake.params p) (bytes sk.val) i h (bytes seed.val) (adrsS a)

private theorem prefix_at {α} [Inhabited α] {cap : Usize} (a : Array α cap) (count : Usize) (part : Slice α)
    (take : part.val=List.slice 0 count.val a.to_slice.val) (fit : count.val ≤ cap.val) (j : Nat) (live : j < count.val) :
    part.val[j]! = a.val[j]! := by
  rw [take,List.getElem!_slice _ _ _ _ (by simp;omega),Nat.zero_add,Array.val_to_slice]

private theorem placed {α} [Inhabited α] {cap : Usize} (a b : Array α cap) (part : Slice α) (count : Nat)
    (fit : count ≤ cap.val) (size : part.length=count) (write : b.val=a.val.setSlice! 0 part.val)
    (j : Nat) (live : j < count) : b.val[j]! = part.val[j]! := by
  rw [write,List.getElem!_setSlice!_middle _ _ _ _ (by simp [size];omega),Nat.sub_zero]

theorem leaf_prefix {N cap : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (ids : Array U32 cap) (count : Usize)
    (fit : count.val ≤ cap.val) (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    leafPrefix sk seed a ids count ⦃ out => ∀ j < count.val,
      bytes out.val[j]!.val=nodeValue p sk seed a 0 ids.val[j]!.val ⦄ := by
  unfold leafPrefix
  step as ⟨s,take,taken⟩
  step as ⟨pair,_,length,save⟩
  obtain ⟨part,back⟩ := pair
  dsimp only at length save ⊢
  step with ForsWideRows.leaves_spec p hp sk seed a s part (by omega) domain perm as ⟨hashed,ok⟩
  obtain ⟨hl,rows⟩ := ok
  intro j hj
  have read := prefix_at ids count s take fit j hj
  have stored := placed (Array.repeat cap (Array.repeat N 0#u8)) (back hashed) hashed count.val fit (by omega) (save hashed) j hj
  rw [stored,rows j (by omega)];dsimp only;rw [read];rfl

theorem pair_prefix {N cap childCap : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a tree : address.Adrs) (height : U32) (childHeight : Nat) (ids : Array U32 cap)
    (children : Array (Array U8 N) childCap) (count childCount : Usize)
    (fit : count.val ≤ cap.val) (childFit : childCount.val ≤ childCap.val) (enough : 2*count.val ≤ childCount.val)
    (eqTree : adrsS tree=adrsS a) (up : height.val=childHeight+1)
    (left : ∀ t < count.val, bytes children.val[2*t]!.val=nodeValue p sk seed a childHeight (2*ids.val[t]!.val))
    (right : ∀ t < count.val, bytes children.val[2*t+1]!.val=nodeValue p sk seed a childHeight (2*ids.val[t]!.val+1))
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    pairPrefix seed tree height ids children count childCount ⦃ out => ∀ j < count.val,
      bytes out.val[j]!.val=nodeValue p sk seed a (childHeight+1) ids.val[j]!.val ⦄ := by
  unfold pairPrefix
  step as ⟨s,take,taken⟩
  step as ⟨l,childSlice,childSize⟩
  step as ⟨pair,_,length,save⟩
  obtain ⟨part,back⟩ := pair
  dsimp only at length save ⊢
  step with ForsWideRows.pairs_spec p hp seed tree height s l part (by omega) (by omega) perm as ⟨hashed,ok⟩
  obtain ⟨hl,rows⟩ := ok
  intro j hj
  have stored := placed (Array.repeat cap (Array.repeat N 0#u8)) (back hashed) hashed count.val fit (by omega) (save hashed) j hj
  rw [stored,rows j (by omega)]
  unfold ForsWideRows.parentRow
  rw [prefix_at ids count s take fit j hj,prefix_at children childCount l childSlice childFit (2*j) (by omega),
    prefix_at children childCount l childSlice childFit (2*j+1) (by omega),left j hj,right j hj,eqTree,up]
  rfl

end slhdsa.ForsDriver
