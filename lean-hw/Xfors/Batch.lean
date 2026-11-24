import Xfors.Level
import Parentdriver.Proof
import Parent256.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Fors
open XForsRust (scalarSeed scalarAddr)

def vectorParents {N : Usize} (seed : XForsRust.hash.Seed N) (a : XForsRust.address.Adrs) (first : U32)
    (nodes : Nodes N) (n : Usize) : Result (Nodes N × Usize) :=
  if N=16#usize then do
    let (s,back) ← lift (Array.to_slice_mut nodes)
    let (num,out) ← XForsRust.sha256.x86.fors_parents seed.state a first s n
    ok (back out,num)
  else do
    let (s,back) ← lift (Array.to_slice_mut nodes)
    let (num,out) ← XForsRust.sha512.parents.parents seed.state512 a first s n
    ok (back out,num)

theorem vector_spec {N} (p : params.Params) (hp : PN p N) (seed : XForsRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (scalarSeed seed))) (a : XForsRust.address.Adrs) (first : U32)
    (nodes : Nodes N) (n : Usize) (small : n.val≤64) (room : first.val+n.val≤2^32)
    (cpu : GatherRust.avx512Available=true) :
    vectorParents seed a first nodes n ⦃ out num => num.val≤n.val ∧
      (∀ j<num.val, bytes out.val[j]!.val=parent p seed a first nodes j) ∧
      (∀ j, num.val≤j → j<128 → out.val[j]! = nodes.val[j]!) ⦄ := by
  unfold vectorParents
  split
  · rename_i width
    subst N
    step as ⟨s,back,input,restore⟩
    have length : s.length=128 := by simp [Slice.length,input]
    unfold XForsRust.sha256.x86.fors_parents
    step with Parent.fors_parents_spec (paramsS p) (bytes seed.pk_seed.val) seed.state (XForsRust.parentAddr a)
      first s n rfl hp.n (by simp) hs.1 cpu (by omega) room (by scalar_tac) as ⟨num,rows,result⟩
    by_cases few : n.val<2
    · simp only [if_pos few] at result
      obtain ⟨rfl,rfl⟩ := result
      have out : (back rows).val=nodes.val := by rw [restore,Array.from_slice_val nodes rows (by simpa using length),input]
      simp [out]
    · simp only [if_neg few] at result
      obtain ⟨numEq,count,completed⟩ := result
      subst num
      have out : (back rows).val=rows.val := by rw [restore,Array.from_slice_val]; exact count.trans length
      refine ⟨le_rfl,?_,?_⟩
      · intro j hj
        have got := completed j (by omega)
        simp only [if_pos hj] at got
        rw [out]
        simpa only [Parent.expected,Parent.children,input,Array.val_to_slice,parent,addressOf,TreeHash.addr,
          scalarAddr,Parent.addressOf,XForsRust.parentAddr] using got
      · intro j hj endPos
        have got := completed j (by omega)
        simp only [if_neg (by omega : ¬j<n.val)] at got
        simpa only [out,input,Array.val_to_slice] using got
  · rename_i other
    have width : N.val=24 ∨ N.val=32 := by rcases hp.nok with h|h|h <;> scalar_tac
    step as ⟨s,back,input,restore⟩
    have length : s.length=128 := by simp [Slice.length,input]
    unfold XForsRust.sha512.parents.parents
    step with PlatformParent.Driver.x86_tree_spec (paramsS p) (bytes seed.pk_seed.val) (XForsRust.coreAddr a)
      seed.state512 first s n width rfl hp.n (by simp) (hs.2 (by scalar_tac)) (by omega) room
      as ⟨num,rows,count,reduced⟩
    obtain ⟨rowsLen,completed⟩ := reduced
    have bound : num.val≤n.val := by rw [count,PlatformParent.Driver.processed,cpu]; simp; omega
    have out : (back rows).val=rows.val := by rw [restore,Array.from_slice_val]; exact rowsLen.trans length
    refine ⟨bound,?_,?_⟩
    · intro j hj
      have got := completed j (by omega)
      simp only [if_pos hj] at got
      rw [out]
      simpa only [PlatformParent.Driver.nodeBytes,PlatformParent.Driver.parentAt,PlatformParent.Driver.treeAddress,
        PlatformParent.Driver.children,input,Array.val_to_slice,parent,addressOf,TreeHash.addr,scalarAddr,XForsRust.coreAddr] using got
    · intro j hj endPos
      have got := completed j (by omega)
      simp only [if_neg (by omega : ¬j<num.val)] at got
      simpa only [out,input,Array.val_to_slice] using got

end slhdsa.X86.Fors
