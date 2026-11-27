import Cachepath.NativeVerify.ForsWideRowsStore
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ForsWideRows
open ShakeBatch
set_option maxHeartbeats 1800000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance rowsLeafMachine : Machine := Fused.machine kernel

theorem leaves_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (indices : Slice U32) (out : Slice (Array U8 N)) (length : out.length=indices.length)
    (dom : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    leaves sk seed a indices out ⦃ result => Filled (fun j => Spec.forsNode (Shake.params p) (bytes sk.val)
      indices.val[j]!.val 0 (bytes seed.val) (adrsS a)) indices.length indices.length result ⦄ := by
  let target := fun j : Nat => Spec.forsNode (Shake.params p) (bytes sk.val) indices.val[j]!.val 0 (bytes seed.val) (adrsS a)
  change leaves sk seed a indices out ⦃ r => Filled target indices.length indices.length r ⦄
  unfold leaves leaves_loop
  apply loop.spec_decr_nat (measure := fun q : Slice (Array U8 N) × Usize => indices.length-q.2.val)
    (inv := fun q => q.2.val ≤ indices.length ∧ Filled target indices.length q.2.val q.1)
  · rintro ⟨buf,i⟩ ⟨inside,old⟩
    simp only at inside old ⊢
    unfold leaves_loop.body
    dsimp only
    split
    · rename_i more
      have shorter : i.val < indices.length := more
      step as ⟨left,leftVal⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min left 8#usize
      have count : active.val=min (indices.length-i.val) 8 := (min_count _).trans (by rw [leftVal];rfl)
      have size : active.val ≤ 8 := by omega
      have nonzero : 0 < active.val := by omega
      have room : i.val+active.val ≤ indices.length := by omega
      step as ⟨part,back,_,plen,save⟩
      step as ⟨stop,sv⟩
      change stop.val=i.val+active.val at sv
      step as ⟨src,take,taken⟩
      change part.length=active.val at plen
      step as ⟨cp,copy⟩
      all_goals try omega
      have vals (j : Nat) (live : j < active.val) : (back cp).val[j]! = indices.val[i.val+j]! := by
        rw [save,copy,List.getElem!_setSlice!_middle _ _ _ _ (by change _ ∧ j-0 < src.length ∧ j < 8;omega),
          Nat.sub_zero,take,List.getElem!_slice _ _ _ _ (by change stop.val ≤ indices.length ∧ _;omega)]
      step with ForsFused.leaf_correct kernel.active perm p hp sk seed a (back cp) active dom size as ⟨rows,hashed⟩
      erw [←writeBind buf i stop active rows (fun buf' => ok (cont (buf',stop)))]
      step with write_rows buf i stop active rows target indices.length old sv (by omega) size (by
        intro j hj; rw [hashed j hj,vals j hj]) as ⟨result,updated⟩
      exact ⟨by omega,updated,by omega⟩
    · rename_i stop
      simp only [step_simps]
      exact (show i.val=indices.length by change ¬ i.val < indices.length at stop;omega) ▸ old
  · exact ⟨Nat.zero_le _,length,by intro j hj;change j < 0 at hj;omega⟩
end slhdsa.NativeVerify.ForsWideRows
