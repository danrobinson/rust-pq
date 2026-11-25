import Parallel.XmssTicketProgram
import Parallel.Signing
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelXmssTicket
open ParallelSigning
set_option maxHeartbeats 1000000

abbrev Layers := alloc.vec.Vec (address.Adrs × U32)

def LayerTable (hp t l n : Nat) (rows : Layers) := rows.length=n ∧
  ∀ j<n, (adrsS rows.val[j]!.1,rows.val[j]!.2.val) =
    (addr j (loc hp t l j).1,(loc hp t l j).2)

theorem layer_table (p : params.Params) (h : p.hp.val≤9) (tree : U64) (leaf : U32) :
    build_layers p tree leaf ⦃ rows => LayerTable p.hp.val tree.val leaf.val p.d.val rows ⦄ := by
  unfold build_layers build_layers_loop
  simp only [lift,bind_ok]
  let pos := loc p.hp.val tree.val leaf.val
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × U64 × U32 × Layers => p.d.val-q.1.start.val)
    (inv := fun q => q.1.end=p.d ∧ q.1.start.val≤p.d.val ∧
      (q.2.1.val,q.2.2.1.val)=pos q.1.start.val ∧ LayerTable p.hp.val tree.val leaf.val q.1.start.val q.2.2.2)
  · rintro ⟨it,t,l,rows⟩ ⟨last,bounded,current,table⟩
    simp only at last bounded current table ⊢
    unfold build_layers_loop.body
    by_cases more : it.start.val<p.d.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [last];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨a,zero⟩
      step as ⟨a1,layer⟩
      step as ⟨a2,address⟩
      have length : rows.val.length=it.start.val := table.1
      have enough : rows.val.length < Usize.max := by scalar_tac
      step with alloc.vec.Vec.push_spec rows (a2,l) enough as ⟨out,pushed⟩
      step as ⟨width,shift⟩
      have power := ht_shl_val width p.hp h shift
      have positive := Nat.two_pow_pos p.hp.val
      step as ⟨mask,maskEq⟩
      simp only [lift,bind_ok]
      step as ⟨nextTree,shr⟩
      all_goals try scalar_tac
      have oldT : t.val=(pos it.start.val).1 := congrArg Prod.fst current
      have oldL : l.val=(pos it.start.val).2 := congrArg Prod.snd current
      have nextLeaf := ht_leaf_val t mask (t &&& mask) p.hp h (by omega) rfl
      refine ⟨ends.trans last,by omega,?_,?_,by omega⟩
      · rw [inc]
        change (_,_) = ((pos it.start.val).1 >>> p.hp.val,(pos it.start.val).1 % 2^p.hp.val)
        rw [←oldT,nextLeaf,shr]
      · constructor
        · change out.val.length=_
          simp only [pushed,List.length_append,List.length_cons,List.length_nil]
          omega
        · intro j hj
          rw [pushed]
          by_cases prev : j < it.start.val
          · have inRange : j<rows.val.length := by omega
            simp only [List.getElem!_append_left _ _ _ inRange]
            exact table.2 j prev
          · have eq : j=rows.val.length := by omega
            subst j
            simp [adrsS,address,layer,zero,ParallelSigning.addr,Spec.Adrs.zero,oldT,oldL,length,pos]
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by rw [last];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=p.d.val by omega) ▸ table
  · exact ⟨rfl,by simp,rfl,rfl,by simp⟩

end slhdsa.ParallelXmssTicket
