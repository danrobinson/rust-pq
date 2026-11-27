import Parallel.WorkerPrepared
import Parallel.WorkerWotsFrame

open Aeneas Aeneas.Std Result
namespace slhdsa.WorkerPayload
open ParallelWorkerHeap ParallelSignJoin

/-- At a concrete normal return, read each WOTS cell from this final invocation
heap; the native ticket returned the identical vector for that layer. -/
theorem actual_return {N : Usize} (host : Host) (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N)
    (tree : U64) (leaf : U32) (leafLt : leaf.val<2^p.hp.val)
    (threads : Usize) (enabled : 2≤threads.val) (s : WidthEight.Ticket.PublishedInputs N)
    (correct : WidthEight.Ticket.InputsCorrect p md sk seed a tree leaf s)
    (final : Heap N) (forest : final.cells .sigFors=some s.forest) (auth : final.cells .xmssAuth=some s.auth)
    (physical : ∀ j : Usize, j.val<p.d.val → ∃ row : alloc.vec.Vec U8,
      final.cells (.wotsSigs j.val)=some row ∧ nativeTicket host p s.layers s.roots j sk seed=ok row) :
    ∃ signature, ParallelSignJoin.run (ok threads) (heapJoin final) p md sk seed a r tree leaf=ok (some signature) ∧
      bytes signature.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
        (bytes seed.val) (adrsS a) ++ Spec.htSign (Shake.params p)
          (Spec.forsPkFromSig (Shake.params p)
            (Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))
            (bytes md.val) (bytes seed.val) (adrsS a)) (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  obtain ⟨forestOk,authSize,authRows,table,rootCount,messages,_,_⟩ := correct
  have count : (wotsView p final).length=p.d.val := by simp [wotsView,alloc.vec.Vec.length,alloc.vec.Vec.from_val]
  have ready : Ready (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
      tree.val leaf.val s.forest s.auth (wotsView p final) := by
    refine ⟨forestOk,authSize,count.ge,authRows,?_⟩
    intro j hj
    change j<p.d.val at hj
    have small : j<2^UScalarTy.Usize.numBits := by scalar_tac
    let i := Usize.ofNatCore j small
    obtain ⟨row,read,ran⟩ := physical i hj
    obtain ⟨v,computed,data⟩ := compute_succeeds host p hp sk seed s.layers s.roots j hj
      (lt_of_lt_of_le hj table.1.ge) (lt_of_lt_of_le hj rootCount)
    rw [show compute host p sk seed s.layers s.roots j = ok row from by
      simpa only [compute,dite_eq_left small,i] using ran] at computed
    have same := Result.ok_injective computed
    change final.cells (.wotsSigs j) = some row at read
    refine ⟨row,?_,?_⟩
    · have inside : j<p.d.val := hj
      simp only [wotsView,alloc.vec.Vec.from_val]
      rw [getElem!_pos _ _ (by simpa using inside),List.getElem_map,List.getElem_range]
      exact read
    · have address := congrArg Prod.fst (table.2 j hj)
      have keypair := congrArg Prod.snd (table.2 j hj)
      dsimp only at address keypair
      have shape : (Shake.params p).hp=p.hp.val := by simp [Shake.params,paramsS_hp]
      simpa only [same,address,keypair,messages j hj,shape] using data
  have joined : Joined N (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
      tree.val leaf.val (final.cells .sigFors,final.cells .xmssAuth,wotsView p final) :=
    ⟨s.forest,s.auth,forest,auth,ready⟩
  obtain ⟨ret,eq,out⟩ := spec_imp_exists (result_at threads (heapJoin final) p hp md sk seed a r tree leaf leafLt
    (fun _ => by simpa [heapJoin] using joined))
  cases ret with
  | none =>
    change threads < 2#usize ∨ p.hp=0#u32 at out
    have h := hp.valid.hp_pos
    simp only [paramsS_hp] at h
    rcases out with bad|bad
    · scalar_tac
    · rw [bad] at h; contradiction
  | some sig => exact ⟨sig,eq,ParallelFused.Slots.output_fips _ (Suite.valid .shake hp) _ _ _ _ _ _ _ _ leafLt out⟩

end slhdsa.WorkerPayload
