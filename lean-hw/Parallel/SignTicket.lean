import Parallel.SignTicketProgram
import Parallel.SignJoinValues
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignTicket

theorem ticket_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (roots : alloc.vec.Vec (Array U8 N))
    (j : Usize) (sk seed : Array U8 N) (hasLayer : j.val<layers.length) (hasRoot : j.val<roots.length) :
    ticket layers roots j sk seed ⦃ sig =>
      bytes sig.val = Spec.wotsSign (Shake.params p) (bytes roots.val[j.val]!.val)
        (bytes sk.val) (bytes seed.val)
        { (adrsS layers.val[j.val]!.1).setTypeAndClear Spec.WOTS_HASH with keypair := layers.val[j.val]!.2.val } ⦄ := by
  unfold ticket
  step as ⟨addr,idx,read⟩
  step as ⟨root,rootEq⟩
  step as ⟨tag,_,tagEq⟩
  step as ⟨a,aEq⟩
  simp only [WidthThree.shake.wots.wots_sign,WidthThree.shake.batch.available,
    ShakeBatch.available_for_fips _ p hp,KldispRust.shake256.parallel.available,bind_ok,ite_true]
  have domain : WidthThree.Domain a := by simp [WidthThree.Domain,aEq,tagEq]
  obtain ⟨sig,eq,signature,_⟩ := spec_imp_exists (WidthThree.linuxSigning.wots.laws.sign p hp root sk seed a domain)
  rw [show (do let digits ← wots.wots_digits root; @WidthThree.shake.batch.sign WidthThree.linuxWots N sk seed a digits.deref) = ok sig from eq]
  simp only [step_simps]
  rw [signature,rootEq,←getElem!_pos]
  rw [←getElem!_pos] at read
  simp [←read,aEq,tagEq,adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_HASH,address.WOTS_HASH]

/-- The actual Linux Arm computation for a successful phase-two ticket returns the
same complete Rust vector observed in the corresponding post-join cell. -/
theorem published_row {N : Usize} (p : params.Params) (hp : PN p N) (md : Spec.Bytes)
    (sk seed : Array U8 N) (a : Spec.Adrs) (tree leaf : Nat)
    (forest : alloc.vec.Vec U8) (auth : alloc.vec.Vec (Array U8 N))
    (cells : alloc.vec.Vec (Option (alloc.vec.Vec U8)))
    (ready : ParallelSignJoin.Ready (Shake.params p) md (bytes sk.val) (bytes seed.val) a tree leaf forest auth cells)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (roots : alloc.vec.Vec (Array U8 N))
    (j : Usize) (inside : j.val<(Shake.params p).d) (hasLayer : j.val<layers.length) (hasRoot : j.val<roots.length)
    (addr : adrsS layers.val[j.val]!.1 = ParallelSigning.addr j.val (ParallelSigning.loc (Shake.params p).hp tree leaf j.val).1)
    (index : layers.val[j.val]!.2.val = (ParallelSigning.loc (Shake.params p).hp tree leaf j.val).2)
    (root : bytes roots.val[j.val]!.val = ParallelFused.message (Shake.params p)
      (Spec.forsPkFromSig (Shake.params p) (bytes forest.val) md (bytes seed.val) a)
      (bytes sk.val) (bytes seed.val) tree leaf j.val) :
    ∃ sig, ticket layers roots j sk seed = ok sig ∧ cells.val[j.val]! = some sig := by
  obtain ⟨sig,run,sigEq⟩ := spec_imp_exists (ticket_spec p hp layers roots j sk seed hasLayer hasRoot)
  obtain ⟨row,getRow,rowEq⟩ := ready.wotsRow j.val inside
  rw [addr,index,root] at sigEq
  have agree : row=sig := alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (rowEq.trans sigEq.symm))
  exact ⟨sig,run,agree ▸ getRow⟩

end slhdsa.ParallelSignTicket
