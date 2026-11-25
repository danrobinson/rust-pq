import Parallel.WidthEightTicketProgram
import Parallel.TicketLayers
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket

theorem wots (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (m sk seed : Array U8 N)
    (a : address.Adrs) (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    @Fused.Outer.shake.wots.wots_sign (host.outer p) N m sk seed a ⦃ out =>
      bytes out.val=Spec.wotsSign (Shake.params p) (bytes m.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧
      out.length=N.val*(2*N.val+3) ⦄ := by
  cases on : host.available N with
  | false =>
    rw [@Fused.Outer.off_wots (host.outer p) N (by exact (probe_eq host N).trans (by rw [on]))]
    exact Shake.wots_sign_spec p hp m sk seed a
  | true =>
    simp only [Fused.Outer.shake.wots.wots_sign,Fused.Outer.shake.batch.available,
      show (host.outer p).available N=ok true from (probe_eq host N).trans (by rw [on]),bind_ok,ite_true]
    cases host with
    | apple sha3 =>
      exact @NativeShakeWots.sign_spec (AppleHybrid.machine sha3) ⟨NativeVerify.appleActive sha3⟩
        N p hp m sk seed a domain (by change 0<8;decide) (NativeVerify.apple sha3)
    | x86 =>
      exact @NativeShakeWots.sign_spec Kxdispatch.machine ⟨NativeVerify.fullActive _ KxdispatchRust.shake256.parallel.available⟩
        N p hp m sk seed a domain (by decide) (NativeVerify.x86 (Bool.and_eq_true_iff.mp on).2)

theorem ticket_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (roots : alloc.vec.Vec (Array U8 N))
    (j : Usize) (sk seed : Array U8 N) (hasLayer : j.val<layers.length) (hasRoot : j.val<roots.length) :
    ticket host p layers roots j sk seed ⦃ sig => bytes sig.val = Spec.wotsSign (Shake.params p) (bytes roots.val[j.val]!.val)
      (bytes sk.val) (bytes seed.val) { (adrsS layers.val[j.val]!.1).setTypeAndClear Spec.WOTS_HASH with keypair := layers.val[j.val]!.2.val } ⦄ := by
  unfold ticket
  step as ⟨addr,idx,read⟩
  step as ⟨root,rootEq⟩
  step as ⟨tag,_,tagEq⟩
  step as ⟨a,aEq⟩
  step with wots host p hp root sk seed a (by simp [aEq,tagEq]) as ⟨sig,cert,_⟩
  rw [cert,rootEq,←getElem!_pos]
  rw [←getElem!_pos] at read
  simp [←read,aEq,tagEq,adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_HASH,address.WOTS_HASH]

theorem published (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (md : Spec.Bytes)
    (sk seed : Array U8 N) (a : Spec.Adrs) (tree leaf : Nat)
    (forest : alloc.vec.Vec U8) (auth : alloc.vec.Vec (Array U8 N)) (cells : alloc.vec.Vec (Option (alloc.vec.Vec U8)))
    (ready : ParallelSignJoin.Ready (Shake.params p) md (bytes sk.val) (bytes seed.val) a tree leaf forest auth cells)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (roots : alloc.vec.Vec (Array U8 N))
    (j : Usize) (inside : j.val<(Shake.params p).d) (hasLayer : j.val<layers.length) (hasRoot : j.val<roots.length)
    (addr : adrsS layers.val[j.val]!.1 = ParallelSigning.addr j.val (ParallelSigning.loc (Shake.params p).hp tree leaf j.val).1)
    (index : layers.val[j.val]!.2.val = (ParallelSigning.loc (Shake.params p).hp tree leaf j.val).2)
    (root : bytes roots.val[j.val]!.val = ParallelFused.message (Shake.params p)
      (Spec.forsPkFromSig (Shake.params p) (bytes forest.val) md (bytes seed.val) a)
      (bytes sk.val) (bytes seed.val) tree leaf j.val) :
    ∃ sig, ticket host p layers roots j sk seed = ok sig ∧ cells.val[j.val]! = some sig := by
  obtain ⟨sig,run,sigEq⟩ := spec_imp_exists (ticket_spec host p hp layers roots j sk seed hasLayer hasRoot)
  obtain ⟨row,getRow,rowEq⟩ := ready.wotsRow j.val inside
  rw [addr,index,root] at sigEq
  have agree : row=sig := alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (rowEq.trans sigEq.symm))
  exact ⟨sig,run,agree ▸ getRow⟩

theorem from_layers (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (tree : U64) (leaf : U32)
    (roots : alloc.vec.Vec (Array U8 N)) (j : Usize) (sk seed : Array U8 N)
    (inside : j.val<p.d.val) (root : j.val<roots.length) :
    (do let layers ← ParallelXmssTicket.build_layers p tree leaf
        ticket host p layers roots j sk seed) ⦃ r =>
        bytes r.val=Spec.wotsSign (Shake.params p) (bytes roots.val[j.val]!.val) (bytes sk.val)
          (bytes seed.val) { (ParallelSigning.addr j.val (ParallelSigning.loc p.hp.val tree.val leaf.val j.val).1).setTypeAndClear Spec.WOTS_HASH with
            keypair := (ParallelSigning.loc p.hp.val tree.val leaf.val j.val).2 } ⦄ := by
  step with ParallelXmssTicket.layer_table p hp.valid.hp_le tree leaf as ⟨rows,table⟩
  obtain ⟨length,cells⟩ := table
  have addrEq := congrArg Prod.fst (cells _ inside)
  have idxEq := congrArg Prod.snd (cells _ inside)
  dsimp only at addrEq idxEq
  step with ticket_spec host p hp rows roots j sk seed (length.symm ▸ inside) root as ⟨r,value⟩
  rw [value,addrEq,idxEq]

end slhdsa.WidthEight.Ticket
