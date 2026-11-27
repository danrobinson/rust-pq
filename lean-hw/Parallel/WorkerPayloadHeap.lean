import Parallel.WorkerWaitHeap

open Aeneas Aeneas.Std Result
namespace slhdsa.WorkerPayload
open ParallelWorkerHeap ParallelSignJoin

/-- Starting at the barrier with phase-one roots already in the shared heap,
realize *this* split-fetch history with the native ticket results. Every lookup
in the physical output vector agrees with the resulting heap, even on an
unfinished run. -/
theorem native_heap {N : Usize} (host : Host) (p : params.Params) (hp : PN p N)
    (base : Heap N) (sk seed : Array U8 N) (layers : ParallelXmssTicket.Layers)
    (roots : alloc.vec.Vec (Array U8 N)) (published : base.cells .roots=some roots)
    (layerCount : p.d.val≤layers.length) (rootCount : p.d.val≤roots.length)
    (zero : base.counts .phase2Next=0) (fresh : ∀ i, base.cells (.wotsSigs i)=none)
    {workers m log} (run : WorkerFetch.Execution (MaximalWorker.single p.d.val).jobs workers m log) :
    ∃ final : Heap N, Relation.ReflTransGen WotsAction base final ∧
      final.cells .roots=some roots ∧ final.cells .sigFors=base.cells .sigFors ∧
      final.cells .xmssAuth=base.cells .xmssAuth ∧ final.counts .phase2Next=m.counter ∧
      ∃ out, nativePhaseTwo host p sk seed layers roots log=ok out ∧ out.length=p.d.val ∧
        ∀ j<p.d.val, out.val[j]?=some (final.cells (.wotsSigs j)) ∧
          ∀ row : alloc.vec.Vec U8, final.cells (.wotsSigs j)=some row →
          bytes row.val = Spec.wotsSign (Shake.params p) (bytes roots.val[j]!.val)
            (bytes sk.val) (bytes seed.val)
            { (adrsS layers.val[j]!.1).setTypeAndClear Spec.WOTS_HASH with
              keypair := layers.val[j]!.2.val } := by
  obtain ⟨value,law,valued,out,ret,len,agree⟩ := native_run host p hp sk seed layers roots layerCount rootCount run
  refine ⟨wotsHeap base (decorate value m),wots_heap_run base valued zero fresh,published,rfl,rfl,rfl,
    out,ret,len,?_⟩
  intro j hj
  refine ⟨agree j hj,?_⟩
  intro row hit
  change (m.cells j).map (fun _ => value j) = some row at hit
  cases present : m.cells j with
  | none => simp [present] at hit
  | some u =>
    rw [present] at hit
    change some (value j) = some row at hit
    have eq : value j = row := Option.some.inj hit
    exact eq ▸ (law j hj).2

theorem all_written {n workers m log}
    (run : WorkerFetch.Execution (MaximalWorker.single n).jobs workers m log)
    (positive : 0<workers) (retired : m.threads=[]) :
    ∀ i<n, m.cells i=some () := by
  let jobs := (List.range n).map (fun j => [j])
  have reach : ParallelCached.Tickets.Reach (ParallelCached.Tickets.valued jobs (fun _ => ())) workers
      (m.view (MaximalWorker.single n).jobs) := by
    simpa [jobs,MaximalWorker.single,ParallelCached.Tickets.valued,List.map_map,Function.comp_def]
      using run.history.reachable
  have stopped : ¬ ∃ next, ParallelCached.Tickets.Step (ParallelCached.Tickets.valued jobs (fun _ => ()))
      (m.view (MaximalWorker.single n).jobs) next := by
    intro ⟨next,step⟩
    have live {s t} (h : ParallelCached.Tickets.Step (ParallelCached.Tickets.valued jobs (fun _ => ())) s t) :
        s.live≠[] := by cases h <;> simp
    exact live step (by simp [WorkerFetch.Machine.view,retired])
  have cover : jobs.flatten.Perm (List.range n) := by simp [jobs,←List.flatMap_def]
  exact ParallelCached.joined_value jobs n (fun _ => ()) cover
    (ParallelCached.Tickets.ticket_join _ reach positive cover stopped).2

/-- Once all WOTS workers retire, the post-join copy's existing Ready contract
holds for the forest, authentication path, and WOTS values in this same heap.
InputsCorrect supplies the preceding phase's native values. -/
theorem joined_native_heap {N : Usize} (host : Host) (p : params.Params) (hp : PN p N)
    (base : Heap N) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (tree : U64) (leaf : U32)
    (s : WidthEight.Ticket.PublishedInputs N) (correct : WidthEight.Ticket.InputsCorrect p md sk seed a tree leaf s)
    (forest : base.cells .sigFors=some s.forest) (auth : base.cells .xmssAuth=some s.auth)
    (roots : base.cells .roots=some s.roots) (zero : base.counts .phase2Next=0)
    (fresh : ∀ i, base.cells (.wotsSigs i)=none) {workers m log}
    (run : WorkerFetch.Execution (MaximalWorker.single p.d.val).jobs workers m log)
    (positive : 0<workers) (retired : m.threads=[]) :
    ∃ final : Heap N, Relation.ReflTransGen WotsAction base final ∧ final.cells .roots=some s.roots ∧
      final.cells .sigFors=some s.forest ∧ final.cells .xmssAuth=some s.auth ∧
      ∃ out, nativePhaseTwo host p sk seed s.layers s.roots log=ok out ∧ out.length=p.d.val ∧
        (∀ j<p.d.val, out.val[j]?=some (final.cells (.wotsSigs j))) ∧
        Ready (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) tree.val leaf.val
          s.forest s.auth out := by
  obtain ⟨forestOk,authSize,authRows,table,rootCount,messages,_,_⟩ := correct
  obtain ⟨value,law,valued,out,ret,len,agree⟩ := native_run host p hp sk seed s.layers s.roots
    table.1.ge rootCount run
  refine ⟨wotsHeap base (decorate value m),wots_heap_run base valued zero fresh,roots,forest,auth,
    out,ret,len,agree,forestOk,authSize,len.ge,authRows,?_⟩
  intro j hj
  obtain ⟨_,valEq⟩ := law j hj
  have cell := agree j hj
  simp [decorate,all_written run positive retired j hj] at cell
  have found : out.val[j]! = some (value j) := by
    simp [List.getElem!_eq_getElem?_getD,cell]
  refine ⟨value j,found,?_⟩
  have address := congrArg Prod.fst (table.2 j hj)
  have keypair := congrArg Prod.snd (table.2 j hj)
  dsimp only at address keypair
  have shape : (Shake.params p).hp = p.hp.val := by simp [Shake.params,paramsS_hp]
  simpa only [address,keypair,messages j hj,shape] using valEq

/-- Materialize the vector view consumed by the extracted post-join Rust caller.
Each vector entry is read from the invocation's heap at that same index. -/
def wotsCell (h : Heap N) (j : Nat) : Option (alloc.vec.Vec U8) := h.cells (.wotsSigs j)

def wotsView (p : params.Params) (h : Heap N) : WidthEight.Ticket.WotsCells :=
  alloc.vec.Vec.from ((List.range p.d.val).map (wotsCell h))
    (by simp only [List.length_map,List.length_range]; scalar_tac)

theorem wotsView_eq (p : params.Params) (h : Heap N) (out : WidthEight.Ticket.WotsCells)
    (len : out.length=p.d.val) (read : ∀ j<p.d.val, out.val[j]?=some (h.cells (.wotsSigs j))) :
    wotsView p h=out := by
  apply alloc.vec.Vec.ext
  apply List.ext_getElem
  · simp [wotsView,alloc.vec.Vec.from_val,←len,alloc.vec.Vec.length]
  · intro j _ hj
    have inside : j<p.d.val := hj.trans_eq len
    have found : out.val[j]?=some (wotsCell h j) := read j inside
    rw [List.getElem?_eq_getElem hj,Option.some.injEq] at found
    simpa [wotsView,alloc.vec.Vec.from_val] using found.symm

/-- Post-join external interface for a completed invocation. A call at the
wrong array size cannot see an unrelated invocation's memory. -/
def heapJoin {N : Usize} (h : Heap N) : Join :=
  fun {M} p _ _ _ _ _ _ _ _ =>
    if eq : N=M then ok (cast (congrArg Cells eq) (h.cells .sigFors,h.cells .xmssAuth,wotsView p h))
    else fail .panic

theorem wait_to_signature {N : Usize} (host : Host) (p : params.Params) (hp : PN p N)
    (base : Heap N) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (r : Array U8 N) (tree : U64) (leaf : U32) (leafLt : leaf.val<2^p.hp.val)
    (s : WidthEight.Ticket.PublishedInputs N) (correct : WidthEight.Ticket.InputsCorrect p md sk seed a tree leaf s)
    {h : Monitor N} {g decode facts pc seen} (cert : WorkerBarrierMir.Certified g decode facts)
    (exec : WorkerBarrierMir.Interleaved s.forest s.auth s.roots g decode h pc seen)
    (valid : pc<g.length) (accept : decode g[pc].ops = .accept)
    (fc : base.cells .sigFors=none) (ac : base.cells .xmssAuth=none) (rc : base.cells .roots=none)
    (zero : base.counts .phase2Next=0) (fresh : ∀ i, base.cells (.wotsSigs i)=none)
    {workers m log} (run : WorkerFetch.Execution (MaximalWorker.single p.d.val).jobs workers m log)
    (positive : 0<workers) (retired : m.threads=[]) (threads : Usize) (enabled : 2≤threads.val) :
    ∃ final : Heap N, Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
      Relation.ReflTransGen WotsAction (barrierHeap base h) final ∧
      final.cells .sigFors=some s.forest ∧ final.cells .xmssAuth=some s.auth ∧
      nativePhaseTwo host p sk seed s.layers s.roots log=ok (wotsView p final) ∧
      ∃ signature, ParallelSignJoin.run (ok threads) (heapJoin final) p md sk seed a r tree leaf = ok (some signature) ∧
        bytes signature.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
          (bytes seed.val) (adrsS a) ++ Spec.htSign (Shake.params p)
            (Spec.forsPkFromSig (Shake.params p)
              (Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))
              (bytes md.val) (bytes seed.val) (adrsS a))
            (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  have seen := WorkerBarrierMir.accepts_installed cert exec valid accept
  have barrier := barrier_run base exec.projects.1 fc ac rc
  obtain ⟨final,path,_,forest,auth,out,computed,len,read,ready⟩ := joined_native_heap host p hp
    (barrierHeap base h) md sk seed a tree leaf s correct
    (congrArg WorkerBarrier.Cells.fors seen) (congrArg WorkerBarrier.Cells.auth seen)
    (congrArg WorkerBarrier.Cells.roots seen) zero fresh run positive retired
  have viewEq := wotsView_eq p final out len read
  refine ⟨final,barrier,path,forest,auth,viewEq.symm ▸ computed,?_⟩
  have joined : Joined N (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
      tree.val leaf.val (final.cells .sigFors,final.cells .xmssAuth,wotsView p final) := by
    exact ⟨s.forest,s.auth,forest,auth,viewEq.symm ▸ ready⟩
  obtain ⟨ret,eq,output⟩ := spec_imp_exists (result_at threads (heapJoin final) p hp md sk seed a r tree leaf leafLt
    (fun _ => by simpa [heapJoin] using joined))
  cases ret with
  | none =>
    change threads < 2#usize ∨ p.hp=0#u32 at output
    have hpos := hp.valid.hp_pos
    simp only [paramsS_hp] at hpos
    rcases output with bad|bad
    · scalar_tac
    · rw [bad] at hpos; contradiction
  | some sig =>
    exact ⟨sig,eq,ParallelFused.Slots.output_fips _ (Suite.valid .shake hp) _ _ _ _ _ _ _ _ leafLt output⟩

end slhdsa.WorkerPayload
