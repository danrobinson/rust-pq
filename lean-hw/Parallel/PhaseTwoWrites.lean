import Parallel.WidthEightTicket
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket
open ParallelSigning ShakeBatch

/-- Linearized successful OnceLock writes, newest publication first.
The counter trace supplies ownership and the normal scope join. -/
def writeRows {α : Type} (count : Nat) (compute : Nat → Result α) : List Nat → Result (List (Option α))
  | [] => ok (List.replicate count none)
  | j::done => do
    let prior ← writeRows count compute done
    match prior[j]? with
    | some none => do let row ← compute j; ok (prior.set j (some row))
    | _ => fail .panic

private theorem writes {α : Type} (count : Nat) (compute : Nat → Result α) (post : Nat → α → Prop)
    (total : ∀ j<count, ∃ row, compute j=ok row ∧ post j row) (done : List Nat)
    (unique : done.Nodup) (inside : ∀ i∈done, i<count) :
    ∃ rows, writeRows count compute done=ok rows ∧ rows.length=count ∧
      ∀ j<count, (if j∈done then ∃ row, rows[j]?=some (some row) ∧ post j row else rows[j]?=some none) := by
  induction done with
  | nil =>
    refine ⟨_,rfl,by simp,?_⟩
    intro j hj
    simp [hj]
  | cons j done ih =>
    obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp unique
    have room := inside j (by simp)
    obtain ⟨rows,run,len,cells⟩ := ih distinct (fun i hi => inside i (by simp [hi]))
    have empty := cells j room
    simp only [fresh,ite_false] at empty
    obtain ⟨row,computeRow,okRow⟩ := total j room
    refine ⟨rows.set j (some row),by simp [writeRows,run,empty,computeRow],by simp [len],?_⟩
    intro i hi
    by_cases same : i=j
    · subst i
      simp only [List.mem_cons_self,ite_true]
      exact ⟨row,by simp [show j<rows.length by omega],okRow⟩
    · simpa [List.mem_cons,same,List.getElem?_set_ne (Ne.symm same)] using cells i hi

abbrev WotsCells := alloc.vec.Vec (Option (alloc.vec.Vec U8))

noncomputable def phaseTwo (host : Platform) {N : Usize} (p : params.Params) (sk seed : Array U8 N)
    (layers : ParallelXmssTicket.Layers) (roots : alloc.vec.Vec (Array U8 N)) (completed : List Nat) :
    Result WotsCells := do
  let rows ← writeRows p.d.val (fun j =>
    if h : j < 2^UScalarTy.Usize.numBits then ticket host p layers roots (Usize.ofNatCore j h) sk seed else fail .panic) completed
  if h : rows.length≤Usize.max then ok (alloc.vec.Vec.from rows h) else fail .panic

theorem phase_two {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (tree leaf : Nat) (first : Spec.Bytes) (layers : ParallelXmssTicket.Layers)
    (roots : alloc.vec.Vec (Array U8 N)) (table : ParallelXmssTicket.LayerTable p.hp.val tree leaf p.d.val layers)
    (rootCount : p.d.val≤roots.length)
    (messages : ∀ j<p.d.val, bytes roots.val[j]!.val=ParallelFused.message (Shake.params p) first
      (bytes sk.val) (bytes seed.val) tree leaf j)
    {issued : Nat} {completed : List Nat} (trace : Trace p.d.val issued [] completed) (drained : p.d.val < issued) :
    phaseTwo host p sk seed layers roots completed ⦃ out => out.length=p.d.val ∧ ∀ j<p.d.val,
      ∃ row, out.val[j]! = some row ∧ bytes row.val=Spec.wotsSign (Shake.params p)
        (ParallelFused.message (Shake.params p) first (bytes sk.val) (bytes seed.val) tree leaf j)
        (bytes sk.val) (bytes seed.val) { (addr j (loc p.hp.val tree leaf j).1).setTypeAndClear Spec.WOTS_HASH with
          keypair := (loc p.hp.val tree leaf j).2 } ⦄ := by
  let value := fun j => Spec.wotsSign (Shake.params p)
    (ParallelFused.message (Shake.params p) first (bytes sk.val) (bytes seed.val) tree leaf j)
    (bytes sk.val) (bytes seed.val) { (addr j (loc p.hp.val tree leaf j).1).setTypeAndClear Spec.WOTS_HASH with
      keypair := (loc p.hp.val tree leaf j).2 }
  let compute := fun j => if h : j < 2^UScalarTy.Usize.numBits then ticket host p layers roots (Usize.ofNatCore j h) sk seed else fail .panic
  have count : p.d.val≤Usize.max := by scalar_tac
  have law (j : Nat) (hj : j<p.d.val) : ∃ row, compute j=ok row ∧ bytes row.val=value j := by
    have small : j < 2^UScalarTy.Usize.numBits := by scalar_tac
    let i := Usize.ofNatCore j small
    have iv : i.val=j := by simp [i]
    obtain ⟨row,run,data⟩ := spec_imp_exists (ticket_spec host p hp layers roots i sk seed
      (by rw [iv,table.1];exact hj) (by omega))
    refine ⟨row,by simpa only [compute,dite_eq_left small,i] using run,?_⟩
    have address := congrArg Prod.fst (table.2 j hj)
    have keypair := congrArg Prod.snd (table.2 j hj)
    dsimp only at address keypair
    simpa only [value,iv,address,keypair,messages j hj] using data
  obtain ⟨nodup,covers⟩ := (trace.joined drained).exactly_once
  obtain ⟨rows,run,len,cells⟩ := writes _ compute (fun j row => bytes row.val=value j) law completed nodup
    (fun i hi => (covers i).mp hi)
  unfold phaseTwo
  rw [show writeRows p.d.val _ completed=ok rows from run]
  simp only [bind_ok,dite_eq_left (len ▸ count),WP.spec_ok]
  refine ⟨by simpa [alloc.vec.Vec.length,alloc.vec.Vec.from_val] using len,?_⟩
  intro j hj
  obtain ⟨row,read,expected⟩ := (ite_eq_left ((covers j).mpr hj)) ▸ cells j hj
  refine ⟨row,?_,expected⟩
  rw [alloc.vec.Vec.from_val]
  simp [List.getElem!_eq_getElem?_getD,read]

end slhdsa.WidthEight.Ticket
