import Spec.Correctness
import Parallel.Signing

namespace ParallelFused
open Spec ParallelSigning

private theorem inRange (k jobs : Nat) :
    (List.range k).filter (· < jobs) = List.range (min k jobs) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases lt : k < jobs
    · simp [lt, Nat.min_eq_left (Nat.le_of_lt lt), Nat.min_eq_left lt, List.range_succ]
    · simp [lt, Nat.min_eq_right (by omega : jobs ≤ k),
        Nat.min_eq_right (by omega : jobs ≤ k+1)]

/-- On the last successful completion increment every ticket's prior slot
writes have been published, even if a worker has not yet observed an empty queue. -/
theorem phase_one_ready {jobs k pending done} (t : Trace jobs k pending done)
    (last : done.length = jobs) : pending = [] ∧ done.Perm (List.range jobs) := by
  have ledger := t.ledger
  rw [inRange] at ledger
  have size := ledger.length_eq
  simp only [List.length_append, List.length_range, last] at size
  have empty : pending.length = 0 := by omega
  have hk : jobs ≤ k := by omega
  have hp := List.length_eq_zero_iff.mp empty
  exact ⟨hp, by simpa [hp, Nat.min_eq_right hk] using ledger⟩

/-- Phase two can obtain each WOTS input from the previous tree independently
of the messages signed in all lower layers. -/
def message (p : Params) (first sk pk : Bytes) (t l : Nat) : Nat → Bytes
  | 0 => first
  | j+1 => xmssNode p sk 0 p.hp pk (addr j (loc p.hp t l j).1)

def layer (p : Params) (first sk pk : Bytes) (t l j : Nat) :=
  let pos := loc p.hp t l j
  xmssSign p (message p first sk pk t l j) sk pos.2 pk (addr j pos.1)

theorem hypertree (p : Params) (valid : p.Valid) (first sk pk : Bytes) (t l : Nat)
    (bounded : l < 2^p.hp) :
    (List.range p.d).flatMap (layer p first sk pk t l) = htSign p first sk pk t l := by
  let state := fun n => (List.range n).foldl (htLayer p sk pk) ([],first,t,l)
  have inv (n : Nat) : state n =
      ((List.range n).flatMap (layer p first sk pk t l), message p first sk pk t l n,
        loc p.hp t l n) ∧ (loc p.hp t l n).2 < 2^p.hp := by
    induction n with
    | zero => exact ⟨rfl,bounded⟩
    | succ n ih =>
      have next : state (n+1) = htLayer p sk pk (state n) n := by simp [state,List.range_succ]
      rw [next, ih.1]
      dsimp only [htLayer]
      rw [xmss_correct _ valid _ _ _ _ _ ih.2]
      constructor
      · simp [List.range_succ,layer,message,loc,addr]
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  exact (congrArg Prod.fst (inv p.d).1).symm

def assemble (p : Params) (first sk pk : Bytes) (t l : Nat) (done : List Nat) : Bytes :=
    let pos := loc p.hp t l
    let sig := fun j => wotsSign p (message p first sk pk t l j) sk pk
      { (addr j (pos j).1).setTypeAndClear WOTS_HASH with keypair := (pos j).2 }
    let slots := fill sig done
    (List.range p.d).flatMap (fun j => (slots j).getD [] ++
      (List.range p.hp).flatMap (fun h =>
        xmssNode p sk (((pos j).2 / 2^h) ^^^ 1) h pk (addr j (pos j).1)))

/-- Both the WOTS bytes and the authentication nodes are emitted in layer
order even if the WOTS computations publish their results out of order. -/
theorem joined (p : Params) (valid : p.Valid) (first sk pk : Bytes) (t l k : Nat)
    (bounded : l < 2^p.hp) (done : List Nat) (trace : Trace p.d k [] done)
    (drained : p.d < k) :
    assemble p first sk pk t l done =
      htSign p first sk pk t l := by
  unfold assemble
  rw [← hypertree p valid first sk pk t l bounded]
  apply List.flatMap_congr
  intro j hj
  have covered := ((trace.joined drained).exactly_once.2 j).mpr (List.mem_range.mp hj)
  simp [fill_lookup, covered, layer, xmssSign]

def signInternal (p : Params) (m sk randomness : Bytes) (done : List Nat) : Bytes :=
  let secret := block p sk 0
  let pk := block p sk 2
  let r := PRFmsg p (block p sk 1) randomness m
  let digest := Hmsg p r pk (block p sk 3) m
  let md := digest.take p.mdBytes
  let t := digestTree p digest
  let l := digestLeaf p digest
  let a := {{Adrs.zero with tree := t}.setTypeAndClear FORS_TREE with keypair := l}
  let fors := forsSign p md secret pk a
  let first := forsPkFromSig p fors md pk a
  r ++ fors ++ assemble p first secret pk t l done

theorem sign_fips (p : Params) (valid : p.Valid) (m sk randomness : Bytes) {k done}
    (trace : Trace p.d k [] done) (drained : p.d < k) :
    signInternal p m sk randomness done = slhSignInternal p m sk randomness := by
  unfold signInternal slhSignInternal
  dsimp only
  rw [joined _ valid _ _ _ _ _ _ (digestLeaf_lt p valid _) _ trace drained]

theorem context_sign_fips (p : Params) (valid : p.Valid) (m ctx sk randomness : Bytes) {k done}
    (trace : Trace p.d k [] done) (drained : p.d < k) :
    (if ctx.length > 255 then none else some (signInternal p (withContext m ctx) sk randomness done))
      = slhSign p m ctx sk randomness := by
  simp only [slhSign, sign_fips _ valid _ _ _ trace drained]

end ParallelFused
