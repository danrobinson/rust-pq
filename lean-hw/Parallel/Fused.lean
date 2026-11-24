import Spec.Correctness
import Parallel.Signing

namespace ParallelFused
open Spec ParallelSigning

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

/-- Both the WOTS bytes and the authentication nodes are emitted in layer
order even if the WOTS computations publish their results out of order. -/
theorem joined (p : Params) (valid : p.Valid) (first sk pk : Bytes) (t l k : Nat)
    (bounded : l < 2^p.hp) (done : List Nat) (trace : Trace p.d k [] done)
    (drained : p.d < k) :
    let pos := loc p.hp t l
    let sig := fun j => wotsSign p (message p first sk pk t l j) sk pk
      { (addr j (pos j).1).setTypeAndClear WOTS_HASH with keypair := (pos j).2 }
    let slots := fill sig done
    (List.range p.d).flatMap (fun j => (slots j).getD [] ++
      (List.range p.hp).flatMap (fun h =>
        xmssNode p sk (((pos j).2 / 2^h) ^^^ 1) h pk (addr j (pos j).1))) =
      htSign p first sk pk t l := by
  rw [← hypertree p valid first sk pk t l bounded]
  apply List.flatMap_congr
  intro j hj
  have covered := ((trace.joined drained).exactly_once.2 j).mpr (List.mem_range.mp hj)
  simp [fill_lookup, covered, layer, xmssSign]

end ParallelFused
