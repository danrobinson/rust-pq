import Kgridbulk.Funs
import Kdiag.Theta
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86
set_option maxHeartbeats 800000

theorem putRow (s : Array U64 25#usize) (y : Usize) (hy : y.val < 5)
    (row : KgridbulkRust.core.core_arch.x86.__m512i) :
    write_row s y row ⦃ t => ∀ i : Fin 25, t.val[i.val]!.bv =
      if i.val / 5 = y.val then row ⟨i.val % 5,by omega⟩ else s.val[i.val]!.bv ⦄ := by
  simp only [write_row,hy,if_true,step_simps]
  intro i
  rw [Array.make_val]
  rw [getElem!_pos _ i.val (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
  split <;> rfl

theorem restore (s : Array U64 25#usize) (a : Kdiag.Grid) :
    absorb_loop1 ⟨0#usize,5#usize⟩ s a ⦃ out => ∀ i : Fin 25,
      out.val[i.val]!.bv = a.val[i.val/5]! ⟨i.val%5,by omega⟩ ⦄ := by
  unfold absorb_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 25#usize) => 5-p.1.start.val)
    (inv := fun p => p.1.end = 5#usize ∧ p.1.start.val ≤ 5 ∧
      ∀ i : Fin 25, i.val/5 < p.1.start.val →
        p.2.val[i.val]!.bv = a.val[i.val/5]! ⟨i.val%5,by omega⟩)
  · rintro ⟨it,st⟩ ⟨he,hb,prior⟩
    simp only at *
    unfold absorb_loop1.body
    by_cases more : it.start.val < 5
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok]
      step as ⟨row,hr⟩
      step with putRow st it.start more row as ⟨out,hout⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro i hi
      rw [hout i]
      split
      · rename_i same
        rw [same,getElem!_pos a.val it.start.val (by simpa using more),hr]
      · exact prior i (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro i
      exact prior i (by have := i.isLt; omega)
  · exact ⟨rfl,Nat.zero_le _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
#print axioms restore
end slhdsa.Kgridbulk
