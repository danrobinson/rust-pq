import Kdiag.Theta
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
open KdiagRust.core.core_arch.x86.avx512f

def chi (a b c : BitVec 64) := a ^^^ ((~~~b) &&& c)
private theorem chi_inst (a b c : Reg) :
    _mm512_ternarylogic_epi64 210#i32 a b c = ok (fun j => chi (a j) (b j) (c j)) := by
  unfold _mm512_ternarylogic_epi64 KavxRust.core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
  congr 1
  funext j
  exact KeccakAsm.chiInstruction _ _ _

theorem across (b : Grid) : core.array.from_fn 5#usize even.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i b
    ⦃ out => ∀ (i : Nat), i<5 → ∀ j, out.val[i]! j = chi (b.val[i]! j) (b.val[(i+1)%5]! j) (b.val[(i+2)%5]! j) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 5#usize _ _
    (fun i (w : Reg) => ∀ j, w j = chi (b.val[i]! j) (b.val[(i+1)%5]! j) (b.val[(i+2)%5]! j)) ?_)
  · intro out h i hi j
    simpa only [Array.getElem!_Nat_eq] using h i hi j
  intro i hi
  unfold even.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i
  simp only [even.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut]
  step as ⟨v,hv⟩
  step as ⟨n,hn⟩
  step as ⟨n',hn'⟩
  step as ⟨v1,h1⟩
  step as ⟨m,hm⟩
  step as ⟨m',hm'⟩
  step as ⟨v2,h2⟩
  simp [chi_inst,hv,h1,h2,hn',hn,hm',hm,getElem!_pos,getElem?_pos b.val i.val (by simpa using hi),hi,Nat.mod_lt _ (by decide : 0<5)]

theorem within (b : Grid) : core.array.Array.map odd.closure.Insts.CoreOpsFunctionFnMutTuple__m512i__m512i b ()
    ⦃ out => ∀ (i : Nat), i<5 → ∀ j, out.val[i]! j = chi (b.val[i]! j) (b.val[i]! (col 1 1 j.val)) (b.val[i]! (col 2 1 j.val)) ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 5#usize _ _
    (fun i (w : Reg) => ∀ j, w j = chi (b.val[i]! j) (b.val[i]! (col 1 1 j.val)) (b.val[i]! (col 2 1 j.val))) ?_)
  · intro out h i hi j
    simpa only [Array.getElem!_Nat_eq] using h i hi j
  intro i hi
  simp only [odd.closure.Insts.CoreOpsFunctionFnMutTuple__m512i__m512i,
    odd.closure.Insts.CoreOpsFunctionFnMutTuple__m512i__m512i.call_mut]
  step as ⟨v,hv⟩
  step with move_spec 1#usize 1#usize (by decide) (by decide) v as ⟨v1,h1⟩
  step with move_spec 2#usize 1#usize (by decide) (by decide) v as ⟨v2,h2⟩
  simp [chi_inst,hv,h1,h2,getElem!_pos,getElem?_pos b.val i.val (by simpa using hi),hi]

end slhdsa.Kdiag
