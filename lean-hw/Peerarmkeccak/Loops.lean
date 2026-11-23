import Peerarmkeccak.Fips
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace PeerKeccak.Arm
open PeerArmRust
open slhdsa.Ksha3 (Reg Rows lane)
set_option maxHeartbeats 850000
abbrev States := Array (Array U64 25#usize) 2#usize

theorem rounds (a : Rows) (keys : Slice U64) :
    backends.aarch64_sha3.p1600_armv8_sha3_times2_loop0 ⟨keys,0⟩ a ⦃ out => ∀ j, lane out j = (keys.val.map (·.bv)).foldl round (lane a j) ⦄ := by
  unfold backends.aarch64_sha3.p1600_armv8_sha3_times2_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U64 × Rows) => keys.length-p.1.i)
    (inv := fun p => p.1.slice = keys ∧ p.1.i ≤ keys.length ∧
      ∀ j, lane p.2 j = ((keys.val.take p.1.i).map (·.bv)).foldl round (lane a j))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold backends.aarch64_sha3.p1600_armv8_sha3_times2_loop0.body
    by_cases more : it.i < keys.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some keys.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      rcases htheta : pure_theta state with ⟨d0,d1,d2,d3,d4⟩
      simp only [theta_eq,htheta,bind_ok,rho_pi_eq,chi_iota_eq,step_simps]
      have post := lanes_fips state keys.val[it.i]
      simp only [pureRound,htheta] at post
      refine ⟨slice,by change it.i+1 ≤ keys.length; omega,?_,by change keys.length-(it.i+1) < keys.length-it.i; omega⟩
      intro j
      rw [post j,prior j]
      change _ = (((keys.val.take (it.i+1)).map _).foldl _ _)
      rw [List.take_succ_eq_append_getElem more,List.map_append,List.foldl_append]
      rfl
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length] at *
      rw [doneIt]
      simp only [step_simps]
      simpa [show it.i=keys.length by omega,Slice.length] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩


theorem packed (m : States) :
    core.array.from_fn 25#usize backends.aarch64_sha3.p1600_armv8_sha3_times2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeuint64x2_t m
      ⦃ out => ∀ j : Fin 2, lane out j=slhdsa.Keccak.words m.val[j.val]! ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 25#usize _ m
    (fun i v => ∀ j : Fin 2, v j=(m.val[j.val]!.val[i]!).bv) ?_)
  · intro out h j
    apply ext25 _ _ (by simp [slhdsa.Ksha3.lane]) (by simp [slhdsa.Keccak.words])
    intro i hi
    rw [slhdsa.Keccak.words_get (n:=25#usize) m.val[j.val]! i hi,← getElem!_pos m.val[j.val]!.val i (by simpa using hi)]
    rw [slhdsa.Ksha3.lane,ofFnAt (fun k : Fin 25 => out.val[k.val]! j) i hi]
    simpa only [Array.getElem!_Nat_eq] using h i hi j
  · intro i hi
    change backends.aarch64_sha3.p1600_armv8_sha3_times2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeuint64x2_t.call_mut m i ⦃ _ ⦄
    unfold backends.aarch64_sha3.p1600_armv8_sha3_times2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeuint64x2_t.call_mut
    step as ⟨l,hl⟩
    step as ⟨v,hv⟩
    simp only [core.core_arch.arm_shared.neon.generated.vcreate_u64,bind_ok]
    step as ⟨r,hr⟩
    step as ⟨w,hw⟩
    simp only [core.core_arch.arm_shared.neon.generated.vcreate_u64,
      core.core_arch.arm_shared.neon.generated.vcombine_u64,step_simps]
    intro j
    have h0 : i.val<m.val[0]!.val.length := by simpa using hi
    have h1 : i.val<m.val[1]!.val.length := by simpa using hi
    fin_cases j <;> simp (disch := first | assumption | decide | scalar_tac) only [hv,hw,hl,hr,getElem!_pos,↓reduceIte] <;> rfl

end PeerKeccak.Arm
