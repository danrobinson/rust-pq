import Peerarmkeccak.Loops
import Shakebatch.Seed
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace PeerKeccak.Arm
open PeerArmRust
open slhdsa.Ksha3 (Reg Rows lane)
set_option maxHeartbeats 600000

private theorem set_at {T : Type} [Inhabited T] {N : Usize} (a : Array T N) (idx : Usize)
    (v : T) (i : Nat) (h : idx.val < N.val) :
    (a.set idx v).val[i]! = if idx.val=i then v else a.val[i]! := by
  rw [Array.set_val_eq]
  by_cases eq : idx.val=i
  · subst i; simp only [ite_true]; exact slhdsa.ShakeBatch.setSame _ _ _ (by simpa using h)
  · simp only [eq,ite_false];exact slhdsa.ShakeBatch.setOther _ _ _ _ eq

theorem unpacked (m : States) (s : Rows) :
    backends.aarch64_sha3.p1600_armv8_sha3_times2_loop1 ⟨0#usize,25#usize⟩ m s
      ⦃ out => ∀ j : Fin 2, slhdsa.Keccak.words out.val[j.val]! = lane s j ⦄ := by
  unfold backends.aarch64_sha3.p1600_armv8_sha3_times2_loop1
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × States => 25-q.1.start.val)
    (inv := fun q => q.1.end=25#usize ∧ q.1.start.val≤25 ∧ ∀ j : Fin 2, ∀ k < q.1.start.val,
      q.2.val[j.val]!.val[k]!.bv=s.val[k]! j)
  · rintro ⟨it,a⟩ ⟨he,le,old⟩
    simp only at he le old
    unfold backends.aarch64_sha3.p1600_armv8_sha3_times2_loop1.body
    by_cases live : it.start.val < it.end.val
    · have z : (0#usize).val=0 := rfl
      have one : (1#usize).val=1 := rfl
      have valid : it.start.val<25 := by simpa [he] using live
      step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨o,nxt,ho,hn,hend⟩
      simp only [ho,core.core_arch.arm_shared.neon.generated.vgetq_lane_u64,step_simps]
      step as ⟨v,get⟩
      simp (disch := decide) only [core.core_arch.arm_shared.neon.generated.vgetq_lane_u64,dif_pos,bind_ok]
      step as ⟨l,back,hl,repl⟩
      step as ⟨l1,upd⟩
      step as ⟨r,back2,hr,repl2⟩
      step as ⟨r1,upd2⟩
      refine ⟨hend.trans he,by omega,?_,by omega⟩
      intro j k hk
      rw [repl2,upd2,hr,← getElem!_pos,repl,upd,hl,← getElem!_pos,get,← getElem!_pos]
      have inside (r : Array U64 25#usize) (v : U64) (i : Nat) := set_at r it.start v i (show it.start.val < (25#usize).val from valid)
      by_cases here : it.start.val=k
      · subst k
        fin_cases j <;> simp (disch := first | decide | assumption) only [inside,set_at,z,one,Nat.zero_ne_one,Nat.one_ne_zero,ite_true,ite_false,reduceCtorEq] <;> rfl
      · have prev := old j k (by omega)
        fin_cases j <;> simp (disch := first | decide | assumption) only [inside,set_at,here,z,one,Nat.zero_ne_one,Nat.one_ne_zero,ite_true,ite_false,reduceCtorEq] <;> exact prev
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,nxt,ho,hn⟩
      simp only [ho,step_simps]
      intro j
      apply ext25 _ _ (by simp [slhdsa.Keccak.words]) (by simp [slhdsa.Ksha3.lane])
      intro k hk
      rw [slhdsa.Keccak.words_get (n:=25#usize) a.val[j.val]! k hk,← getElem!_pos]
      rw [slhdsa.Ksha3.lane,ofFnAt (fun i : Fin 25 => s.val[i.val]! j) k hk]
      apply old j k
      have he' : it.end.val=25 := by simp [he]
      omega
  · exact ⟨rfl,by change 0 ≤ 25; decide,fun _ _ h => by simp at h⟩
end PeerKeccak.Arm
