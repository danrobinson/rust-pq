import Chainni.Pair
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Intel.Chain
open ChainNiRust.sha256.x86

def Shared (N : Usize) (iv : Array Reg 2#usize) (starts : Slice U32)
    (before after : Rows) (steps : Nat) :=
  after.length = 2 ∧ ∀ j < 2, bytes after.val[j]!.val =
    runBlock N.val (stateWords (packedState iv)) (bytes before.val[j]!.val)
        starts.val[j]!.val (starts.val[j]!.val+steps)

theorem shared_spec (N : Usize) (iv : Array Reg 2#usize) (starts : Slice U32)
    (stop : U32) (pair : Rows) (hn : N.val ≤ 32) (hp : pair.length = 2)
    (hs : starts.length = 2) (bound : ∀ j < 2, starts.val[j]!.val+stop.val ≤ U32.max) :
    chains_loop0_loop0 N ⟨0#u32,stop⟩ iv pair starts ⦃ r => Shared N iv starts pair r stop.val ⦄ := by
  obtain ⟨limit,eq,hl⟩ := spec_imp_exists (@UScalar.add_spec .Usize 22#usize N (by scalar_tac))
  unfold chains_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Rows => stop.val-q.1.start.val)
    (inv := fun q => q.1.end = stop ∧ q.1.start.val ≤ stop.val ∧ Shared N iv starts pair q.2 q.1.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hle,len,old⟩
    simp only at he hle len old
    unfold chains_loop0_loop0.body
    by_cases lt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec it lt as ⟨o,next,ho,hnxt,hend⟩
      simp only [ho]
      conv => lhs; equals (pairStep N limit iv starts it.start buf >>= fun r => ok (cont (next,r))) =>
        unfold pairStep setIndex putDigest
        simp only [eq,bind_tc_eq,Std.bind_assoc,bind_ok,lift]
        rfl
      step with pair_step_spec N limit iv starts it.start buf hn hl len hs
        (fun j hj => by have := bound j hj; omega) as ⟨r,hr,step⟩
      refine ⟨hend.trans he,by rw [he] at lt; omega,⟨hr,fun j hj => ?_⟩,by rw [he] at lt; omega⟩
      rw [hnxt,runBlock_succ,step j hj,old j hj]
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = stop.val := by rw [he] at lt; omega
      exact ⟨len,eq ▸ old⟩
  · simp [Shared,hp,runBlock]

end slhdsa.Intel.Chain
