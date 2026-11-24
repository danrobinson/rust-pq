import Ct.Funs
import Ct.Tactic

/-! Equal branch and memory-access traces for arbitrary Keccak-f[1600] inputs. -/

open Aeneas Aeneas.Std Ct slhdsa_leak

namespace Ct.Shake

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Lockstep for the unrolled fixed-index loads and register operations. -/
macro "fixed_lanes" : tactic => `(tactic|
  repeat' first
    | (with_reducible refine Rel.bind_prim rfl (fun _ _ _ _ => ?_))
    | (with_reducible refine Rel.bind_pure ?_)
    | (with_reducible exact Rel.pure trivial))

@[ct_rel] theorem chi (a b : Array U64 25#usize) :
    Rel (shake256.chi a) (shake256.chi b) (fun _ _ => True) := by
  unfold shake256.chi
  fixed_lanes

@[ct_rel] theorem rho_pi (a b : Array U64 25#usize) (d d' : Array U64 5#usize) :
    Rel (shake256.rho_pi a d) (shake256.rho_pi b d') (fun _ _ => True) := by
  unfold shake256.rho_pi
  fixed_lanes

@[ct_rel] theorem parity (a b : Array U64 25#usize) (c d : Array U64 5#usize) (x : Usize) :
    Rel (shake256.round_loop0 a c x) (shake256.round_loop0 b d x) (fun _ _ => True) := by
  unfold shake256.round_loop0
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨v,i⟩ ⟨w,j⟩ (rfl : i = j)
  unfold shake256.round_loop0.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem theta (a b c d : Array U64 5#usize) (x : Usize) :
    Rel (shake256.round_loop1 a c x) (shake256.round_loop1 b d x) (fun _ _ => True) := by
  unfold shake256.round_loop1
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨v,i⟩ ⟨w,j⟩ (rfl : i = j)
  unfold shake256.round_loop1.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem keccakRound (a b : Array U64 25#usize) (rc : U64) :
    Rel (shake256.round a rc) (shake256.round b rc) (fun _ _ => True) := by
  unfold shake256.round
  ct_steps

@[ct_rel] theorem permute (a b : Array U64 25#usize) :
    Rel (shake256.permute a) (shake256.permute b) (fun _ _ => True) := by
  unfold shake256.permute shake256.permute_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨v,i⟩ ⟨w,j⟩ (rfl : i = j)
  unfold shake256.permute_loop.body
  ct_steps
  all_goals simp_all

end Ct.Shake
