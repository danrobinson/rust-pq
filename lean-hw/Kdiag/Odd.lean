import Kdiag.Even
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
set_option maxHeartbeats 4000000

def oddB (a : Grid) (r : Nat) (j : Fin 8) :=
  match r with
  | 0 => rotated a true 0 j
  | 1 => rotated a true 2 (col 3 1 j.val)
  | 2 => rotated a true 4 (col 1 1 j.val)
  | 3 => rotated a true 1 (col 4 1 j.val)
  | _ => rotated a true 3 (col 2 1 j.val)

def oddCell (a : Grid) (rc : U64) (r : Nat) (j : Fin 8) :=
  withRC rc r j (chi (oddB a r j) (oddB a r (col 1 1 j.val)) (oddB a r (col 2 1 j.val)))

theorem odd_spec (a : Grid) (rc : U64) : odd a rc ⦃ out =>
    ∀ (r : Nat), r<5 → ∀ j, out.val[r]! j = oddCell a rc r j ⦄ := by
  unfold odd
  step with delta_spec a as ⟨d,hd⟩
  step as ⟨v0,hv0⟩
  step with rotate_spec true 0#usize (by decide) v0 d as ⟨b0,hb0⟩
  step as ⟨v1,hv1⟩
  step with rotate_spec true 2#usize (by decide) v1 d as ⟨x1,hx1⟩
  step with move_spec 3#usize 1#usize (by decide) (by decide) x1 as ⟨b1,hb1⟩
  step as ⟨v2,hv2⟩
  step with rotate_spec true 4#usize (by decide) v2 d as ⟨x2,hx2⟩
  step with move_spec 1#usize 1#usize (by decide) (by decide) x2 as ⟨b2,hb2⟩
  step as ⟨v3,hv3⟩
  step with rotate_spec true 1#usize (by decide) v3 d as ⟨x3,hx3⟩
  step with move_spec 4#usize 1#usize (by decide) (by decide) x3 as ⟨b3,hb3⟩
  step as ⟨v4,hv4⟩
  step with rotate_spec true 3#usize (by decide) v4 d as ⟨x4,hx4⟩
  step with move_spec 2#usize 1#usize (by decide) (by decide) x4 as ⟨b4,hb4⟩
  let b := Array.make 5#usize [b0,b1,b2,b3,b4]
  have beq (r : Nat) (hr : r<5) (j : Fin 8) : b.val[r]! j = oddB a r j := by
    interval_cases r <;> simp [b,oddB,rotated,Array.make_val,hb0,hb1,hb2,hb3,hb4,
      hx1,hx2,hx3,hx4,hv0,hv1,hv2,hv3,hv4,hd,getElem!_pos]
  step with within b as ⟨c,hc⟩
  apply WP.spec_mono (iota_spec rc c)
  intro out ho r hr j
  dsimp only [b] at beq
  simp only [ho r hr j,hc r hr,beq _ hr,oddCell,withRC]
end slhdsa.Kdiag
