import Kdiag.Iota
import Kdiag.Diagonal
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
open KdiagRust.core.core_arch.x86.avx512f
set_option maxHeartbeats 4500000

def rotated (a : Grid) (diag : Bool) (r : Nat) (j : Fin 8) :=
  (a.val[r]! j ^^^ theta a j).rotateLeft (rotation diag r j.val % 64)
def evenB (a : Grid) (r : Nat) (j : Fin 8) := rotated a false r (col r 3 j.val)
def evenC (a : Grid) (r : Nat) (j : Fin 8) :=
  chi (evenB a r j) (evenB a ((r+1)%5) j) (evenB a ((r+2)%5) j)
def withRC (rc : U64) (r : Nat) (j : Fin 8) (x : BitVec 64) :=
  if r=0 ∧ j.val=0 then x ^^^ rc.bv else x
def evenCell (a : Grid) (rc : U64) (r : Nat) (j : Fin 8) :=
  let k := col r 1 j.val
  withRC rc (j.val%5) k (evenC a (j.val%5) k)

theorem even_spec (a : Grid) (rc : U64) : even a rc ⦃ out =>
    ∀ (r : Nat), r<5 → ∀ j, out.val[r]! j = evenCell a rc r j ⦄ := by
  unfold even
  step with delta_spec a as ⟨d,hd⟩
  step as ⟨v0,hv0⟩
  step with rotate_spec false 0#usize (by decide) v0 d as ⟨x0,hx0⟩
  step with move_spec 0#usize 3#usize (by decide) (by decide) x0 as ⟨b0,hb0⟩
  step as ⟨v1,hv1⟩
  step with rotate_spec false 1#usize (by decide) v1 d as ⟨x1,hx1⟩
  step with move_spec 1#usize 3#usize (by decide) (by decide) x1 as ⟨b1,hb1⟩
  step as ⟨v2,hv2⟩
  step with rotate_spec false 2#usize (by decide) v2 d as ⟨x2,hx2⟩
  step with move_spec 2#usize 3#usize (by decide) (by decide) x2 as ⟨b2,hb2⟩
  step as ⟨v3,hv3⟩
  step with rotate_spec false 3#usize (by decide) v3 d as ⟨x3,hx3⟩
  step with move_spec 3#usize 3#usize (by decide) (by decide) x3 as ⟨b3,hb3⟩
  step as ⟨v4,hv4⟩
  step with rotate_spec false 4#usize (by decide) v4 d as ⟨x4,hx4⟩
  step with move_spec 4#usize 3#usize (by decide) (by decide) x4 as ⟨b4,hb4⟩
  let b := Array.make 5#usize [b0,b1,b2,b3,b4]
  have beq (r : Nat) (hr : r<5) (j : Fin 8) : b.val[r]! j = evenB a r j := by
    interval_cases r <;> simp [b,evenB,rotated,Array.make_val,hb0,hb1,hb2,hb3,hb4,
      hx0,hx1,hx2,hx3,hx4,hv0,hv1,hv2,hv3,hv4,hd,getElem!_pos]
  step with across b as ⟨c,hc⟩
  have ceq (r : Nat) (hr : r<5) (j : Fin 8) : c.val[r]! j = evenC a r j := by
    rw [hc r hr j, beq _ hr, beq _ (Nat.mod_lt _ (by decide)), beq _ (Nat.mod_lt _ (by decide))]
    rfl
  have continueIota {α : Type} (k : Grid → Result α) (P : α → Prop)
      (rest : ∀ x, (∀ (r : Nat), r<5 → ∀ j : Fin 8, x.val[r]! j =
        if r=0 ∧ j.val=0 then c.val[r]! j ^^^ rc.bv else c.val[r]! j) → k x ⦃ y => P y ⦄) :
      (do
        let old ← c.index_usize 0#usize
        let idx ← lift (UScalar.hcast .I64 rc)
        let krc ← _mm512_set1_epi64 idx
        let v ← _mm512_mask_xor_epi64 old 1#u8 old krc
        let out ← c.update 0#usize v
        k out) ⦃ y => P y ⦄ := by
    simpa only [addConstant,bind_tc_eq,Std.bind_assoc] using WP.spec_bind (iota_spec rc c) rest
  apply continueIota
  intro x hrc
  step with diagonal_spec 0#usize (by decide) x as ⟨q0,hq0⟩
  step with diagonal_spec 1#usize (by decide) x as ⟨q1,hq1⟩
  step with diagonal_spec 2#usize (by decide) x as ⟨q2,hq2⟩
  step with diagonal_spec 3#usize (by decide) x as ⟨q3,hq3⟩
  step with diagonal_spec 4#usize (by decide) x as ⟨q4,hq4⟩
  intro r hr j
  interval_cases r <;> simp [Array.make_val,evenCell,withRC,hq0,hq1,hq2,hq3,hq4,
    hrc _ (Nat.mod_lt _ (by decide : 0<5)),ceq _ (Nat.mod_lt _ (by decide : 0<5))]
end slhdsa.Kdiag
