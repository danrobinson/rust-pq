import Shani.Digest
import Slhdsa.Proofs.Platform

open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open ShaNiRust.sha256.x86

def packedState (iv : Array Reg 2#usize) := decode iv.val[0]! iv.val[1]!

private theorem packed_work (iv : Array Reg 2#usize) : Work iv (packedState iv) := by
  unfold Work packedState
  cases iv.val[0]! <;> cases iv.val[1]! <;> exact ⟨rfl,rfl⟩

private theorem initial_good (iv : Array Reg 2#usize) (w : Array Reg 4#usize) (B : Spec.Bytes)
    (h : w.val = [blockGroup B 0,blockGroup B 16,blockGroup B 32,blockGroup B 48]) :
    Good ⟨iv,w⟩ (Spec.SHA256.schedule B) (packedState iv) 0 := by
  refine ⟨?_, packed_work iv⟩
  intro g _ hg
  change g < 4 at hg
  rw [h]
  interval_cases g <;> simp (disch := decide) only [group, slhdsa.schedule_lt16] <;> rfl

set_option maxHeartbeats 3000000 in
/-- For arbitrary input blocks and a packed chaining state, both returned byte arrays
are the big-endian serialization of their FIPS 180-4 compression results. -/
theorem compress_pair_spec (iv : Array Reg 2#usize) (left right : Array U8 64#usize) :
    compress_pair iv left right ⦃ out => out.val.map (·.val) =
      [serialize (Spec.SHA256.compress (stateWords (packedState iv)) (bytes left.val)),
       serialize (Spec.SHA256.compress (stateWords (packedState iv)) (bytes right.val))] ⦄ := by
  unfold compress_pair
  step with load_spec left as ⟨wl,hl⟩
  step with load_spec right as ⟨wr,hr⟩
  have hleft := initial_good iv wl _ hl
  have hright := initial_good iv wr _ hr
  have recB (B : Spec.Bytes) : Rec (Spec.SHA256.schedule B) := fun k lo hi => slhdsa.schedule_rec B k lo hi
  iterate 16
    apply WP.spec_bind (pair_spec _ _ _ _ _ (packedState iv) (by decide) (by assumption) (by assumption) (recB _) (recB _))
    rintro ⟨l,r⟩ ⟨hlast,hrlast⟩
  step with digest_spec iv l.work _ _ (packed_work iv) hlast.2 as ⟨dl,hdl⟩
  step with digest_spec iv r.work _ _ (packed_work iv) hrlast.2 as ⟨dr,hdr⟩
  simp only [step_simps, Array.make]
  change [dl.val, dr.val] = _
  rw [hdl,hdr]
  exact congrArg₂ List.cons (congrArg serialize (X86.finish (packedState iv) (bytes left.val))) (congrArg (fun x => [serialize x]) (X86.finish (packedState iv) (bytes right.val)))

#print axioms compress_pair_spec
end slhdsa.Intel
