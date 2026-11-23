import Kmixedperm.Loop
import Kmixed.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kmixedperm
open KeccakRegisters KmixedpermRust
open KmixedpermRust.shake256.parallel
theorem native_view (a : Rows) (j : Fin 3) : Kmixed.lane (native a) j = lane a j := by
  unfold Kmixed.lane lane
  congr 1
  funext i
  rw [getElem!_pos (native a).val i.val (by simpa using i.isLt),getElem!_pos a.val i.val (by simpa using i.isLt)]
  simp only [native, Array.from_val,List.getElem_map]
  rfl

theorem local_view (a : Kmixed.Rows) (j : Fin 3) : lane (localRows a) j = Kmixed.lane a j := by
  unfold Kmixed.lane lane
  congr 1
  funext i
  rw [getElem!_pos (localRows a).val i.val (by simpa using i.isLt),getElem!_pos a.val i.val (by simpa using i.isLt)]
  simp only [localRows, Array.from_val,List.getElem_map]
  rfl

theorem permute_of_native (one : ∀ (a : Kmixed.Rows) (rc : U64),
    KmixedRust.shake256.parallel.mixed.round a rc ⦃ out => ∀ j, Kmixed.lane out j = round (Kmixed.lane a j) rc.bv ⦄)
    (words : Matrix 3#usize) : mixed.permute words ⦃ out => ∀ j, view out j = permute (view words j) ⦄ := by
  apply permute_of_round _ words
  intro a rc
  unfold mixed.round
  apply WP.spec_bind (one (native a) rc)
  intro b hb
  exact (WP.spec_ok _).mpr (fun j => by rw [local_view,hb,native_view])
end slhdsa.Kmixedperm
