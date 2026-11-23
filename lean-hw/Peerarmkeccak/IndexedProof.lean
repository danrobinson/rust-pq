import Peerarmkeccak.IndexedProgram
import Peerarmkeccak.SoftLinuxProof

open Spec.Keccak
namespace PeerKeccak.Indexed
set_option maxRecDepth 65536

theorem round_eq (a : State) (rc : Lane) : round a rc = PeerKeccak.SoftLinux.round a rc := by
  apply Array.ext
  · rfl
  · intro i hi hj
    change i < 25 at hi
    interval_cases i <;> first | rfl | (simp [round, PeerKeccak.SoftLinux.round]; ac_rfl)

theorem permute_fips (a : State) : permute a = Spec.Keccak.permute a := by
  have r : round = PeerKeccak.SoftLinux.round := funext fun a => funext fun rc => round_eq a rc
  rw [permute, r]
  exact PeerKeccak.SoftLinux.permute_fips a

#print axioms permute_fips
end PeerKeccak.Indexed
