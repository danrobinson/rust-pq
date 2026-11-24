import Spec.AppleShakeDigest
import Shakebatch.Oneblock

namespace LinkedArm.Fors
open Spec Spec.Keccak

/-- Each batched PRF, F or H call checks this exact little-endian padded state and
    projects the first n bytes of one independent lane of the linked permutation. -/
theorem short_hash (scratch : Lane → ArmSha3Binary.Registers) (m : Bytes)
    (n : Nat) (limit : m.length ≤ 128) (aligned : m.length % 8 = 0) (fit : n ≤ 136) :
    (List.range n).map (fun i => extractByte
      (linkedConstants.foldl (machineRound scratch) (padded m)) i) = shake256 m n := by
  rw [permutation_eq, shake256, padded_fips m limit aligned, squeeze_short _ _ _ (by omega)]
  simp

/-- The root accumulator absorbs an aligned 8-byte word at each step. This includes
    the call to the measured permutation when that word completes a rate block. -/
theorem absorb_word (scratch : Lane → ArmSha3Binary.Registers) (a : State)
    (lane : Nat) (input : Bytes) (eight : input.length = 8)
    (valid : lane < a.size) (rate : lane < 17) :
    input.foldl feed (a,8*lane) =
      let next := a.setIfInBounds lane (a[lane]! ^^^ laneBytes 0 input)
      if lane = 16 then (linkedConstants.foldl (machineRound scratch) next,0)
      else (next,8*lane+8) := by
  simpa only [permutation_eq] using feedWord a lane input eight valid rate

end LinkedArm.Fors
