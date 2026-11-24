import MIdeal.Sha512
import HashSig.SLHDSA.EncodingLemmas

namespace MIdeal.Sha512
open Ideal SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

def serialize (s : Chain512) : Bytes 64 :=
  ⟨(stateBytes64 s.toArray).data, stateBytes64_size s.toArray⟩

private theorem encode_injective : Function.Injective (fun x : BitVec 64 => Spec.toByte x.toNat 8) := by
  intro x y h
  dsimp only at h
  rw [← MLink.toByte_eq, ← MLink.toByte_eq] at h
  have eq := congrArg SLHDSA.toInt (MLink.sp_injective h)
  rw [toInt_toByte _ _ x.isLt, toInt_toByte _ _ y.isLt] at eq
  exact BitVec.eq_of_toNat_eq eq

private theorem flat_injective :
    Function.Injective (fun xs : List (BitVec 64) => xs.flatMap fun x => Spec.toByte x.toNat 8) := by
  intro xs
  induction xs with
  | nil =>
    rintro (_|⟨y,ys⟩) h
    · rfl
    · have := congrArg List.length h
      simp [Spec.toByte] at this <;> omega
  | cons x xs ih =>
    rintro (_|⟨y,ys⟩) h
    · have := congrArg List.length h
      simp [Spec.toByte] at this <;> omega
    · simp only [List.flatMap_cons] at h
      obtain ⟨h₁,h₂⟩ := List.append_inj h (by simp [Spec.toByte])
      rw [encode_injective h₁, ih h₂]

theorem serialize_injective : Function.Injective serialize := by
  intro x y h
  have hb := congrArg (fun b : Bytes 64 => MLink.spA ((bytesToByteArray b).extract 0 64)) h
  change MLink.spA ((stateBytes64 x.toArray).extract 0 64) =
    MLink.spA ((stateBytes64 y.toArray).extract 0 64) at hb
  rw [MLink.stateBytes64_eq _ x.size_toArray, MLink.stateBytes64_eq _ y.size_toArray] at hb
  have hw := flat_injective hb
  apply Vector.toList_inj.mp
  exact List.map_injective_iff.mpr (fun _ _ h => UInt64.eq_of_toBitVec_eq h) hw

theorem card_chain512 : Fintype.card Chain512 = 2^512 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Vector UInt64 8) = _
  rw [Nat.card_congr (arrayVectorEquivFin UInt64 8), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide +kernel

theorem serialize_bijective : Function.Bijective serialize :=
  (Fintype.bijective_iff_injective_and_card serialize).2 ⟨serialize_injective, by
    rw [card_chain512, card_bytes]; decide +kernel⟩
end MIdeal.Sha512

#print axioms MIdeal.Sha512.serialize_bijective
