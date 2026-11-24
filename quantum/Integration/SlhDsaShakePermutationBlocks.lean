import Integration.SlhDsaShakePermutationPadding
import Integration.SlhDsaShakePermutationMask

/-! Little-endian SHAKE rate blocks at the byte-string / sponge boundary. -/
namespace Reduction.ShakePermutation
open Spec.Keccak

def lane (b : Fin 8 → Spec.Byte) : UInt64 :=
  UInt64.ofBitVec (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0)

def laneByte (x : UInt64) (i : Fin 8) : Spec.Byte :=
  (x.toBitVec >>> (8*i.val)).truncate 8

theorem laneByte_lane (b : Fin 8 → Spec.Byte) (i : Fin 8) : laneByte (lane b) i = b i := by
  fin_cases i <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    interval_cases j <;> simp only [lane,laneByte,UInt64.toBitVec_ofBitVec,BitVec.truncate,
      BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append] <;> norm_num

/-- Read up to 136 bytes at a block offset into the first seventeen Keccak lanes. -/
def rateBlock (xs : Spec.Bytes) (block : ℕ) : Rate := fun w =>
  lane (fun j => xs[136*block + 8*w.val+j.val]?.getD 0)

def blockByte (w : Rate) (i : Fin 136) : Spec.Byte :=
  laneByte (w ⟨i.val/8,by omega⟩) ⟨i.val%8,by omega⟩

theorem blockByte_rateBlock (xs : Spec.Bytes) (b : ℕ) (i : Fin 136) :
    blockByte (rateBlock xs b) i = xs[136*b+i.val]?.getD 0 := by
  unfold blockByte rateBlock
  rw [laneByte_lane]
  change xs[136*b + 8*(i.val/8)+i.val%8]?.getD 0 = _
  rw [show 136*b+8*(i.val/8)+i.val%8=136*b+i.val by omega]

def messageBlocks (xs : Spec.Bytes) : List Rate :=
  List.ofFn (fun i : Fin (xs.length/136+1) => rateBlock (padded xs) i.val)

theorem messageBlocks_length (xs : Spec.Bytes) : (messageBlocks xs).length = xs.length/136+1 := by
  simp [messageBlocks]

theorem messageBlocks_injective : Function.Injective messageBlocks := by
  intro xs ys h
  apply padded_injective
  have len := congrArg List.length h
  simp only [messageBlocks_length] at len
  apply List.ext_getElem
  · rw [padded_length,padded_length,len]
  · intro i hx hy
    have hb : i/136 < xs.length/136+1 := by rw [padded_length] at hx; omega
    have hb' : i/136 < ys.length/136+1 := len ▸ hb
    have eq : rateBlock (padded xs) (i/136) = rateBlock (padded ys) (i/136) := by
      have e := congrArg (fun bs : List Rate => bs[i/136]?) h
      have ax : i/136 < (messageBlocks xs).length := by rwa [messageBlocks_length]
      have ay : i/136 < (messageBlocks ys).length := by rwa [messageBlocks_length]
      simp only [List.getElem?_eq_getElem ax,List.getElem?_eq_getElem ay,Option.some.injEq] at e
      simpa only [messageBlocks,List.getElem_ofFn] using e
    let off : Fin 136 := ⟨i%136,Nat.mod_lt _ (by decide)⟩
    have e := congrArg (fun x => blockByte x off) eq
    rw [blockByte_rateBlock,blockByte_rateBlock] at e
    simpa only [off, show 136*(i/136) + i%136 = i by omega,List.getElem?_eq_getElem hx,
      List.getElem?_eq_getElem hy, Option.getD_some] using e

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.messageBlocks_injective
