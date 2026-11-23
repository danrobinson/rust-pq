import Shakebatch.WotsWords
import Shakebatch.WotsResult
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

private theorem decoded (a : Array U8 8#usize) (b : Nat) (hb : b<8) :
    ((core.num.U64.from_le_bytes a).bv >>> (8*b)).setWidth 8 = a.val[b]!.bv := by
  let v := a.val.map (·.bv)
  have len : v.length=8 := by simp [v]
  have atByte (p : Nat) (hp : p<8) := BitVec.fromLEBytes_getElem v (8*b+p) (by omega)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bit := atByte i hi
  have byte := BitVec.getElem_eq_testBit_toNat a.val[b]!.bv i hi
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_setWidth',BitVec.getLsbD_ushiftRight,
    hi,decide_true,Bool.true_and]
  have fit : 8*b+i < 64 := by omega
  rw [BitVec.getLsbD_eq_getElem (h:=fit)]
  change ((BitVec.fromLEBytes v).cast (show 8*v.length=64 by omega))[8*b+i]=_
  simpa only [BitVec.getElem_cast,show (8*b+i)/8=b by omega,show (8*b+i)%8=i by omega,
    v,List.getElem_map,BitVec.getElem_eq_testBit_toNat,BitVec.getLsbD_eq_getElem (h:=hi),
    BitVec.toNat_cast,Byte.testBit,getElem!_pos a.val b (by simpa using hb)] using bit

variable [machine : Machine]

theorem decoded_cell {N : Usize} (s : Matrix machine.width) (j off b : Nat) (v : Array U8 N)
    (bound : b<N.val) (aligned : N.val%8=0)
    (cellAt : cell s (off+b/8) j = inputWord v.val (b/8)) :
    (stateByte s j (off+b/8) (b%8)).bv = v.val[b]!.bv := by
  let pos := b/8*8
  have room : pos+8≤N.val := by dsimp [pos];omega
  let buf := Array.from (n:=8#usize) ((v.val.drop pos).take 8) (by simp; omega)
  have word : inputWord v.val (b/8)=(core.num.U64.from_le_bytes buf).bv := by
    rw [PlatformShake.loaded]
    simp only [inputWord,buf,pos,Array.from_val]
  rw [stateByte,le_byte _ _ (by omega)]
  change (cell s (off+b/8) j >>> (8*(b%8))).setWidth 8=_
  rw [cellAt,word,decoded _ _ (by omega)]
  have atPos : b%8 < buf.val.length := by simp [buf];omega
  rw [getElem!_pos buf.val (b%8) atPos]
  simp only [buf,Array.from_val,List.getElem_take,List.getElem_drop]
  rw [← getElem!_pos,show pos+b%8=b by dsimp [pos];omega]

end slhdsa.ShakeBatch
