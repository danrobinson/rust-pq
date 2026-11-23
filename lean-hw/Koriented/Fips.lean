import Koriented.Chi
import Koriented.Round
import Spec.ShakeWords
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Oriented
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def decode (a : Array U64 25#usize) : State :=
  _root_.Array.ofFn (n := 25) fun i =>
    a.val[i.val]!.bv.rotateLeft (KorientedRust.shake256.oriented.OFF.val[i.val]!.val)

theorem decodedAt (a : Array U64 25#usize) (i : Nat) (h : i < 25) :
    (decode a)[i]! = a.val[i]!.bv.rotateLeft (KorientedRust.shake256.oriented.OFF.val[i]!.val) := ofFnAt _ _ h

def before (a : Array U64 25#usize) : Array U64 25#usize := Id.run do
  let i := a.val[0]!
  let i1 := core.num.U64.rotate_left i 0#u32
  let i2 := a.val[5]!
  let i3 := core.num.U64.rotate_left i2 28#u32
  let i4 := i1 ^^^ i3
  let i5 := a.val[10]!
  let i6 := core.num.U64.rotate_left i5 1#u32
  let i7 := i4 ^^^ i6
  let i8 := a.val[15]!
  let i9 := core.num.U64.rotate_left i8 27#u32
  let i10 := i7 ^^^ i9
  let i11 := a.val[20]!
  let i12 := core.num.U64.rotate_left i11 62#u32
  let i13 := i10 ^^^ i12
  let i14 := a.val[1]!
  let i15 := core.num.U64.rotate_left i14 44#u32
  let i16 := a.val[6]!
  let i17 := core.num.U64.rotate_left i16 20#u32
  let i18 := i15 ^^^ i17
  let i19 := a.val[11]!
  let i20 := core.num.U64.rotate_left i19 6#u32
  let i21 := i18 ^^^ i20
  let i22 := a.val[16]!
  let i23 := core.num.U64.rotate_left i22 36#u32
  let i24 := i21 ^^^ i23
  let i25 := a.val[21]!
  let i26 := core.num.U64.rotate_left i25 55#u32
  let i27 := i24 ^^^ i26
  let i28 := a.val[2]!
  let i29 := core.num.U64.rotate_left i28 43#u32
  let i30 := a.val[7]!
  let i31 := core.num.U64.rotate_left i30 3#u32
  let i32 := i29 ^^^ i31
  let i33 := a.val[12]!
  let i34 := core.num.U64.rotate_left i33 25#u32
  let i35 := i32 ^^^ i34
  let i36 := a.val[17]!
  let i37 := core.num.U64.rotate_left i36 10#u32
  let i38 := i35 ^^^ i37
  let i39 := a.val[22]!
  let i40 := core.num.U64.rotate_left i39 39#u32
  let i41 := i38 ^^^ i40
  let i42 := a.val[3]!
  let i43 := core.num.U64.rotate_left i42 21#u32
  let i44 := a.val[8]!
  let i45 := core.num.U64.rotate_left i44 45#u32
  let i46 := i43 ^^^ i45
  let i47 := a.val[13]!
  let i48 := core.num.U64.rotate_left i47 8#u32
  let i49 := i46 ^^^ i48
  let i50 := a.val[18]!
  let i51 := core.num.U64.rotate_left i50 15#u32
  let i52 := i49 ^^^ i51
  let i53 := a.val[23]!
  let i54 := core.num.U64.rotate_left i53 41#u32
  let i55 := i52 ^^^ i54
  let i56 := a.val[4]!
  let i57 := core.num.U64.rotate_left i56 14#u32
  let i58 := a.val[9]!
  let i59 := core.num.U64.rotate_left i58 61#u32
  let i60 := i57 ^^^ i59
  let i61 := a.val[14]!
  let i62 := core.num.U64.rotate_left i61 18#u32
  let i63 := i60 ^^^ i62
  let i64 := a.val[19]!
  let i65 := core.num.U64.rotate_left i64 56#u32
  let i66 := i63 ^^^ i65
  let i67 := a.val[24]!
  let i68 := core.num.U64.rotate_left i67 2#u32
  let i69 := i66 ^^^ i68
  let i70 := i69
  let i71 := i27
  let i72 := core.num.U64.rotate_left i71 1#u32
  let i73 := i70 ^^^ i72
  let i74 := i13
  let i75 := i41
  let i76 := core.num.U64.rotate_left i75 1#u32
  let i77 := i74 ^^^ i76
  let i78 := i55
  let i79 := core.num.U64.rotate_left i78 1#u32
  let i80 := i71 ^^^ i79
  let i81 := core.num.U64.rotate_left i70 1#u32
  let i82 := i75 ^^^ i81
  let i83 := core.num.U64.rotate_left i74 1#u32
  let i84 := i78 ^^^ i83
  let i85 := i73
  let i86 := core.num.U64.rotate_left i 0#u32
  let i87 := i85 ^^^ i86
  let i88 := i77
  let i89 := core.num.U64.rotate_left i16 20#u32
  let i90 := i88 ^^^ i89
  let i91 := i80
  let i92 := core.num.U64.rotate_left i33 25#u32
  let i93 := i91 ^^^ i92
  let i94 := i82
  let i95 := core.num.U64.rotate_left i50 15#u32
  let i96 := i94 ^^^ i95
  let i97 := i84
  let i98 := core.num.U64.rotate_left i67 2#u32
  let i99 := i97 ^^^ i98
  let i100 := core.num.U64.rotate_left i42 21#u32
  let i101 := i94 ^^^ i100
  let i102 := core.num.U64.rotate_left i58 61#u32
  let i103 := i97 ^^^ i102
  let i104 := core.num.U64.rotate_left i5 1#u32
  let i105 := i85 ^^^ i104
  let i106 := core.num.U64.rotate_left i22 36#u32
  let i107 := i88 ^^^ i106
  let i108 := core.num.U64.rotate_left i39 39#u32
  let i109 := i91 ^^^ i108
  let i110 := core.num.U64.rotate_left i14 44#u32
  let i111 := i88 ^^^ i110
  let i112 := core.num.U64.rotate_left i30 3#u32
  let i113 := i91 ^^^ i112
  let i114 := core.num.U64.rotate_left i47 8#u32
  let i115 := i94 ^^^ i114
  let i116 := core.num.U64.rotate_left i64 56#u32
  let i117 := i97 ^^^ i116
  let i118 := core.num.U64.rotate_left i11 62#u32
  let i119 := i85 ^^^ i118
  let i120 := core.num.U64.rotate_left i56 14#u32
  let i121 := i97 ^^^ i120
  let i122 := core.num.U64.rotate_left i2 28#u32
  let i123 := i85 ^^^ i122
  let i124 := core.num.U64.rotate_left i19 6#u32
  let i125 := i88 ^^^ i124
  let i126 := core.num.U64.rotate_left i36 10#u32
  let i127 := i91 ^^^ i126
  let i128 := core.num.U64.rotate_left i53 41#u32
  let i129 := i94 ^^^ i128
  let i130 := core.num.U64.rotate_left i28 43#u32
  let i131 := i91 ^^^ i130
  let i132 := core.num.U64.rotate_left i44 45#u32
  let i133 := i94 ^^^ i132
  let i134 := core.num.U64.rotate_left i61 18#u32
  let i135 := i97 ^^^ i134
  let i136 := core.num.U64.rotate_left i8 27#u32
  let i137 := i85 ^^^ i136
  let i138 := core.num.U64.rotate_left i25 55#u32
  let i139 := i88 ^^^ i138
  return Array.make 25#usize [i87, i90, i93, i96, i99, i101, i103, i105, i107, i109, i111, i113, i115, i117, i119, i121, i123, i125, i127, i129, i131, i133, i135, i137, i139]

private theorem rho0 (a : Array U64 25#usize) :
    (before a).val[0]!.bv.rotateLeft 0 = rhoPi (decode a) 0 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)) ^^^ ((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 1)
  change (d ^^^ (a.val[0]!.bv.rotateLeft 0)).rotateLeft 0 = ((a.val[0]!.bv.rotateLeft 0) ^^^ d).rotateLeft 0
  rw [BitVec.xor_comm d]

private theorem rho1 (a : Array U64 25#usize) :
    (before a).val[1]!.bv.rotateLeft 44 = rhoPi (decode a) 1 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)) ^^^ ((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 1)
  change (d ^^^ (a.val[6]!.bv.rotateLeft 20)).rotateLeft 44 = ((a.val[6]!.bv.rotateLeft 20) ^^^ d).rotateLeft 44
  rw [BitVec.xor_comm d]

private theorem rho2 (a : Array U64 25#usize) :
    (before a).val[2]!.bv.rotateLeft 43 = rhoPi (decode a) 2 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)) ^^^ ((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 1)
  change (d ^^^ (a.val[12]!.bv.rotateLeft 25)).rotateLeft 43 = ((a.val[12]!.bv.rotateLeft 25) ^^^ d).rotateLeft 43
  rw [BitVec.xor_comm d]

private theorem rho3 (a : Array U64 25#usize) :
    (before a).val[3]!.bv.rotateLeft 21 = rhoPi (decode a) 3 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)) ^^^ ((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 1)
  change (d ^^^ (a.val[18]!.bv.rotateLeft 15)).rotateLeft 21 = ((a.val[18]!.bv.rotateLeft 15) ^^^ d).rotateLeft 21
  rw [BitVec.xor_comm d]

private theorem rho4 (a : Array U64 25#usize) :
    (before a).val[4]!.bv.rotateLeft 14 = rhoPi (decode a) 4 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)) ^^^ ((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 1)
  change (d ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 14 = ((a.val[24]!.bv.rotateLeft 2) ^^^ d).rotateLeft 14
  rw [BitVec.xor_comm d]

private theorem rho5 (a : Array U64 25#usize) :
    (before a).val[5]!.bv.rotateLeft 28 = rhoPi (decode a) 5 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)) ^^^ ((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 1)
  change (d ^^^ (a.val[3]!.bv.rotateLeft 21)).rotateLeft 28 = ((a.val[3]!.bv.rotateLeft 21) ^^^ d).rotateLeft 28
  rw [BitVec.xor_comm d]

private theorem rho6 (a : Array U64 25#usize) :
    (before a).val[6]!.bv.rotateLeft 20 = rhoPi (decode a) 6 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)) ^^^ ((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 1)
  change (d ^^^ (a.val[9]!.bv.rotateLeft 61)).rotateLeft 20 = ((a.val[9]!.bv.rotateLeft 61) ^^^ d).rotateLeft 20
  rw [BitVec.xor_comm d]

private theorem rho7 (a : Array U64 25#usize) :
    (before a).val[7]!.bv.rotateLeft 3 = rhoPi (decode a) 7 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)) ^^^ ((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 1)
  change (d ^^^ (a.val[10]!.bv.rotateLeft 1)).rotateLeft 3 = ((a.val[10]!.bv.rotateLeft 1) ^^^ d).rotateLeft 3
  rw [BitVec.xor_comm d]

private theorem rho8 (a : Array U64 25#usize) :
    (before a).val[8]!.bv.rotateLeft 45 = rhoPi (decode a) 8 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)) ^^^ ((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 1)
  change (d ^^^ (a.val[16]!.bv.rotateLeft 36)).rotateLeft 45 = ((a.val[16]!.bv.rotateLeft 36) ^^^ d).rotateLeft 45
  rw [BitVec.xor_comm d]

private theorem rho9 (a : Array U64 25#usize) :
    (before a).val[9]!.bv.rotateLeft 61 = rhoPi (decode a) 9 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)) ^^^ ((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 1)
  change (d ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 61 = ((a.val[22]!.bv.rotateLeft 39) ^^^ d).rotateLeft 61
  rw [BitVec.xor_comm d]

private theorem rho10 (a : Array U64 25#usize) :
    (before a).val[10]!.bv.rotateLeft 1 = rhoPi (decode a) 10 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)) ^^^ ((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 1)
  change (d ^^^ (a.val[1]!.bv.rotateLeft 44)).rotateLeft 1 = ((a.val[1]!.bv.rotateLeft 44) ^^^ d).rotateLeft 1
  rw [BitVec.xor_comm d]

private theorem rho11 (a : Array U64 25#usize) :
    (before a).val[11]!.bv.rotateLeft 6 = rhoPi (decode a) 11 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)) ^^^ ((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 1)
  change (d ^^^ (a.val[7]!.bv.rotateLeft 3)).rotateLeft 6 = ((a.val[7]!.bv.rotateLeft 3) ^^^ d).rotateLeft 6
  rw [BitVec.xor_comm d]

private theorem rho12 (a : Array U64 25#usize) :
    (before a).val[12]!.bv.rotateLeft 25 = rhoPi (decode a) 12 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)) ^^^ ((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 1)
  change (d ^^^ (a.val[13]!.bv.rotateLeft 8)).rotateLeft 25 = ((a.val[13]!.bv.rotateLeft 8) ^^^ d).rotateLeft 25
  rw [BitVec.xor_comm d]

private theorem rho13 (a : Array U64 25#usize) :
    (before a).val[13]!.bv.rotateLeft 8 = rhoPi (decode a) 13 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)) ^^^ ((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 1)
  change (d ^^^ (a.val[19]!.bv.rotateLeft 56)).rotateLeft 8 = ((a.val[19]!.bv.rotateLeft 56) ^^^ d).rotateLeft 8
  rw [BitVec.xor_comm d]

private theorem rho14 (a : Array U64 25#usize) :
    (before a).val[14]!.bv.rotateLeft 18 = rhoPi (decode a) 14 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)) ^^^ ((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 1)
  change (d ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 18 = ((a.val[20]!.bv.rotateLeft 62) ^^^ d).rotateLeft 18
  rw [BitVec.xor_comm d]

private theorem rho15 (a : Array U64 25#usize) :
    (before a).val[15]!.bv.rotateLeft 27 = rhoPi (decode a) 15 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)) ^^^ ((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 1)
  change (d ^^^ (a.val[4]!.bv.rotateLeft 14)).rotateLeft 27 = ((a.val[4]!.bv.rotateLeft 14) ^^^ d).rotateLeft 27
  rw [BitVec.xor_comm d]

private theorem rho16 (a : Array U64 25#usize) :
    (before a).val[16]!.bv.rotateLeft 36 = rhoPi (decode a) 16 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)) ^^^ ((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 1)
  change (d ^^^ (a.val[5]!.bv.rotateLeft 28)).rotateLeft 36 = ((a.val[5]!.bv.rotateLeft 28) ^^^ d).rotateLeft 36
  rw [BitVec.xor_comm d]

private theorem rho17 (a : Array U64 25#usize) :
    (before a).val[17]!.bv.rotateLeft 10 = rhoPi (decode a) 17 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)) ^^^ ((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 1)
  change (d ^^^ (a.val[11]!.bv.rotateLeft 6)).rotateLeft 10 = ((a.val[11]!.bv.rotateLeft 6) ^^^ d).rotateLeft 10
  rw [BitVec.xor_comm d]

private theorem rho18 (a : Array U64 25#usize) :
    (before a).val[18]!.bv.rotateLeft 15 = rhoPi (decode a) 18 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)) ^^^ ((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 1)
  change (d ^^^ (a.val[17]!.bv.rotateLeft 10)).rotateLeft 15 = ((a.val[17]!.bv.rotateLeft 10) ^^^ d).rotateLeft 15
  rw [BitVec.xor_comm d]

private theorem rho19 (a : Array U64 25#usize) :
    (before a).val[19]!.bv.rotateLeft 56 = rhoPi (decode a) 19 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)) ^^^ ((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 1)
  change (d ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 56 = ((a.val[23]!.bv.rotateLeft 41) ^^^ d).rotateLeft 56
  rw [BitVec.xor_comm d]

private theorem rho20 (a : Array U64 25#usize) :
    (before a).val[20]!.bv.rotateLeft 62 = rhoPi (decode a) 20 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)) ^^^ ((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)).rotateLeft 1)
  change (d ^^^ (a.val[2]!.bv.rotateLeft 43)).rotateLeft 62 = ((a.val[2]!.bv.rotateLeft 43) ^^^ d).rotateLeft 62
  rw [BitVec.xor_comm d]

private theorem rho21 (a : Array U64 25#usize) :
    (before a).val[21]!.bv.rotateLeft 55 = rhoPi (decode a) 21 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)) ^^^ ((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)).rotateLeft 1)
  change (d ^^^ (a.val[8]!.bv.rotateLeft 45)).rotateLeft 55 = ((a.val[8]!.bv.rotateLeft 45) ^^^ d).rotateLeft 55
  rw [BitVec.xor_comm d]

private theorem rho22 (a : Array U64 25#usize) :
    (before a).val[22]!.bv.rotateLeft 39 = rhoPi (decode a) 22 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[3]!.bv.rotateLeft 21) ^^^ (a.val[8]!.bv.rotateLeft 45) ^^^ (a.val[13]!.bv.rotateLeft 8) ^^^ (a.val[18]!.bv.rotateLeft 15) ^^^ (a.val[23]!.bv.rotateLeft 41)) ^^^ ((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)).rotateLeft 1)
  change (d ^^^ (a.val[14]!.bv.rotateLeft 18)).rotateLeft 39 = ((a.val[14]!.bv.rotateLeft 18) ^^^ d).rotateLeft 39
  rw [BitVec.xor_comm d]

private theorem rho23 (a : Array U64 25#usize) :
    (before a).val[23]!.bv.rotateLeft 41 = rhoPi (decode a) 23 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[4]!.bv.rotateLeft 14) ^^^ (a.val[9]!.bv.rotateLeft 61) ^^^ (a.val[14]!.bv.rotateLeft 18) ^^^ (a.val[19]!.bv.rotateLeft 56) ^^^ (a.val[24]!.bv.rotateLeft 2)) ^^^ ((a.val[1]!.bv.rotateLeft 44) ^^^ (a.val[6]!.bv.rotateLeft 20) ^^^ (a.val[11]!.bv.rotateLeft 6) ^^^ (a.val[16]!.bv.rotateLeft 36) ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 1)
  change (d ^^^ (a.val[15]!.bv.rotateLeft 27)).rotateLeft 41 = ((a.val[15]!.bv.rotateLeft 27) ^^^ d).rotateLeft 41
  rw [BitVec.xor_comm d]

private theorem rho24 (a : Array U64 25#usize) :
    (before a).val[24]!.bv.rotateLeft 2 = rhoPi (decode a) 24 := by
  simp (disch := decide) only [rhoPi, theta, delta, parity, decodedAt]
  unfold KorientedRust.shake256.oriented.OFF
  let d := (((a.val[0]!.bv.rotateLeft 0) ^^^ (a.val[5]!.bv.rotateLeft 28) ^^^ (a.val[10]!.bv.rotateLeft 1) ^^^ (a.val[15]!.bv.rotateLeft 27) ^^^ (a.val[20]!.bv.rotateLeft 62)) ^^^ ((a.val[2]!.bv.rotateLeft 43) ^^^ (a.val[7]!.bv.rotateLeft 3) ^^^ (a.val[12]!.bv.rotateLeft 25) ^^^ (a.val[17]!.bv.rotateLeft 10) ^^^ (a.val[22]!.bv.rotateLeft 39)).rotateLeft 1)
  change (d ^^^ (a.val[21]!.bv.rotateLeft 55)).rotateLeft 2 = ((a.val[21]!.bv.rotateLeft 55) ^^^ d).rotateLeft 2
  rw [BitVec.xor_comm d]

private theorem rotZero (x : Lane) : x.rotateLeft 0 = x := by
  simp [BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]

private theorem decodeCell0 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[0]! = (round (decode a) rc.bv)[0]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 0 ^^^ ((~~~(rhoPi (decode a) 1)) &&& (rhoPi (decode a) 2))) ^^^ rc.bv
  rw [← rho0, ← rho1, ← rho2]
  unfold KorientedRust.shake256.oriented.OFF
  let x := (before a).val[0]!.bv
  let y := (before a).val[1]!.bv
  let z := (before a).val[2]!.bv
  change ((x ^^^ (z &&& ~~~(y.rotateLeft 1)).rotateLeft 43) ^^^ rc.bv).rotateLeft 0 =
    (x.rotateLeft 0 ^^^ ((~~~(y.rotateLeft 44)) &&& z.rotateLeft 43)) ^^^ rc.bv
  simpa only [rotZero] using congrArg (fun v => v ^^^ rc.bv) (chi0 x y z)

private theorem decodeCell1 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[1]! = (round (decode a) rc.bv)[1]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 1 ^^^ ((~~~(rhoPi (decode a) 2)) &&& (rhoPi (decode a) 3)))
  rw [← rho1, ← rho2, ← rho3]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi1 ((before a).val[1]!.bv) ((before a).val[2]!.bv) ((before a).val[3]!.bv)
  exact h
private theorem decodeCell2 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[2]! = (round (decode a) rc.bv)[2]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 2 ^^^ ((~~~(rhoPi (decode a) 3)) &&& (rhoPi (decode a) 4)))
  rw [← rho2, ← rho3, ← rho4]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi2 ((before a).val[2]!.bv) ((before a).val[3]!.bv) ((before a).val[4]!.bv)
  exact h
private theorem decodeCell3 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[3]! = (round (decode a) rc.bv)[3]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 3 ^^^ ((~~~(rhoPi (decode a) 4)) &&& (rhoPi (decode a) 0)))
  rw [← rho3, ← rho4, ← rho0]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi3 ((before a).val[3]!.bv) ((before a).val[4]!.bv) ((before a).val[0]!.bv)
  exact h
private theorem decodeCell4 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[4]! = (round (decode a) rc.bv)[4]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 4 ^^^ ((~~~(rhoPi (decode a) 0)) &&& (rhoPi (decode a) 1)))
  rw [← rho4, ← rho0, ← rho1]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi4 ((before a).val[4]!.bv) ((before a).val[0]!.bv) ((before a).val[1]!.bv)
  exact h
private theorem decodeCell5 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[5]! = (round (decode a) rc.bv)[5]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 5 ^^^ ((~~~(rhoPi (decode a) 6)) &&& (rhoPi (decode a) 7)))
  rw [← rho5, ← rho6, ← rho7]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi5 ((before a).val[5]!.bv) ((before a).val[6]!.bv) ((before a).val[7]!.bv)
  exact h
private theorem decodeCell6 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[6]! = (round (decode a) rc.bv)[6]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 6 ^^^ ((~~~(rhoPi (decode a) 7)) &&& (rhoPi (decode a) 8)))
  rw [← rho6, ← rho7, ← rho8]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi6 ((before a).val[6]!.bv) ((before a).val[7]!.bv) ((before a).val[8]!.bv)
  exact h
private theorem decodeCell7 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[7]! = (round (decode a) rc.bv)[7]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 7 ^^^ ((~~~(rhoPi (decode a) 8)) &&& (rhoPi (decode a) 9)))
  rw [← rho7, ← rho8, ← rho9]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi7 ((before a).val[7]!.bv) ((before a).val[8]!.bv) ((before a).val[9]!.bv)
  exact h
private theorem decodeCell8 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[8]! = (round (decode a) rc.bv)[8]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 8 ^^^ ((~~~(rhoPi (decode a) 9)) &&& (rhoPi (decode a) 5)))
  rw [← rho8, ← rho9, ← rho5]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi8 ((before a).val[8]!.bv) ((before a).val[9]!.bv) ((before a).val[5]!.bv)
  exact h
private theorem decodeCell9 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[9]! = (round (decode a) rc.bv)[9]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 9 ^^^ ((~~~(rhoPi (decode a) 5)) &&& (rhoPi (decode a) 6)))
  rw [← rho9, ← rho5, ← rho6]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi9 ((before a).val[9]!.bv) ((before a).val[5]!.bv) ((before a).val[6]!.bv)
  exact h
private theorem decodeCell10 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[10]! = (round (decode a) rc.bv)[10]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 10 ^^^ ((~~~(rhoPi (decode a) 11)) &&& (rhoPi (decode a) 12)))
  rw [← rho10, ← rho11, ← rho12]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi10 ((before a).val[10]!.bv) ((before a).val[11]!.bv) ((before a).val[12]!.bv)
  exact h
private theorem decodeCell11 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[11]! = (round (decode a) rc.bv)[11]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 11 ^^^ ((~~~(rhoPi (decode a) 12)) &&& (rhoPi (decode a) 13)))
  rw [← rho11, ← rho12, ← rho13]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi11 ((before a).val[11]!.bv) ((before a).val[12]!.bv) ((before a).val[13]!.bv)
  exact h
private theorem decodeCell12 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[12]! = (round (decode a) rc.bv)[12]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 12 ^^^ ((~~~(rhoPi (decode a) 13)) &&& (rhoPi (decode a) 14)))
  rw [← rho12, ← rho13, ← rho14]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi12 ((before a).val[12]!.bv) ((before a).val[13]!.bv) ((before a).val[14]!.bv)
  exact h
private theorem decodeCell13 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[13]! = (round (decode a) rc.bv)[13]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 13 ^^^ ((~~~(rhoPi (decode a) 14)) &&& (rhoPi (decode a) 10)))
  rw [← rho13, ← rho14, ← rho10]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi13 ((before a).val[13]!.bv) ((before a).val[14]!.bv) ((before a).val[10]!.bv)
  exact h
private theorem decodeCell14 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[14]! = (round (decode a) rc.bv)[14]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 14 ^^^ ((~~~(rhoPi (decode a) 10)) &&& (rhoPi (decode a) 11)))
  rw [← rho14, ← rho10, ← rho11]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi14 ((before a).val[14]!.bv) ((before a).val[10]!.bv) ((before a).val[11]!.bv)
  exact h
private theorem decodeCell15 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[15]! = (round (decode a) rc.bv)[15]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 15 ^^^ ((~~~(rhoPi (decode a) 16)) &&& (rhoPi (decode a) 17)))
  rw [← rho15, ← rho16, ← rho17]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi15 ((before a).val[15]!.bv) ((before a).val[16]!.bv) ((before a).val[17]!.bv)
  exact h
private theorem decodeCell16 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[16]! = (round (decode a) rc.bv)[16]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 16 ^^^ ((~~~(rhoPi (decode a) 17)) &&& (rhoPi (decode a) 18)))
  rw [← rho16, ← rho17, ← rho18]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi16 ((before a).val[16]!.bv) ((before a).val[17]!.bv) ((before a).val[18]!.bv)
  exact h
private theorem decodeCell17 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[17]! = (round (decode a) rc.bv)[17]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 17 ^^^ ((~~~(rhoPi (decode a) 18)) &&& (rhoPi (decode a) 19)))
  rw [← rho17, ← rho18, ← rho19]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi17 ((before a).val[17]!.bv) ((before a).val[18]!.bv) ((before a).val[19]!.bv)
  exact h
private theorem decodeCell18 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[18]! = (round (decode a) rc.bv)[18]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 18 ^^^ ((~~~(rhoPi (decode a) 19)) &&& (rhoPi (decode a) 15)))
  rw [← rho18, ← rho19, ← rho15]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi18 ((before a).val[18]!.bv) ((before a).val[19]!.bv) ((before a).val[15]!.bv)
  exact h
private theorem decodeCell19 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[19]! = (round (decode a) rc.bv)[19]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 19 ^^^ ((~~~(rhoPi (decode a) 15)) &&& (rhoPi (decode a) 16)))
  rw [← rho19, ← rho15, ← rho16]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi19 ((before a).val[19]!.bv) ((before a).val[15]!.bv) ((before a).val[16]!.bv)
  exact h
private theorem decodeCell20 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[20]! = (round (decode a) rc.bv)[20]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 20 ^^^ ((~~~(rhoPi (decode a) 21)) &&& (rhoPi (decode a) 22)))
  rw [← rho20, ← rho21, ← rho22]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi20 ((before a).val[20]!.bv) ((before a).val[21]!.bv) ((before a).val[22]!.bv)
  exact h
private theorem decodeCell21 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[21]! = (round (decode a) rc.bv)[21]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 21 ^^^ ((~~~(rhoPi (decode a) 22)) &&& (rhoPi (decode a) 23)))
  rw [← rho21, ← rho22, ← rho23]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi21 ((before a).val[21]!.bv) ((before a).val[22]!.bv) ((before a).val[23]!.bv)
  exact h
private theorem decodeCell22 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[22]! = (round (decode a) rc.bv)[22]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 22 ^^^ ((~~~(rhoPi (decode a) 23)) &&& (rhoPi (decode a) 24)))
  rw [← rho22, ← rho23, ← rho24]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi22 ((before a).val[22]!.bv) ((before a).val[23]!.bv) ((before a).val[24]!.bv)
  exact h
private theorem decodeCell23 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[23]! = (round (decode a) rc.bv)[23]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 23 ^^^ ((~~~(rhoPi (decode a) 24)) &&& (rhoPi (decode a) 20)))
  rw [← rho23, ← rho24, ← rho20]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi23 ((before a).val[23]!.bv) ((before a).val[24]!.bv) ((before a).val[20]!.bv)
  exact h
private theorem decodeCell24 (a : Array U64 25#usize) (rc : U64) :
    (decode (plain a rc))[24]! = (round (decode a) rc.bv)[24]! := by
  rw [decodedAt _ _ (by decide), roundAt _ _ _ (by decide)]
  change _ = (rhoPi (decode a) 24 ^^^ ((~~~(rhoPi (decode a) 20)) &&& (rhoPi (decode a) 21)))
  rw [← rho24, ← rho20, ← rho21]
  unfold KorientedRust.shake256.oriented.OFF
  have h := chi24 ((before a).val[24]!.bv) ((before a).val[20]!.bv) ((before a).val[21]!.bv)
  exact h

theorem round_fips (a : Array U64 25#usize) (rc : U64) :
    KorientedRust.shake256.oriented.round a rc ⦃ out => decode out = round (decode a) rc.bv ⦄ := by
  rw [round_plain]
  simp only [WP.spec_ok]
  apply ext25
  · simp [decode]
  · simp only [round, Id.run, pure, _root_.Array.size_ofFn]
  · intro i hi
    interval_cases i
    · exact decodeCell0 a rc
    · exact decodeCell1 a rc
    · exact decodeCell2 a rc
    · exact decodeCell3 a rc
    · exact decodeCell4 a rc
    · exact decodeCell5 a rc
    · exact decodeCell6 a rc
    · exact decodeCell7 a rc
    · exact decodeCell8 a rc
    · exact decodeCell9 a rc
    · exact decodeCell10 a rc
    · exact decodeCell11 a rc
    · exact decodeCell12 a rc
    · exact decodeCell13 a rc
    · exact decodeCell14 a rc
    · exact decodeCell15 a rc
    · exact decodeCell16 a rc
    · exact decodeCell17 a rc
    · exact decodeCell18 a rc
    · exact decodeCell19 a rc
    · exact decodeCell20 a rc
    · exact decodeCell21 a rc
    · exact decodeCell22 a rc
    · exact decodeCell23 a rc
    · exact decodeCell24 a rc
end slhdsa.Oriented
