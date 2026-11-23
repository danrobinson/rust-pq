import Kmixed.Funs
import Ksha3.Rows
open Aeneas Aeneas.Std Result
namespace slhdsa.Kmixed
abbrev V := KmixedRust.shake256.parallel.mixed.V
instance : Inhabited V := ⟨⟨fun _ => 0,0#u64⟩⟩
abbrev Rows := Array V 25#usize
def writeRows (a : Rows) (rc : U64) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 : V) := Id.run do
  let a1 := a.set 0#usize v0
  let a2 := a1.set 1#usize v1
  let a3 := a2.set 2#usize v2
  let a4 := a3.set 3#usize v3
  let a5 := a4.set 4#usize v4
  let a6 := a5.set 5#usize v5
  let a7 := a6.set 6#usize v6
  let a8 := a7.set 7#usize v7
  let a9 := a8.set 8#usize v8
  let a10 := a9.set 9#usize v9
  let a11 := a10.set 10#usize v10
  let a12 := a11.set 11#usize v11
  let a13 := a12.set 12#usize v12
  let a14 := a13.set 13#usize v13
  let a15 := a14.set 14#usize v14
  let a16 := a15.set 15#usize v15
  let a17 := a16.set 16#usize v16
  let a18 := a17.set 17#usize v17
  let a19 := a18.set 18#usize v18
  let a20 := a19.set 19#usize v19
  let a21 := a20.set 20#usize v20
  let a22 := a21.set 21#usize v21
  let a23 := a22.set 22#usize v22
  let a24 := a23.set 23#usize v23
  let a25 := a24.set 24#usize v24
  let w := a25.val[0]!
  return a25.set 0#usize ⟨fun j => w.pair j ^^^ rc.bv,w.scalar ^^^ rc⟩

def pureRound (a : Rows) (rc : U64) := Id.run do
  let uxt : Ksha3.Reg := fun j => (a.val[15]!).pair j ^^^ (a.val[20]!).pair j
  let uxt1 : Ksha3.Reg := fun j => (a.val[10]!).pair j ^^^ uxt j
  let i : U64 := ((a.val[10]!).scalar ^^^ (a.val[15]!).scalar)
  let i1 : U64 := (i ^^^ (a.val[20]!).scalar)
  let uxt2 : Ksha3.Reg := fun j => (a.val[5]!).pair j ^^^ uxt1 j
  let uxt3 : Ksha3.Reg := fun j => (a.val[0]!).pair j ^^^ uxt2 j
  let i2 : U64 := ((a.val[0]!).scalar ^^^ (a.val[5]!).scalar)
  let i3 : U64 := (i2 ^^^ i1)
  let uxt4 : Ksha3.Reg := fun j => (a.val[16]!).pair j ^^^ (a.val[21]!).pair j
  let uxt5 : Ksha3.Reg := fun j => (a.val[11]!).pair j ^^^ uxt4 j
  let i4 : U64 := ((a.val[11]!).scalar ^^^ (a.val[16]!).scalar)
  let i5 : U64 := (i4 ^^^ (a.val[21]!).scalar)
  let uxt6 : Ksha3.Reg := fun j => (a.val[6]!).pair j ^^^ uxt5 j
  let uxt7 : Ksha3.Reg := fun j => (a.val[1]!).pair j ^^^ uxt6 j
  let i6 : U64 := ((a.val[1]!).scalar ^^^ (a.val[6]!).scalar)
  let i7 : U64 := (i6 ^^^ i5)
  let uxt8 : Ksha3.Reg := fun j => (a.val[17]!).pair j ^^^ (a.val[22]!).pair j
  let uxt9 : Ksha3.Reg := fun j => (a.val[12]!).pair j ^^^ uxt8 j
  let i8 : U64 := ((a.val[12]!).scalar ^^^ (a.val[17]!).scalar)
  let i9 : U64 := (i8 ^^^ (a.val[22]!).scalar)
  let uxt10 : Ksha3.Reg := fun j => (a.val[7]!).pair j ^^^ uxt9 j
  let uxt11 : Ksha3.Reg := fun j => (a.val[2]!).pair j ^^^ uxt10 j
  let i10 : U64 := ((a.val[2]!).scalar ^^^ (a.val[7]!).scalar)
  let i11 : U64 := (i10 ^^^ i9)
  let uxt12 : Ksha3.Reg := fun j => (a.val[18]!).pair j ^^^ (a.val[23]!).pair j
  let uxt13 : Ksha3.Reg := fun j => (a.val[13]!).pair j ^^^ uxt12 j
  let i12 : U64 := ((a.val[13]!).scalar ^^^ (a.val[18]!).scalar)
  let i13 : U64 := (i12 ^^^ (a.val[23]!).scalar)
  let uxt14 : Ksha3.Reg := fun j => (a.val[8]!).pair j ^^^ uxt13 j
  let uxt15 : Ksha3.Reg := fun j => (a.val[3]!).pair j ^^^ uxt14 j
  let i14 : U64 := ((a.val[3]!).scalar ^^^ (a.val[8]!).scalar)
  let i15 : U64 := (i14 ^^^ i13)
  let uxt16 : Ksha3.Reg := fun j => (a.val[19]!).pair j ^^^ (a.val[24]!).pair j
  let uxt17 : Ksha3.Reg := fun j => (a.val[14]!).pair j ^^^ uxt16 j
  let i16 : U64 := ((a.val[14]!).scalar ^^^ (a.val[19]!).scalar)
  let i17 : U64 := (i16 ^^^ (a.val[24]!).scalar)
  let uxt18 : Ksha3.Reg := fun j => (a.val[9]!).pair j ^^^ uxt17 j
  let uxt19 : Ksha3.Reg := fun j => (a.val[4]!).pair j ^^^ uxt18 j
  let i18 : U64 := ((a.val[4]!).scalar ^^^ (a.val[9]!).scalar)
  let i19 : U64 := (i18 ^^^ i17)
  let uxt20 : Ksha3.Reg := fun j => ((⟨uxt7,i7⟩ : V)).pair j <<< 1
  let uxt21 : Ksha3.Reg := fun j => ((uxt20 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((((⟨uxt7,i7⟩ : V)).pair j) >>> 63)
  let uxt22 : Ksha3.Reg := fun j => ((⟨uxt19,i19⟩ : V)).pair j ^^^ uxt21 j
  let i20 : U64 := (core.num.U64.rotate_left ((⟨uxt7,i7⟩ : V)).scalar 1#u32)
  let i21 : U64 := (((⟨uxt19,i19⟩ : V)).scalar ^^^ i20)
  let uxt23 : Ksha3.Reg := fun j => ((⟨uxt11,i11⟩ : V)).pair j <<< 1
  let uxt24 : Ksha3.Reg := fun j => ((uxt23 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((((⟨uxt11,i11⟩ : V)).pair j) >>> 63)
  let uxt25 : Ksha3.Reg := fun j => ((⟨uxt3,i3⟩ : V)).pair j ^^^ uxt24 j
  let i22 : U64 := (core.num.U64.rotate_left ((⟨uxt11,i11⟩ : V)).scalar 1#u32)
  let i23 : U64 := (((⟨uxt3,i3⟩ : V)).scalar ^^^ i22)
  let uxt26 : Ksha3.Reg := fun j => ((⟨uxt15,i15⟩ : V)).pair j <<< 1
  let uxt27 : Ksha3.Reg := fun j => ((uxt26 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((((⟨uxt15,i15⟩ : V)).pair j) >>> 63)
  let uxt28 : Ksha3.Reg := fun j => ((⟨uxt7,i7⟩ : V)).pair j ^^^ uxt27 j
  let i24 : U64 := (core.num.U64.rotate_left ((⟨uxt15,i15⟩ : V)).scalar 1#u32)
  let i25 : U64 := (((⟨uxt7,i7⟩ : V)).scalar ^^^ i24)
  let uxt29 : Ksha3.Reg := fun j => ((⟨uxt19,i19⟩ : V)).pair j <<< 1
  let uxt30 : Ksha3.Reg := fun j => ((uxt29 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((((⟨uxt19,i19⟩ : V)).pair j) >>> 63)
  let uxt31 : Ksha3.Reg := fun j => ((⟨uxt11,i11⟩ : V)).pair j ^^^ uxt30 j
  let i26 : U64 := (core.num.U64.rotate_left ((⟨uxt19,i19⟩ : V)).scalar 1#u32)
  let i27 : U64 := (((⟨uxt11,i11⟩ : V)).scalar ^^^ i26)
  let uxt32 : Ksha3.Reg := fun j => ((⟨uxt3,i3⟩ : V)).pair j <<< 1
  let uxt33 : Ksha3.Reg := fun j => ((uxt32 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((((⟨uxt3,i3⟩ : V)).pair j) >>> 63)
  let uxt34 : Ksha3.Reg := fun j => ((⟨uxt15,i15⟩ : V)).pair j ^^^ uxt33 j
  let i28 : U64 := (core.num.U64.rotate_left ((⟨uxt3,i3⟩ : V)).scalar 1#u32)
  let i29 : U64 := (((⟨uxt15,i15⟩ : V)).scalar ^^^ i28)
  let x : Ksha3.Reg := fun j => (a.val[0]!).pair j ^^^ ((⟨uxt22,i21⟩ : V)).pair j
  let uxt35 : Ksha3.Reg := fun j => x j <<< 0
  let uxt36 : Ksha3.Reg := fun j => ((uxt35 j) &&& (BitVec.allOnes 64 <<< 0)) ||| ((x j) >>> 64)
  let i30 : U64 := ((a.val[0]!).scalar ^^^ ((⟨uxt22,i21⟩ : V)).scalar)
  let i31 : U64 := (core.num.U64.rotate_left i30 0#u32)
  let x1 : Ksha3.Reg := fun j => (a.val[6]!).pair j ^^^ ((⟨uxt25,i23⟩ : V)).pair j
  let uxt37 : Ksha3.Reg := fun j => x1 j <<< 44
  let uxt38 : Ksha3.Reg := fun j => ((uxt37 j) &&& (BitVec.allOnes 64 <<< 44)) ||| ((x1 j) >>> 20)
  let i32 : U64 := ((a.val[6]!).scalar ^^^ ((⟨uxt25,i23⟩ : V)).scalar)
  let i33 : U64 := (core.num.U64.rotate_left i32 44#u32)
  let x2 : Ksha3.Reg := fun j => (a.val[12]!).pair j ^^^ ((⟨uxt28,i25⟩ : V)).pair j
  let uxt39 : Ksha3.Reg := fun j => x2 j <<< 43
  let uxt40 : Ksha3.Reg := fun j => ((uxt39 j) &&& (BitVec.allOnes 64 <<< 43)) ||| ((x2 j) >>> 21)
  let i34 : U64 := ((a.val[12]!).scalar ^^^ ((⟨uxt28,i25⟩ : V)).scalar)
  let i35 : U64 := (core.num.U64.rotate_left i34 43#u32)
  let x3 : Ksha3.Reg := fun j => (a.val[18]!).pair j ^^^ ((⟨uxt31,i27⟩ : V)).pair j
  let uxt41 : Ksha3.Reg := fun j => x3 j <<< 21
  let uxt42 : Ksha3.Reg := fun j => ((uxt41 j) &&& (BitVec.allOnes 64 <<< 21)) ||| ((x3 j) >>> 43)
  let i36 : U64 := ((a.val[18]!).scalar ^^^ ((⟨uxt31,i27⟩ : V)).scalar)
  let i37 : U64 := (core.num.U64.rotate_left i36 21#u32)
  let x4 : Ksha3.Reg := fun j => (a.val[24]!).pair j ^^^ ((⟨uxt34,i29⟩ : V)).pair j
  let uxt43 : Ksha3.Reg := fun j => x4 j <<< 14
  let uxt44 : Ksha3.Reg := fun j => ((uxt43 j) &&& (BitVec.allOnes 64 <<< 14)) ||| ((x4 j) >>> 50)
  let i38 : U64 := ((a.val[24]!).scalar ^^^ ((⟨uxt34,i29⟩ : V)).scalar)
  let i39 : U64 := (core.num.U64.rotate_left i38 14#u32)
  let x5 : Ksha3.Reg := fun j => (a.val[3]!).pair j ^^^ ((⟨uxt31,i27⟩ : V)).pair j
  let uxt45 : Ksha3.Reg := fun j => x5 j <<< 28
  let uxt46 : Ksha3.Reg := fun j => ((uxt45 j) &&& (BitVec.allOnes 64 <<< 28)) ||| ((x5 j) >>> 36)
  let i40 : U64 := ((a.val[3]!).scalar ^^^ ((⟨uxt31,i27⟩ : V)).scalar)
  let i41 : U64 := (core.num.U64.rotate_left i40 28#u32)
  let x6 : Ksha3.Reg := fun j => (a.val[9]!).pair j ^^^ ((⟨uxt34,i29⟩ : V)).pair j
  let uxt47 : Ksha3.Reg := fun j => x6 j <<< 20
  let uxt48 : Ksha3.Reg := fun j => ((uxt47 j) &&& (BitVec.allOnes 64 <<< 20)) ||| ((x6 j) >>> 44)
  let i42 : U64 := ((a.val[9]!).scalar ^^^ ((⟨uxt34,i29⟩ : V)).scalar)
  let i43 : U64 := (core.num.U64.rotate_left i42 20#u32)
  let x7 : Ksha3.Reg := fun j => (a.val[10]!).pair j ^^^ ((⟨uxt22,i21⟩ : V)).pair j
  let uxt49 : Ksha3.Reg := fun j => x7 j <<< 3
  let uxt50 : Ksha3.Reg := fun j => ((uxt49 j) &&& (BitVec.allOnes 64 <<< 3)) ||| ((x7 j) >>> 61)
  let i44 : U64 := ((a.val[10]!).scalar ^^^ ((⟨uxt22,i21⟩ : V)).scalar)
  let i45 : U64 := (core.num.U64.rotate_left i44 3#u32)
  let x8 : Ksha3.Reg := fun j => (a.val[16]!).pair j ^^^ ((⟨uxt25,i23⟩ : V)).pair j
  let uxt51 : Ksha3.Reg := fun j => x8 j <<< 45
  let uxt52 : Ksha3.Reg := fun j => ((uxt51 j) &&& (BitVec.allOnes 64 <<< 45)) ||| ((x8 j) >>> 19)
  let i46 : U64 := ((a.val[16]!).scalar ^^^ ((⟨uxt25,i23⟩ : V)).scalar)
  let i47 : U64 := (core.num.U64.rotate_left i46 45#u32)
  let x9 : Ksha3.Reg := fun j => (a.val[22]!).pair j ^^^ ((⟨uxt28,i25⟩ : V)).pair j
  let uxt53 : Ksha3.Reg := fun j => x9 j <<< 61
  let uxt54 : Ksha3.Reg := fun j => ((uxt53 j) &&& (BitVec.allOnes 64 <<< 61)) ||| ((x9 j) >>> 3)
  let i48 : U64 := ((a.val[22]!).scalar ^^^ ((⟨uxt28,i25⟩ : V)).scalar)
  let i49 : U64 := (core.num.U64.rotate_left i48 61#u32)
  let x10 : Ksha3.Reg := fun j => (a.val[1]!).pair j ^^^ ((⟨uxt25,i23⟩ : V)).pair j
  let uxt55 : Ksha3.Reg := fun j => x10 j <<< 1
  let uxt56 : Ksha3.Reg := fun j => ((uxt55 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((x10 j) >>> 63)
  let i50 : U64 := ((a.val[1]!).scalar ^^^ ((⟨uxt25,i23⟩ : V)).scalar)
  let i51 : U64 := (core.num.U64.rotate_left i50 1#u32)
  let x11 : Ksha3.Reg := fun j => (a.val[7]!).pair j ^^^ ((⟨uxt28,i25⟩ : V)).pair j
  let uxt57 : Ksha3.Reg := fun j => x11 j <<< 6
  let uxt58 : Ksha3.Reg := fun j => ((uxt57 j) &&& (BitVec.allOnes 64 <<< 6)) ||| ((x11 j) >>> 58)
  let i52 : U64 := ((a.val[7]!).scalar ^^^ ((⟨uxt28,i25⟩ : V)).scalar)
  let i53 : U64 := (core.num.U64.rotate_left i52 6#u32)
  let x12 : Ksha3.Reg := fun j => (a.val[13]!).pair j ^^^ ((⟨uxt31,i27⟩ : V)).pair j
  let uxt59 : Ksha3.Reg := fun j => x12 j <<< 25
  let uxt60 : Ksha3.Reg := fun j => ((uxt59 j) &&& (BitVec.allOnes 64 <<< 25)) ||| ((x12 j) >>> 39)
  let i54 : U64 := ((a.val[13]!).scalar ^^^ ((⟨uxt31,i27⟩ : V)).scalar)
  let i55 : U64 := (core.num.U64.rotate_left i54 25#u32)
  let x13 : Ksha3.Reg := fun j => (a.val[19]!).pair j ^^^ ((⟨uxt34,i29⟩ : V)).pair j
  let uxt61 : Ksha3.Reg := fun j => x13 j <<< 8
  let uxt62 : Ksha3.Reg := fun j => ((uxt61 j) &&& (BitVec.allOnes 64 <<< 8)) ||| ((x13 j) >>> 56)
  let i56 : U64 := ((a.val[19]!).scalar ^^^ ((⟨uxt34,i29⟩ : V)).scalar)
  let i57 : U64 := (core.num.U64.rotate_left i56 8#u32)
  let x14 : Ksha3.Reg := fun j => (a.val[20]!).pair j ^^^ ((⟨uxt22,i21⟩ : V)).pair j
  let uxt63 : Ksha3.Reg := fun j => x14 j <<< 18
  let uxt64 : Ksha3.Reg := fun j => ((uxt63 j) &&& (BitVec.allOnes 64 <<< 18)) ||| ((x14 j) >>> 46)
  let i58 : U64 := ((a.val[20]!).scalar ^^^ ((⟨uxt22,i21⟩ : V)).scalar)
  let i59 : U64 := (core.num.U64.rotate_left i58 18#u32)
  let x15 : Ksha3.Reg := fun j => (a.val[4]!).pair j ^^^ ((⟨uxt34,i29⟩ : V)).pair j
  let uxt65 : Ksha3.Reg := fun j => x15 j <<< 27
  let uxt66 : Ksha3.Reg := fun j => ((uxt65 j) &&& (BitVec.allOnes 64 <<< 27)) ||| ((x15 j) >>> 37)
  let i60 : U64 := ((a.val[4]!).scalar ^^^ ((⟨uxt34,i29⟩ : V)).scalar)
  let i61 : U64 := (core.num.U64.rotate_left i60 27#u32)
  let x16 : Ksha3.Reg := fun j => (a.val[5]!).pair j ^^^ ((⟨uxt22,i21⟩ : V)).pair j
  let uxt67 : Ksha3.Reg := fun j => x16 j <<< 36
  let uxt68 : Ksha3.Reg := fun j => ((uxt67 j) &&& (BitVec.allOnes 64 <<< 36)) ||| ((x16 j) >>> 28)
  let i62 : U64 := ((a.val[5]!).scalar ^^^ ((⟨uxt22,i21⟩ : V)).scalar)
  let i63 : U64 := (core.num.U64.rotate_left i62 36#u32)
  let x17 : Ksha3.Reg := fun j => (a.val[11]!).pair j ^^^ ((⟨uxt25,i23⟩ : V)).pair j
  let uxt69 : Ksha3.Reg := fun j => x17 j <<< 10
  let uxt70 : Ksha3.Reg := fun j => ((uxt69 j) &&& (BitVec.allOnes 64 <<< 10)) ||| ((x17 j) >>> 54)
  let i64 : U64 := ((a.val[11]!).scalar ^^^ ((⟨uxt25,i23⟩ : V)).scalar)
  let i65 : U64 := (core.num.U64.rotate_left i64 10#u32)
  let x18 : Ksha3.Reg := fun j => (a.val[17]!).pair j ^^^ ((⟨uxt28,i25⟩ : V)).pair j
  let uxt71 : Ksha3.Reg := fun j => x18 j <<< 15
  let uxt72 : Ksha3.Reg := fun j => ((uxt71 j) &&& (BitVec.allOnes 64 <<< 15)) ||| ((x18 j) >>> 49)
  let i66 : U64 := ((a.val[17]!).scalar ^^^ ((⟨uxt28,i25⟩ : V)).scalar)
  let i67 : U64 := (core.num.U64.rotate_left i66 15#u32)
  let x19 : Ksha3.Reg := fun j => (a.val[23]!).pair j ^^^ ((⟨uxt31,i27⟩ : V)).pair j
  let uxt73 : Ksha3.Reg := fun j => x19 j <<< 56
  let uxt74 : Ksha3.Reg := fun j => ((uxt73 j) &&& (BitVec.allOnes 64 <<< 56)) ||| ((x19 j) >>> 8)
  let i68 : U64 := ((a.val[23]!).scalar ^^^ ((⟨uxt31,i27⟩ : V)).scalar)
  let i69 : U64 := (core.num.U64.rotate_left i68 56#u32)
  let x20 : Ksha3.Reg := fun j => (a.val[2]!).pair j ^^^ ((⟨uxt28,i25⟩ : V)).pair j
  let uxt75 : Ksha3.Reg := fun j => x20 j <<< 62
  let uxt76 : Ksha3.Reg := fun j => ((uxt75 j) &&& (BitVec.allOnes 64 <<< 62)) ||| ((x20 j) >>> 2)
  let i70 : U64 := ((a.val[2]!).scalar ^^^ ((⟨uxt28,i25⟩ : V)).scalar)
  let i71 : U64 := (core.num.U64.rotate_left i70 62#u32)
  let x21 : Ksha3.Reg := fun j => (a.val[8]!).pair j ^^^ ((⟨uxt31,i27⟩ : V)).pair j
  let uxt77 : Ksha3.Reg := fun j => x21 j <<< 55
  let uxt78 : Ksha3.Reg := fun j => ((uxt77 j) &&& (BitVec.allOnes 64 <<< 55)) ||| ((x21 j) >>> 9)
  let i72 : U64 := ((a.val[8]!).scalar ^^^ ((⟨uxt31,i27⟩ : V)).scalar)
  let i73 : U64 := (core.num.U64.rotate_left i72 55#u32)
  let x22 : Ksha3.Reg := fun j => (a.val[14]!).pair j ^^^ ((⟨uxt34,i29⟩ : V)).pair j
  let uxt79 : Ksha3.Reg := fun j => x22 j <<< 39
  let uxt80 : Ksha3.Reg := fun j => ((uxt79 j) &&& (BitVec.allOnes 64 <<< 39)) ||| ((x22 j) >>> 25)
  let i74 : U64 := ((a.val[14]!).scalar ^^^ ((⟨uxt34,i29⟩ : V)).scalar)
  let i75 : U64 := (core.num.U64.rotate_left i74 39#u32)
  let x23 : Ksha3.Reg := fun j => (a.val[15]!).pair j ^^^ ((⟨uxt22,i21⟩ : V)).pair j
  let uxt81 : Ksha3.Reg := fun j => x23 j <<< 41
  let uxt82 : Ksha3.Reg := fun j => ((uxt81 j) &&& (BitVec.allOnes 64 <<< 41)) ||| ((x23 j) >>> 23)
  let i76 : U64 := ((a.val[15]!).scalar ^^^ ((⟨uxt22,i21⟩ : V)).scalar)
  let i77 : U64 := (core.num.U64.rotate_left i76 41#u32)
  let x24 : Ksha3.Reg := fun j => (a.val[21]!).pair j ^^^ ((⟨uxt25,i23⟩ : V)).pair j
  let uxt83 : Ksha3.Reg := fun j => x24 j <<< 2
  let uxt84 : Ksha3.Reg := fun j => ((uxt83 j) &&& (BitVec.allOnes 64 <<< 2)) ||| ((x24 j) >>> 62)
  let i78 : U64 := ((a.val[21]!).scalar ^^^ ((⟨uxt25,i23⟩ : V)).scalar)
  let i79 : U64 := (core.num.U64.rotate_left i78 2#u32)
  let uxt85 : Ksha3.Reg := fun j => ((⟨uxt40,i35⟩ : V)).pair j &&& ~~~(((⟨uxt38,i33⟩ : V)).pair j)
  let uxt86 : Ksha3.Reg := fun j => ((⟨uxt36,i31⟩ : V)).pair j ^^^ uxt85 j
  let i82 : U64 := (~~~ ((⟨uxt38,i33⟩ : V)).scalar)
  let i83 : U64 := (i82 &&& ((⟨uxt40,i35⟩ : V)).scalar)
  let i84 : U64 := (((⟨uxt36,i31⟩ : V)).scalar ^^^ i83)
  let uxt87 : Ksha3.Reg := fun j => ((⟨uxt42,i37⟩ : V)).pair j &&& ~~~(((⟨uxt40,i35⟩ : V)).pair j)
  let uxt88 : Ksha3.Reg := fun j => ((⟨uxt38,i33⟩ : V)).pair j ^^^ uxt87 j
  let i86 : U64 := (~~~ ((⟨uxt40,i35⟩ : V)).scalar)
  let i87 : U64 := (i86 &&& ((⟨uxt42,i37⟩ : V)).scalar)
  let i88 : U64 := (((⟨uxt38,i33⟩ : V)).scalar ^^^ i87)
  let uxt89 : Ksha3.Reg := fun j => ((⟨uxt44,i39⟩ : V)).pair j &&& ~~~(((⟨uxt42,i37⟩ : V)).pair j)
  let uxt90 : Ksha3.Reg := fun j => ((⟨uxt40,i35⟩ : V)).pair j ^^^ uxt89 j
  let i90 : U64 := (~~~ ((⟨uxt42,i37⟩ : V)).scalar)
  let i91 : U64 := (i90 &&& ((⟨uxt44,i39⟩ : V)).scalar)
  let i92 : U64 := (((⟨uxt40,i35⟩ : V)).scalar ^^^ i91)
  let uxt91 : Ksha3.Reg := fun j => ((⟨uxt36,i31⟩ : V)).pair j &&& ~~~(((⟨uxt44,i39⟩ : V)).pair j)
  let uxt92 : Ksha3.Reg := fun j => ((⟨uxt42,i37⟩ : V)).pair j ^^^ uxt91 j
  let i93 : U64 := (~~~ ((⟨uxt44,i39⟩ : V)).scalar)
  let i94 : U64 := (i93 &&& ((⟨uxt36,i31⟩ : V)).scalar)
  let i95 : U64 := (((⟨uxt42,i37⟩ : V)).scalar ^^^ i94)
  let uxt93 : Ksha3.Reg := fun j => ((⟨uxt38,i33⟩ : V)).pair j &&& ~~~(((⟨uxt36,i31⟩ : V)).pair j)
  let uxt94 : Ksha3.Reg := fun j => ((⟨uxt44,i39⟩ : V)).pair j ^^^ uxt93 j
  let i96 : U64 := (~~~ ((⟨uxt36,i31⟩ : V)).scalar)
  let i97 : U64 := (i96 &&& ((⟨uxt38,i33⟩ : V)).scalar)
  let i98 : U64 := (((⟨uxt44,i39⟩ : V)).scalar ^^^ i97)
  let uxt95 : Ksha3.Reg := fun j => ((⟨uxt50,i45⟩ : V)).pair j &&& ~~~(((⟨uxt48,i43⟩ : V)).pair j)
  let uxt96 : Ksha3.Reg := fun j => ((⟨uxt46,i41⟩ : V)).pair j ^^^ uxt95 j
  let i101 : U64 := (~~~ ((⟨uxt48,i43⟩ : V)).scalar)
  let i102 : U64 := (i101 &&& ((⟨uxt50,i45⟩ : V)).scalar)
  let i103 : U64 := (((⟨uxt46,i41⟩ : V)).scalar ^^^ i102)
  let uxt97 : Ksha3.Reg := fun j => ((⟨uxt52,i47⟩ : V)).pair j &&& ~~~(((⟨uxt50,i45⟩ : V)).pair j)
  let uxt98 : Ksha3.Reg := fun j => ((⟨uxt48,i43⟩ : V)).pair j ^^^ uxt97 j
  let i105 : U64 := (~~~ ((⟨uxt50,i45⟩ : V)).scalar)
  let i106 : U64 := (i105 &&& ((⟨uxt52,i47⟩ : V)).scalar)
  let i107 : U64 := (((⟨uxt48,i43⟩ : V)).scalar ^^^ i106)
  let uxt99 : Ksha3.Reg := fun j => ((⟨uxt54,i49⟩ : V)).pair j &&& ~~~(((⟨uxt52,i47⟩ : V)).pair j)
  let uxt100 : Ksha3.Reg := fun j => ((⟨uxt50,i45⟩ : V)).pair j ^^^ uxt99 j
  let i109 : U64 := (~~~ ((⟨uxt52,i47⟩ : V)).scalar)
  let i110 : U64 := (i109 &&& ((⟨uxt54,i49⟩ : V)).scalar)
  let i111 : U64 := (((⟨uxt50,i45⟩ : V)).scalar ^^^ i110)
  let uxt101 : Ksha3.Reg := fun j => ((⟨uxt46,i41⟩ : V)).pair j &&& ~~~(((⟨uxt54,i49⟩ : V)).pair j)
  let uxt102 : Ksha3.Reg := fun j => ((⟨uxt52,i47⟩ : V)).pair j ^^^ uxt101 j
  let i112 : U64 := (~~~ ((⟨uxt54,i49⟩ : V)).scalar)
  let i113 : U64 := (i112 &&& ((⟨uxt46,i41⟩ : V)).scalar)
  let i114 : U64 := (((⟨uxt52,i47⟩ : V)).scalar ^^^ i113)
  let uxt103 : Ksha3.Reg := fun j => ((⟨uxt48,i43⟩ : V)).pair j &&& ~~~(((⟨uxt46,i41⟩ : V)).pair j)
  let uxt104 : Ksha3.Reg := fun j => ((⟨uxt54,i49⟩ : V)).pair j ^^^ uxt103 j
  let i115 : U64 := (~~~ ((⟨uxt46,i41⟩ : V)).scalar)
  let i116 : U64 := (i115 &&& ((⟨uxt48,i43⟩ : V)).scalar)
  let i117 : U64 := (((⟨uxt54,i49⟩ : V)).scalar ^^^ i116)
  let uxt105 : Ksha3.Reg := fun j => ((⟨uxt60,i55⟩ : V)).pair j &&& ~~~(((⟨uxt58,i53⟩ : V)).pair j)
  let uxt106 : Ksha3.Reg := fun j => ((⟨uxt56,i51⟩ : V)).pair j ^^^ uxt105 j
  let i120 : U64 := (~~~ ((⟨uxt58,i53⟩ : V)).scalar)
  let i121 : U64 := (i120 &&& ((⟨uxt60,i55⟩ : V)).scalar)
  let i122 : U64 := (((⟨uxt56,i51⟩ : V)).scalar ^^^ i121)
  let uxt107 : Ksha3.Reg := fun j => ((⟨uxt62,i57⟩ : V)).pair j &&& ~~~(((⟨uxt60,i55⟩ : V)).pair j)
  let uxt108 : Ksha3.Reg := fun j => ((⟨uxt58,i53⟩ : V)).pair j ^^^ uxt107 j
  let i124 : U64 := (~~~ ((⟨uxt60,i55⟩ : V)).scalar)
  let i125 : U64 := (i124 &&& ((⟨uxt62,i57⟩ : V)).scalar)
  let i126 : U64 := (((⟨uxt58,i53⟩ : V)).scalar ^^^ i125)
  let uxt109 : Ksha3.Reg := fun j => ((⟨uxt64,i59⟩ : V)).pair j &&& ~~~(((⟨uxt62,i57⟩ : V)).pair j)
  let uxt110 : Ksha3.Reg := fun j => ((⟨uxt60,i55⟩ : V)).pair j ^^^ uxt109 j
  let i128 : U64 := (~~~ ((⟨uxt62,i57⟩ : V)).scalar)
  let i129 : U64 := (i128 &&& ((⟨uxt64,i59⟩ : V)).scalar)
  let i130 : U64 := (((⟨uxt60,i55⟩ : V)).scalar ^^^ i129)
  let uxt111 : Ksha3.Reg := fun j => ((⟨uxt56,i51⟩ : V)).pair j &&& ~~~(((⟨uxt64,i59⟩ : V)).pair j)
  let uxt112 : Ksha3.Reg := fun j => ((⟨uxt62,i57⟩ : V)).pair j ^^^ uxt111 j
  let i131 : U64 := (~~~ ((⟨uxt64,i59⟩ : V)).scalar)
  let i132 : U64 := (i131 &&& ((⟨uxt56,i51⟩ : V)).scalar)
  let i133 : U64 := (((⟨uxt62,i57⟩ : V)).scalar ^^^ i132)
  let uxt113 : Ksha3.Reg := fun j => ((⟨uxt58,i53⟩ : V)).pair j &&& ~~~(((⟨uxt56,i51⟩ : V)).pair j)
  let uxt114 : Ksha3.Reg := fun j => ((⟨uxt64,i59⟩ : V)).pair j ^^^ uxt113 j
  let i134 : U64 := (~~~ ((⟨uxt56,i51⟩ : V)).scalar)
  let i135 : U64 := (i134 &&& ((⟨uxt58,i53⟩ : V)).scalar)
  let i136 : U64 := (((⟨uxt64,i59⟩ : V)).scalar ^^^ i135)
  let uxt115 : Ksha3.Reg := fun j => ((⟨uxt70,i65⟩ : V)).pair j &&& ~~~(((⟨uxt68,i63⟩ : V)).pair j)
  let uxt116 : Ksha3.Reg := fun j => ((⟨uxt66,i61⟩ : V)).pair j ^^^ uxt115 j
  let i139 : U64 := (~~~ ((⟨uxt68,i63⟩ : V)).scalar)
  let i140 : U64 := (i139 &&& ((⟨uxt70,i65⟩ : V)).scalar)
  let i141 : U64 := (((⟨uxt66,i61⟩ : V)).scalar ^^^ i140)
  let uxt117 : Ksha3.Reg := fun j => ((⟨uxt72,i67⟩ : V)).pair j &&& ~~~(((⟨uxt70,i65⟩ : V)).pair j)
  let uxt118 : Ksha3.Reg := fun j => ((⟨uxt68,i63⟩ : V)).pair j ^^^ uxt117 j
  let i143 : U64 := (~~~ ((⟨uxt70,i65⟩ : V)).scalar)
  let i144 : U64 := (i143 &&& ((⟨uxt72,i67⟩ : V)).scalar)
  let i145 : U64 := (((⟨uxt68,i63⟩ : V)).scalar ^^^ i144)
  let uxt119 : Ksha3.Reg := fun j => ((⟨uxt74,i69⟩ : V)).pair j &&& ~~~(((⟨uxt72,i67⟩ : V)).pair j)
  let uxt120 : Ksha3.Reg := fun j => ((⟨uxt70,i65⟩ : V)).pair j ^^^ uxt119 j
  let i147 : U64 := (~~~ ((⟨uxt72,i67⟩ : V)).scalar)
  let i148 : U64 := (i147 &&& ((⟨uxt74,i69⟩ : V)).scalar)
  let i149 : U64 := (((⟨uxt70,i65⟩ : V)).scalar ^^^ i148)
  let uxt121 : Ksha3.Reg := fun j => ((⟨uxt66,i61⟩ : V)).pair j &&& ~~~(((⟨uxt74,i69⟩ : V)).pair j)
  let uxt122 : Ksha3.Reg := fun j => ((⟨uxt72,i67⟩ : V)).pair j ^^^ uxt121 j
  let i150 : U64 := (~~~ ((⟨uxt74,i69⟩ : V)).scalar)
  let i151 : U64 := (i150 &&& ((⟨uxt66,i61⟩ : V)).scalar)
  let i152 : U64 := (((⟨uxt72,i67⟩ : V)).scalar ^^^ i151)
  let uxt123 : Ksha3.Reg := fun j => ((⟨uxt68,i63⟩ : V)).pair j &&& ~~~(((⟨uxt66,i61⟩ : V)).pair j)
  let uxt124 : Ksha3.Reg := fun j => ((⟨uxt74,i69⟩ : V)).pair j ^^^ uxt123 j
  let i153 : U64 := (~~~ ((⟨uxt66,i61⟩ : V)).scalar)
  let i154 : U64 := (i153 &&& ((⟨uxt68,i63⟩ : V)).scalar)
  let i155 : U64 := (((⟨uxt74,i69⟩ : V)).scalar ^^^ i154)
  let uxt125 : Ksha3.Reg := fun j => ((⟨uxt80,i75⟩ : V)).pair j &&& ~~~(((⟨uxt78,i73⟩ : V)).pair j)
  let uxt126 : Ksha3.Reg := fun j => ((⟨uxt76,i71⟩ : V)).pair j ^^^ uxt125 j
  let i158 : U64 := (~~~ ((⟨uxt78,i73⟩ : V)).scalar)
  let i159 : U64 := (i158 &&& ((⟨uxt80,i75⟩ : V)).scalar)
  let i160 : U64 := (((⟨uxt76,i71⟩ : V)).scalar ^^^ i159)
  let uxt127 : Ksha3.Reg := fun j => ((⟨uxt82,i77⟩ : V)).pair j &&& ~~~(((⟨uxt80,i75⟩ : V)).pair j)
  let uxt128 : Ksha3.Reg := fun j => ((⟨uxt78,i73⟩ : V)).pair j ^^^ uxt127 j
  let i162 : U64 := (~~~ ((⟨uxt80,i75⟩ : V)).scalar)
  let i163 : U64 := (i162 &&& ((⟨uxt82,i77⟩ : V)).scalar)
  let i164 : U64 := (((⟨uxt78,i73⟩ : V)).scalar ^^^ i163)
  let uxt129 : Ksha3.Reg := fun j => ((⟨uxt84,i79⟩ : V)).pair j &&& ~~~(((⟨uxt82,i77⟩ : V)).pair j)
  let uxt130 : Ksha3.Reg := fun j => ((⟨uxt80,i75⟩ : V)).pair j ^^^ uxt129 j
  let i166 : U64 := (~~~ ((⟨uxt82,i77⟩ : V)).scalar)
  let i167 : U64 := (i166 &&& ((⟨uxt84,i79⟩ : V)).scalar)
  let i168 : U64 := (((⟨uxt80,i75⟩ : V)).scalar ^^^ i167)
  let uxt131 : Ksha3.Reg := fun j => ((⟨uxt76,i71⟩ : V)).pair j &&& ~~~(((⟨uxt84,i79⟩ : V)).pair j)
  let uxt132 : Ksha3.Reg := fun j => ((⟨uxt82,i77⟩ : V)).pair j ^^^ uxt131 j
  let i169 : U64 := (~~~ ((⟨uxt84,i79⟩ : V)).scalar)
  let i170 : U64 := (i169 &&& ((⟨uxt76,i71⟩ : V)).scalar)
  let i171 : U64 := (((⟨uxt82,i77⟩ : V)).scalar ^^^ i170)
  let uxt133 : Ksha3.Reg := fun j => ((⟨uxt78,i73⟩ : V)).pair j &&& ~~~(((⟨uxt76,i71⟩ : V)).pair j)
  let uxt134 : Ksha3.Reg := fun j => ((⟨uxt84,i79⟩ : V)).pair j ^^^ uxt133 j
  let i172 : U64 := (~~~ ((⟨uxt76,i71⟩ : V)).scalar)
  let i173 : U64 := (i172 &&& ((⟨uxt78,i73⟩ : V)).scalar)
  let i174 : U64 := (((⟨uxt84,i79⟩ : V)).scalar ^^^ i173)
  return writeRows a rc (⟨uxt86,i84⟩ : V) (⟨uxt88,i88⟩ : V) (⟨uxt90,i92⟩ : V) (⟨uxt92,i95⟩ : V) (⟨uxt94,i98⟩ : V) (⟨uxt96,i103⟩ : V) (⟨uxt98,i107⟩ : V) (⟨uxt100,i111⟩ : V) (⟨uxt102,i114⟩ : V) (⟨uxt104,i117⟩ : V) (⟨uxt106,i122⟩ : V) (⟨uxt108,i126⟩ : V) (⟨uxt110,i130⟩ : V) (⟨uxt112,i133⟩ : V) (⟨uxt114,i136⟩ : V) (⟨uxt116,i141⟩ : V) (⟨uxt118,i145⟩ : V) (⟨uxt120,i149⟩ : V) (⟨uxt122,i152⟩ : V) (⟨uxt124,i155⟩ : V) (⟨uxt126,i160⟩ : V) (⟨uxt128,i164⟩ : V) (⟨uxt130,i168⟩ : V) (⟨uxt132,i171⟩ : V) (⟨uxt134,i174⟩ : V)
end slhdsa.Kmixed
