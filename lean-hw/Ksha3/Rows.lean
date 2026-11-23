import Ksha3.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.Ksha3
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
abbrev Reg := Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t
abbrev Rows := Array Reg 25#usize
def writeRows (a : Rows) (rc : Reg) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 : Reg) : Rows := Id.run do
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
  let uxt167 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a25.val[0]!) j ^^^ (rc) j)
  let answer := a25.set 0#usize uxt167
  return answer

def pureRound (a : Array Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t 25#usize) (rc : U64) := Id.run do
  let uxt5 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[10]!) j ^^^ (a.val[15]!) j ^^^ (a.val[20]!) j)
  let uxt6 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[0]!) j ^^^ (a.val[5]!) j ^^^ (uxt5) j)
  let uxt12 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[11]!) j ^^^ (a.val[16]!) j ^^^ (a.val[21]!) j)
  let uxt13 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[1]!) j ^^^ (a.val[6]!) j ^^^ (uxt12) j)
  let uxt19 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[12]!) j ^^^ (a.val[17]!) j ^^^ (a.val[22]!) j)
  let uxt20 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[2]!) j ^^^ (a.val[7]!) j ^^^ (uxt19) j)
  let uxt26 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[13]!) j ^^^ (a.val[18]!) j ^^^ (a.val[23]!) j)
  let uxt27 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[3]!) j ^^^ (a.val[8]!) j ^^^ (uxt26) j)
  let uxt33 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[14]!) j ^^^ (a.val[19]!) j ^^^ (a.val[24]!) j)
  let uxt34 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (a.val[4]!) j ^^^ (a.val[9]!) j ^^^ (uxt33) j)
  let uxt37 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt34) j ^^^ ((uxt13) j).rotateLeft 1)
  let uxt40 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt6) j ^^^ ((uxt20) j).rotateLeft 1)
  let uxt42 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt13) j ^^^ ((uxt27) j).rotateLeft 1)
  let uxt43 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt20) j ^^^ ((uxt34) j).rotateLeft 1)
  let uxt44 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt27) j ^^^ ((uxt6) j).rotateLeft 1)
  let uxt46 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[0]!) j ^^^ (uxt37) j).rotateRight 0)
  let uxt48 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[6]!) j ^^^ (uxt40) j).rotateRight 20)
  let uxt50 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[12]!) j ^^^ (uxt42) j).rotateRight 21)
  let uxt52 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[18]!) j ^^^ (uxt43) j).rotateRight 43)
  let uxt54 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[24]!) j ^^^ (uxt44) j).rotateRight 50)
  let uxt55 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[3]!) j ^^^ (uxt43) j).rotateRight 36)
  let uxt56 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[9]!) j ^^^ (uxt44) j).rotateRight 44)
  let uxt57 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[10]!) j ^^^ (uxt37) j).rotateRight 61)
  let uxt58 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[16]!) j ^^^ (uxt40) j).rotateRight 19)
  let uxt59 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[22]!) j ^^^ (uxt42) j).rotateRight 3)
  let uxt60 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[1]!) j ^^^ (uxt40) j).rotateRight 63)
  let uxt61 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[7]!) j ^^^ (uxt42) j).rotateRight 58)
  let uxt62 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[13]!) j ^^^ (uxt43) j).rotateRight 39)
  let uxt63 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[19]!) j ^^^ (uxt44) j).rotateRight 56)
  let uxt64 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[20]!) j ^^^ (uxt37) j).rotateRight 46)
  let uxt65 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[4]!) j ^^^ (uxt44) j).rotateRight 37)
  let uxt66 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[5]!) j ^^^ (uxt37) j).rotateRight 28)
  let uxt67 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[11]!) j ^^^ (uxt40) j).rotateRight 54)
  let uxt68 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[17]!) j ^^^ (uxt42) j).rotateRight 49)
  let uxt69 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[23]!) j ^^^ (uxt43) j).rotateRight 8)
  let uxt70 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[2]!) j ^^^ (uxt42) j).rotateRight 2)
  let uxt71 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[8]!) j ^^^ (uxt43) j).rotateRight 9)
  let uxt72 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[14]!) j ^^^ (uxt44) j).rotateRight 25)
  let uxt73 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[15]!) j ^^^ (uxt37) j).rotateRight 23)
  let uxt74 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => ((a.val[21]!) j ^^^ (uxt40) j).rotateRight 62)
  let uxt78 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt46) j ^^^ ((uxt50) j &&& ~~~((uxt48) j)))
  let uxt82 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt48) j ^^^ ((uxt52) j &&& ~~~((uxt50) j)))
  let uxt86 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt50) j ^^^ ((uxt54) j &&& ~~~((uxt52) j)))
  let uxt89 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt52) j ^^^ ((uxt46) j &&& ~~~((uxt54) j)))
  let uxt92 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt54) j ^^^ ((uxt48) j &&& ~~~((uxt46) j)))
  let uxt96 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt55) j ^^^ ((uxt57) j &&& ~~~((uxt56) j)))
  let uxt100 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt56) j ^^^ ((uxt58) j &&& ~~~((uxt57) j)))
  let uxt104 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt57) j ^^^ ((uxt59) j &&& ~~~((uxt58) j)))
  let uxt107 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt58) j ^^^ ((uxt55) j &&& ~~~((uxt59) j)))
  let uxt110 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt59) j ^^^ ((uxt56) j &&& ~~~((uxt55) j)))
  let uxt114 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt60) j ^^^ ((uxt62) j &&& ~~~((uxt61) j)))
  let uxt118 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt61) j ^^^ ((uxt63) j &&& ~~~((uxt62) j)))
  let uxt122 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt62) j ^^^ ((uxt64) j &&& ~~~((uxt63) j)))
  let uxt125 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt63) j ^^^ ((uxt60) j &&& ~~~((uxt64) j)))
  let uxt128 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt64) j ^^^ ((uxt61) j &&& ~~~((uxt60) j)))
  let uxt132 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt65) j ^^^ ((uxt67) j &&& ~~~((uxt66) j)))
  let uxt136 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt66) j ^^^ ((uxt68) j &&& ~~~((uxt67) j)))
  let uxt140 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt67) j ^^^ ((uxt69) j &&& ~~~((uxt68) j)))
  let uxt143 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt68) j ^^^ ((uxt65) j &&& ~~~((uxt69) j)))
  let uxt146 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt69) j ^^^ ((uxt66) j &&& ~~~((uxt65) j)))
  let uxt150 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt70) j ^^^ ((uxt72) j &&& ~~~((uxt71) j)))
  let uxt154 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt71) j ^^^ ((uxt73) j &&& ~~~((uxt72) j)))
  let uxt158 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt72) j ^^^ ((uxt74) j &&& ~~~((uxt73) j)))
  let uxt161 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt73) j ^^^ ((uxt70) j &&& ~~~((uxt74) j)))
  let uxt164 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (uxt74) j ^^^ ((uxt71) j &&& ~~~((uxt70) j)))
  let uxt166 : Ksha3Rust.core.core_arch.arm_shared.neon.uint64x2_t := (fun j : Fin 2 => (rc).bv)
  return writeRows a uxt166 uxt78 uxt82 uxt86 uxt89 uxt92 uxt96 uxt100 uxt104 uxt107 uxt110 uxt114 uxt118 uxt122 uxt125 uxt128 uxt132 uxt136 uxt140 uxt143 uxt146 uxt150 uxt154 uxt158 uxt161 uxt164

end slhdsa.Ksha3
