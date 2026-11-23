import Kavx.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.Kavx
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
abbrev Reg := KavxRust.core.core_arch.x86.__m512i
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
  let mi197 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a25.val[0]!) j ^^^ (rc) j)
  let answer := a25.set 0#usize mi197
  return answer

def pureRound (a : Array KavxRust.core.core_arch.x86.__m512i 25#usize) (rc : U64) := Id.run do
  let mi5 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[10]!) j) ((a.val[15]!) j) ((a.val[20]!) j))
  let mi6 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[0]!) j) ((a.val[5]!) j) ((mi5) j))
  let mi12 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[11]!) j) ((a.val[16]!) j) ((a.val[21]!) j))
  let mi13 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[1]!) j) ((a.val[6]!) j) ((mi12) j))
  let mi19 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[12]!) j) ((a.val[17]!) j) ((a.val[22]!) j))
  let mi20 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[2]!) j) ((a.val[7]!) j) ((mi19) j))
  let mi26 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[13]!) j) ((a.val[18]!) j) ((a.val[23]!) j))
  let mi27 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[3]!) j) ((a.val[8]!) j) ((mi26) j))
  let mi33 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[14]!) j) ((a.val[19]!) j) ((a.val[24]!) j))
  let mi34 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 150 ((a.val[4]!) j) ((a.val[9]!) j) ((mi33) j))
  let mi37 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi13) j).rotateLeft 1)
  let mi38 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (mi34) j ^^^ (mi37) j)
  let mi41 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi20) j).rotateLeft 1)
  let mi42 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (mi6) j ^^^ (mi41) j)
  let mi44 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi27) j).rotateLeft 1)
  let mi45 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (mi13) j ^^^ (mi44) j)
  let mi46 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi34) j).rotateLeft 1)
  let mi47 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (mi20) j ^^^ (mi46) j)
  let mi48 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi6) j).rotateLeft 1)
  let mi49 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (mi27) j ^^^ (mi48) j)
  let mi51 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[0]!) j ^^^ (mi38) j)
  let mi52 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi51) j).rotateLeft 0)
  let mi54 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[6]!) j ^^^ (mi42) j)
  let mi55 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi54) j).rotateLeft 44)
  let mi57 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[12]!) j ^^^ (mi45) j)
  let mi58 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi57) j).rotateLeft 43)
  let mi60 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[18]!) j ^^^ (mi47) j)
  let mi61 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi60) j).rotateLeft 21)
  let mi63 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[24]!) j ^^^ (mi49) j)
  let mi64 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi63) j).rotateLeft 14)
  let mi65 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[3]!) j ^^^ (mi47) j)
  let mi66 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi65) j).rotateLeft 28)
  let mi67 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[9]!) j ^^^ (mi49) j)
  let mi68 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi67) j).rotateLeft 20)
  let mi69 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[10]!) j ^^^ (mi38) j)
  let mi70 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi69) j).rotateLeft 3)
  let mi71 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[16]!) j ^^^ (mi42) j)
  let mi72 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi71) j).rotateLeft 45)
  let mi73 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[22]!) j ^^^ (mi45) j)
  let mi74 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi73) j).rotateLeft 61)
  let mi75 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[1]!) j ^^^ (mi42) j)
  let mi76 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi75) j).rotateLeft 1)
  let mi77 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[7]!) j ^^^ (mi45) j)
  let mi78 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi77) j).rotateLeft 6)
  let mi79 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[13]!) j ^^^ (mi47) j)
  let mi80 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi79) j).rotateLeft 25)
  let mi81 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[19]!) j ^^^ (mi49) j)
  let mi82 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi81) j).rotateLeft 8)
  let mi83 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[20]!) j ^^^ (mi38) j)
  let mi84 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi83) j).rotateLeft 18)
  let mi85 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[4]!) j ^^^ (mi49) j)
  let mi86 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi85) j).rotateLeft 27)
  let mi87 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[5]!) j ^^^ (mi38) j)
  let mi88 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi87) j).rotateLeft 36)
  let mi89 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[11]!) j ^^^ (mi42) j)
  let mi90 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi89) j).rotateLeft 10)
  let mi91 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[17]!) j ^^^ (mi45) j)
  let mi92 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi91) j).rotateLeft 15)
  let mi93 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[23]!) j ^^^ (mi47) j)
  let mi94 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi93) j).rotateLeft 56)
  let mi95 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[2]!) j ^^^ (mi45) j)
  let mi96 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi95) j).rotateLeft 62)
  let mi97 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[8]!) j ^^^ (mi47) j)
  let mi98 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi97) j).rotateLeft 55)
  let mi99 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[14]!) j ^^^ (mi49) j)
  let mi100 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi99) j).rotateLeft 39)
  let mi101 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[15]!) j ^^^ (mi38) j)
  let mi102 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi101) j).rotateLeft 41)
  let mi103 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => (a.val[21]!) j ^^^ (mi42) j)
  let mi104 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => ((mi103) j).rotateLeft 2)
  let mi108 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi52) j) ((mi55) j) ((mi58) j))
  let mi112 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi55) j) ((mi58) j) ((mi61) j))
  let mi116 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi58) j) ((mi61) j) ((mi64) j))
  let mi119 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi61) j) ((mi64) j) ((mi52) j))
  let mi122 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi64) j) ((mi52) j) ((mi55) j))
  let mi126 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi66) j) ((mi68) j) ((mi70) j))
  let mi130 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi68) j) ((mi70) j) ((mi72) j))
  let mi134 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi70) j) ((mi72) j) ((mi74) j))
  let mi137 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi72) j) ((mi74) j) ((mi66) j))
  let mi140 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi74) j) ((mi66) j) ((mi68) j))
  let mi144 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi76) j) ((mi78) j) ((mi80) j))
  let mi148 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi78) j) ((mi80) j) ((mi82) j))
  let mi152 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi80) j) ((mi82) j) ((mi84) j))
  let mi155 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi82) j) ((mi84) j) ((mi76) j))
  let mi158 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi84) j) ((mi76) j) ((mi78) j))
  let mi162 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi86) j) ((mi88) j) ((mi90) j))
  let mi166 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi88) j) ((mi90) j) ((mi92) j))
  let mi170 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi90) j) ((mi92) j) ((mi94) j))
  let mi173 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi92) j) ((mi94) j) ((mi86) j))
  let mi176 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi94) j) ((mi86) j) ((mi88) j))
  let mi180 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi96) j) ((mi98) j) ((mi100) j))
  let mi184 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi98) j) ((mi100) j) ((mi102) j))
  let mi188 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi100) j) ((mi102) j) ((mi104) j))
  let mi191 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi102) j) ((mi104) j) ((mi96) j))
  let mi194 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => slhdsa.X86.ternary 210 ((mi104) j) ((mi96) j) ((mi98) j))
  let mi196 : KavxRust.core.core_arch.x86.__m512i := (fun j : Fin 8 => rc.bv)
  return writeRows a mi196 mi108 mi112 mi116 mi119 mi122 mi126 mi130 mi134 mi137 mi140 mi144 mi148 mi152 mi155 mi158 mi162 mi166 mi170 mi173 mi176 mi180 mi184 mi188 mi191 mi194

end slhdsa.Kavx
