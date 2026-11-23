import Kneon.Funs
import Ksha3.Rows
open Aeneas Aeneas.Std Result
namespace slhdsa.Kneon
open Ksha3 (Reg Rows writeRows)
def pureRound (a : Rows) (rc : U64) := Id.run do
  let uxt5 : Reg := fun j => (a.val[15]! j) ^^^ (a.val[20]! j)
  let uxt6 : Reg := fun j => (a.val[10]! j) ^^^ (uxt5 j)
  let uxt7 : Reg := fun j => (a.val[5]! j) ^^^ (uxt6 j)
  let uxt8 : Reg := fun j => (a.val[0]! j) ^^^ (uxt7 j)
  let uxt14 : Reg := fun j => (a.val[16]! j) ^^^ (a.val[21]! j)
  let uxt15 : Reg := fun j => (a.val[11]! j) ^^^ (uxt14 j)
  let uxt16 : Reg := fun j => (a.val[6]! j) ^^^ (uxt15 j)
  let uxt17 : Reg := fun j => (a.val[1]! j) ^^^ (uxt16 j)
  let uxt23 : Reg := fun j => (a.val[17]! j) ^^^ (a.val[22]! j)
  let uxt24 : Reg := fun j => (a.val[12]! j) ^^^ (uxt23 j)
  let uxt25 : Reg := fun j => (a.val[7]! j) ^^^ (uxt24 j)
  let uxt26 : Reg := fun j => (a.val[2]! j) ^^^ (uxt25 j)
  let uxt32 : Reg := fun j => (a.val[18]! j) ^^^ (a.val[23]! j)
  let uxt33 : Reg := fun j => (a.val[13]! j) ^^^ (uxt32 j)
  let uxt34 : Reg := fun j => (a.val[8]! j) ^^^ (uxt33 j)
  let uxt35 : Reg := fun j => (a.val[3]! j) ^^^ (uxt34 j)
  let uxt41 : Reg := fun j => (a.val[19]! j) ^^^ (a.val[24]! j)
  let uxt42 : Reg := fun j => (a.val[14]! j) ^^^ (uxt41 j)
  let uxt43 : Reg := fun j => (a.val[9]! j) ^^^ (uxt42 j)
  let uxt44 : Reg := fun j => (a.val[4]! j) ^^^ (uxt43 j)
  let uxt47 : Reg := fun j => (uxt17 j) <<< 1
  let uxt48 : Reg := fun j => ((uxt47 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((uxt17 j) >>> 63)
  let uxt49 : Reg := fun j => (uxt44 j) ^^^ (uxt48 j)
  let uxt52 : Reg := fun j => (uxt26 j) <<< 1
  let uxt53 : Reg := fun j => ((uxt52 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((uxt26 j) >>> 63)
  let uxt54 : Reg := fun j => (uxt8 j) ^^^ (uxt53 j)
  let uxt56 : Reg := fun j => (uxt35 j) <<< 1
  let uxt57 : Reg := fun j => ((uxt56 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((uxt35 j) >>> 63)
  let uxt58 : Reg := fun j => (uxt17 j) ^^^ (uxt57 j)
  let uxt59 : Reg := fun j => (uxt44 j) <<< 1
  let uxt60 : Reg := fun j => ((uxt59 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((uxt44 j) >>> 63)
  let uxt61 : Reg := fun j => (uxt26 j) ^^^ (uxt60 j)
  let uxt62 : Reg := fun j => (uxt8 j) <<< 1
  let uxt63 : Reg := fun j => ((uxt62 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((uxt8 j) >>> 63)
  let uxt64 : Reg := fun j => (uxt35 j) ^^^ (uxt63 j)
  let x : Reg := fun j => (a.val[0]! j) ^^^ (uxt49 j)
  let uxt66 : Reg := fun j => (x j) <<< 0
  let uxt67 : Reg := fun j => ((uxt66 j) &&& (BitVec.allOnes 64 <<< 0)) ||| ((x j) >>> 64)
  let x1 : Reg := fun j => (a.val[6]! j) ^^^ (uxt54 j)
  let uxt69 : Reg := fun j => (x1 j) <<< 44
  let uxt70 : Reg := fun j => ((uxt69 j) &&& (BitVec.allOnes 64 <<< 44)) ||| ((x1 j) >>> 20)
  let x2 : Reg := fun j => (a.val[12]! j) ^^^ (uxt58 j)
  let uxt72 : Reg := fun j => (x2 j) <<< 43
  let uxt73 : Reg := fun j => ((uxt72 j) &&& (BitVec.allOnes 64 <<< 43)) ||| ((x2 j) >>> 21)
  let x3 : Reg := fun j => (a.val[18]! j) ^^^ (uxt61 j)
  let uxt75 : Reg := fun j => (x3 j) <<< 21
  let uxt76 : Reg := fun j => ((uxt75 j) &&& (BitVec.allOnes 64 <<< 21)) ||| ((x3 j) >>> 43)
  let x4 : Reg := fun j => (a.val[24]! j) ^^^ (uxt64 j)
  let uxt78 : Reg := fun j => (x4 j) <<< 14
  let uxt79 : Reg := fun j => ((uxt78 j) &&& (BitVec.allOnes 64 <<< 14)) ||| ((x4 j) >>> 50)
  let x5 : Reg := fun j => (a.val[3]! j) ^^^ (uxt61 j)
  let uxt80 : Reg := fun j => (x5 j) <<< 28
  let uxt81 : Reg := fun j => ((uxt80 j) &&& (BitVec.allOnes 64 <<< 28)) ||| ((x5 j) >>> 36)
  let x6 : Reg := fun j => (a.val[9]! j) ^^^ (uxt64 j)
  let uxt82 : Reg := fun j => (x6 j) <<< 20
  let uxt83 : Reg := fun j => ((uxt82 j) &&& (BitVec.allOnes 64 <<< 20)) ||| ((x6 j) >>> 44)
  let x7 : Reg := fun j => (a.val[10]! j) ^^^ (uxt49 j)
  let uxt84 : Reg := fun j => (x7 j) <<< 3
  let uxt85 : Reg := fun j => ((uxt84 j) &&& (BitVec.allOnes 64 <<< 3)) ||| ((x7 j) >>> 61)
  let x8 : Reg := fun j => (a.val[16]! j) ^^^ (uxt54 j)
  let uxt86 : Reg := fun j => (x8 j) <<< 45
  let uxt87 : Reg := fun j => ((uxt86 j) &&& (BitVec.allOnes 64 <<< 45)) ||| ((x8 j) >>> 19)
  let x9 : Reg := fun j => (a.val[22]! j) ^^^ (uxt58 j)
  let uxt88 : Reg := fun j => (x9 j) <<< 61
  let uxt89 : Reg := fun j => ((uxt88 j) &&& (BitVec.allOnes 64 <<< 61)) ||| ((x9 j) >>> 3)
  let x10 : Reg := fun j => (a.val[1]! j) ^^^ (uxt54 j)
  let uxt90 : Reg := fun j => (x10 j) <<< 1
  let uxt91 : Reg := fun j => ((uxt90 j) &&& (BitVec.allOnes 64 <<< 1)) ||| ((x10 j) >>> 63)
  let x11 : Reg := fun j => (a.val[7]! j) ^^^ (uxt58 j)
  let uxt92 : Reg := fun j => (x11 j) <<< 6
  let uxt93 : Reg := fun j => ((uxt92 j) &&& (BitVec.allOnes 64 <<< 6)) ||| ((x11 j) >>> 58)
  let x12 : Reg := fun j => (a.val[13]! j) ^^^ (uxt61 j)
  let uxt94 : Reg := fun j => (x12 j) <<< 25
  let uxt95 : Reg := fun j => ((uxt94 j) &&& (BitVec.allOnes 64 <<< 25)) ||| ((x12 j) >>> 39)
  let x13 : Reg := fun j => (a.val[19]! j) ^^^ (uxt64 j)
  let uxt96 : Reg := fun j => (x13 j) <<< 8
  let uxt97 : Reg := fun j => ((uxt96 j) &&& (BitVec.allOnes 64 <<< 8)) ||| ((x13 j) >>> 56)
  let x14 : Reg := fun j => (a.val[20]! j) ^^^ (uxt49 j)
  let uxt98 : Reg := fun j => (x14 j) <<< 18
  let uxt99 : Reg := fun j => ((uxt98 j) &&& (BitVec.allOnes 64 <<< 18)) ||| ((x14 j) >>> 46)
  let x15 : Reg := fun j => (a.val[4]! j) ^^^ (uxt64 j)
  let uxt100 : Reg := fun j => (x15 j) <<< 27
  let uxt101 : Reg := fun j => ((uxt100 j) &&& (BitVec.allOnes 64 <<< 27)) ||| ((x15 j) >>> 37)
  let x16 : Reg := fun j => (a.val[5]! j) ^^^ (uxt49 j)
  let uxt102 : Reg := fun j => (x16 j) <<< 36
  let uxt103 : Reg := fun j => ((uxt102 j) &&& (BitVec.allOnes 64 <<< 36)) ||| ((x16 j) >>> 28)
  let x17 : Reg := fun j => (a.val[11]! j) ^^^ (uxt54 j)
  let uxt104 : Reg := fun j => (x17 j) <<< 10
  let uxt105 : Reg := fun j => ((uxt104 j) &&& (BitVec.allOnes 64 <<< 10)) ||| ((x17 j) >>> 54)
  let x18 : Reg := fun j => (a.val[17]! j) ^^^ (uxt58 j)
  let uxt106 : Reg := fun j => (x18 j) <<< 15
  let uxt107 : Reg := fun j => ((uxt106 j) &&& (BitVec.allOnes 64 <<< 15)) ||| ((x18 j) >>> 49)
  let x19 : Reg := fun j => (a.val[23]! j) ^^^ (uxt61 j)
  let uxt108 : Reg := fun j => (x19 j) <<< 56
  let uxt109 : Reg := fun j => ((uxt108 j) &&& (BitVec.allOnes 64 <<< 56)) ||| ((x19 j) >>> 8)
  let x20 : Reg := fun j => (a.val[2]! j) ^^^ (uxt58 j)
  let uxt110 : Reg := fun j => (x20 j) <<< 62
  let uxt111 : Reg := fun j => ((uxt110 j) &&& (BitVec.allOnes 64 <<< 62)) ||| ((x20 j) >>> 2)
  let x21 : Reg := fun j => (a.val[8]! j) ^^^ (uxt61 j)
  let uxt112 : Reg := fun j => (x21 j) <<< 55
  let uxt113 : Reg := fun j => ((uxt112 j) &&& (BitVec.allOnes 64 <<< 55)) ||| ((x21 j) >>> 9)
  let x22 : Reg := fun j => (a.val[14]! j) ^^^ (uxt64 j)
  let uxt114 : Reg := fun j => (x22 j) <<< 39
  let uxt115 : Reg := fun j => ((uxt114 j) &&& (BitVec.allOnes 64 <<< 39)) ||| ((x22 j) >>> 25)
  let x23 : Reg := fun j => (a.val[15]! j) ^^^ (uxt49 j)
  let uxt116 : Reg := fun j => (x23 j) <<< 41
  let uxt117 : Reg := fun j => ((uxt116 j) &&& (BitVec.allOnes 64 <<< 41)) ||| ((x23 j) >>> 23)
  let x24 : Reg := fun j => (a.val[21]! j) ^^^ (uxt54 j)
  let uxt118 : Reg := fun j => (x24 j) <<< 2
  let uxt119 : Reg := fun j => ((uxt118 j) &&& (BitVec.allOnes 64 <<< 2)) ||| ((x24 j) >>> 62)
  let uxt123 : Reg := fun j => (uxt73 j) &&& ~~~(uxt70 j)
  let uxt124 : Reg := fun j => (uxt67 j) ^^^ (uxt123 j)
  let uxt128 : Reg := fun j => (uxt76 j) &&& ~~~(uxt73 j)
  let uxt129 : Reg := fun j => (uxt70 j) ^^^ (uxt128 j)
  let uxt133 : Reg := fun j => (uxt79 j) &&& ~~~(uxt76 j)
  let uxt134 : Reg := fun j => (uxt73 j) ^^^ (uxt133 j)
  let uxt137 : Reg := fun j => (uxt67 j) &&& ~~~(uxt79 j)
  let uxt138 : Reg := fun j => (uxt76 j) ^^^ (uxt137 j)
  let uxt141 : Reg := fun j => (uxt70 j) &&& ~~~(uxt67 j)
  let uxt142 : Reg := fun j => (uxt79 j) ^^^ (uxt141 j)
  let uxt146 : Reg := fun j => (uxt85 j) &&& ~~~(uxt83 j)
  let uxt147 : Reg := fun j => (uxt81 j) ^^^ (uxt146 j)
  let uxt151 : Reg := fun j => (uxt87 j) &&& ~~~(uxt85 j)
  let uxt152 : Reg := fun j => (uxt83 j) ^^^ (uxt151 j)
  let uxt156 : Reg := fun j => (uxt89 j) &&& ~~~(uxt87 j)
  let uxt157 : Reg := fun j => (uxt85 j) ^^^ (uxt156 j)
  let uxt160 : Reg := fun j => (uxt81 j) &&& ~~~(uxt89 j)
  let uxt161 : Reg := fun j => (uxt87 j) ^^^ (uxt160 j)
  let uxt164 : Reg := fun j => (uxt83 j) &&& ~~~(uxt81 j)
  let uxt165 : Reg := fun j => (uxt89 j) ^^^ (uxt164 j)
  let uxt169 : Reg := fun j => (uxt95 j) &&& ~~~(uxt93 j)
  let uxt170 : Reg := fun j => (uxt91 j) ^^^ (uxt169 j)
  let uxt174 : Reg := fun j => (uxt97 j) &&& ~~~(uxt95 j)
  let uxt175 : Reg := fun j => (uxt93 j) ^^^ (uxt174 j)
  let uxt179 : Reg := fun j => (uxt99 j) &&& ~~~(uxt97 j)
  let uxt180 : Reg := fun j => (uxt95 j) ^^^ (uxt179 j)
  let uxt183 : Reg := fun j => (uxt91 j) &&& ~~~(uxt99 j)
  let uxt184 : Reg := fun j => (uxt97 j) ^^^ (uxt183 j)
  let uxt187 : Reg := fun j => (uxt93 j) &&& ~~~(uxt91 j)
  let uxt188 : Reg := fun j => (uxt99 j) ^^^ (uxt187 j)
  let uxt192 : Reg := fun j => (uxt105 j) &&& ~~~(uxt103 j)
  let uxt193 : Reg := fun j => (uxt101 j) ^^^ (uxt192 j)
  let uxt197 : Reg := fun j => (uxt107 j) &&& ~~~(uxt105 j)
  let uxt198 : Reg := fun j => (uxt103 j) ^^^ (uxt197 j)
  let uxt202 : Reg := fun j => (uxt109 j) &&& ~~~(uxt107 j)
  let uxt203 : Reg := fun j => (uxt105 j) ^^^ (uxt202 j)
  let uxt206 : Reg := fun j => (uxt101 j) &&& ~~~(uxt109 j)
  let uxt207 : Reg := fun j => (uxt107 j) ^^^ (uxt206 j)
  let uxt210 : Reg := fun j => (uxt103 j) &&& ~~~(uxt101 j)
  let uxt211 : Reg := fun j => (uxt109 j) ^^^ (uxt210 j)
  let uxt215 : Reg := fun j => (uxt115 j) &&& ~~~(uxt113 j)
  let uxt216 : Reg := fun j => (uxt111 j) ^^^ (uxt215 j)
  let uxt220 : Reg := fun j => (uxt117 j) &&& ~~~(uxt115 j)
  let uxt221 : Reg := fun j => (uxt113 j) ^^^ (uxt220 j)
  let uxt225 : Reg := fun j => (uxt119 j) &&& ~~~(uxt117 j)
  let uxt226 : Reg := fun j => (uxt115 j) ^^^ (uxt225 j)
  let uxt229 : Reg := fun j => (uxt111 j) &&& ~~~(uxt119 j)
  let uxt230 : Reg := fun j => (uxt117 j) ^^^ (uxt229 j)
  let uxt233 : Reg := fun j => (uxt113 j) &&& ~~~(uxt111 j)
  let uxt234 : Reg := fun j => (uxt119 j) ^^^ (uxt233 j)
  let uxt236 : Reg := fun j => rc.bv
  return writeRows a uxt236 uxt124 uxt129 uxt134 uxt138 uxt142 uxt147 uxt152 uxt157 uxt161 uxt165 uxt170 uxt175 uxt180 uxt184 uxt188 uxt193 uxt198 uxt203 uxt207 uxt211 uxt216 uxt221 uxt226 uxt230 uxt234
end slhdsa.Kneon
