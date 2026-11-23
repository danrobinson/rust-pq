module

@[expose] public section

/-!
# The Arm instructions used by the `hw-sha2` backends

This file is the meaning the proofs give to the processor instructions that
`rust/src/sha256.rs` and `rust/src/sha512.rs`, modules `hw::arm`, wrap. It is
a transcription of the pseudocode in the Arm Architecture Reference Manual
for A-profile architecture (DDI 0487): the instruction descriptions of
`SHA256H`, `SHA256H2`, `SHA256SU0` and `SHA256SU1`, and the shared functions
`SHA256hash`, `SHAchoose`, `SHAmajority`, `SHAhashSIGMA0` and
`SHAhashSIGMA1`; and (last section) the descriptions of `SHA512H`,
`SHA512H2`, `SHA512SU0` and `SHA512SU1` (FEAT_SHA512). The other
instructions (element-wise add, logical operations, shifts, `EXT`, loads and
stores) are simple enough to state directly.

Nothing here is proved about the processor. The definitions are checked
against the processor by running both on the same inputs (`ArmTest.lean`).
The file depends on core Lean only.
-/

namespace Arm

/-- A 128-bit register as four 32-bit elements: `e0` is `Elem[v, 0, 32]`,
bits 31:0. -/
structure V where
  e0 : BitVec 32
  e1 : BitVec 32
  e2 : BitVec 32
  e3 : BitVec 32
deriving DecidableEq, Inhabited, Repr

/-- `ROR(x, n)` on 32 bits. -/
def ROR (x : BitVec 32) (n : Nat) : BitVec 32 := x.rotateRight n

/-- `LSR(x, n)` on 32 bits. -/
def LSR (x : BitVec 32) (n : Nat) : BitVec 32 := x >>> n

/-- `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z`. -/
def SHAchoose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z

/-- `SHAmajority(x, y, z) = (x AND y) OR ((x OR y) AND z)`. -/
def SHAmajority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)`. -/
def SHAhashSIGMA0 (x : BitVec 32) : BitVec 32 := ROR x 2 ^^^ ROR x 13 ^^^ ROR x 22

/-- `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)`. -/
def SHAhashSIGMA1 (x : BitVec 32) : BitVec 32 := ROR x 6 ^^^ ROR x 11 ^^^ ROR x 25

/-- One iteration of the loop of `SHA256hash`, with `w = Elem[W, e, 32]`:
```
chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>);
maj = SHAmajority(X<31:0>, X<63:32>, X<95:64>);
t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs + Elem[W, e, 32];
X<127:96> = t + X<127:96>;
Y<127:96> = t + SHAhashSIGMA0(X<31:0>) + maj;
<Y, X> = ROL(Y : X, 32);
```
The rotation of the 256-bit `Y : X` by 32 moves every element up one place
and the top element of `Y` to the bottom of `X`. -/
def SHA256hashStep (X Y : V) (w : BitVec 32) : V × V :=
  let chs := SHAchoose Y.e0 Y.e1 Y.e2
  let maj := SHAmajority X.e0 X.e1 X.e2
  let t := Y.e3 + SHAhashSIGMA1 Y.e0 + chs + w
  let x3 := t + X.e3
  let y3 := t + SHAhashSIGMA0 X.e0 + maj
  (⟨y3, X.e0, X.e1, X.e2⟩, ⟨x3, Y.e0, Y.e1, Y.e2⟩)

/-- `SHA256hash(X, Y, W, part1)`: four iterations, `e = 0 to 3`, then `X` if
`part1` and `Y` otherwise. -/
def SHA256hash (X Y W : V) (part1 : Bool) : V :=
  let s0 := SHA256hashStep X Y W.e0
  let s1 := SHA256hashStep s0.1 s0.2 W.e1
  let s2 := SHA256hashStep s1.1 s1.2 W.e2
  let s3 := SHA256hashStep s2.1 s2.2 W.e3
  if part1 then s3.1 else s3.2

/-- `SHA256H <Qd>, <Qn>, <Vm>.4S`:
`result = SHA256hash(V[d], V[n], V[m], TRUE)`. -/
def SHA256H (d n m : V) : V := SHA256hash d n m true

/-- `SHA256H2 <Qd>, <Qn>, <Vm>.4S`:
`result = SHA256hash(V[n], V[d], V[m], FALSE)`. -/
def SHA256H2 (d n m : V) : V := SHA256hash n d m false

/-- `SHA256SU0 <Vd>.4S, <Vn>.4S`:
```
T = operand2<31:0> : operand1<127:32>;
for e = 0 to 3
    elt = Elem[T, e, 32];
    elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
    Elem[result, e, 32] = elt + Elem[operand1, e, 32];
```
with `operand1 = V[d]`, `operand2 = V[n]`. -/
def SHA256SU0 (d n : V) : V :=
  let f (elt : BitVec 32) : BitVec 32 := ROR elt 7 ^^^ ROR elt 18 ^^^ LSR elt 3
  ⟨f d.e1 + d.e0, f d.e2 + d.e1, f d.e3 + d.e2, f n.e0 + d.e3⟩

/-- `SHA256SU1 <Vd>.4S, <Vn>.4S, <Vm>.4S`:
```
T0 = operand3<31:0> : operand2<127:32>;
T1 = operand3<127:64>;
for e = 0 to 1
    elt = Elem[T1, e, 32];
    elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
    elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
    Elem[result, e, 32] = elt;
T1 = result<63:0>;
for e = 2 to 3
    elt = Elem[T1, e - 2, 32];
    elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
    elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
    Elem[result, e, 32] = elt;
```
with `operand1 = V[d]`, `operand2 = V[n]`, `operand3 = V[m]`. -/
def SHA256SU1 (d n m : V) : V :=
  let g (elt : BitVec 32) : BitVec 32 := ROR elt 17 ^^^ ROR elt 19 ^^^ LSR elt 10
  let r0 := g m.e2 + d.e0 + n.e1
  let r1 := g m.e3 + d.e1 + n.e2
  let r2 := g r0 + d.e2 + n.e3
  let r3 := g r1 + d.e3 + m.e0
  ⟨r0, r1, r2, r3⟩

/-- `ADD <Vd>.4S, <Vn>.4S, <Vm>.4S`: element-wise sum modulo 2^32. -/
def ADD (a b : V) : V := ⟨a.e0 + b.e0, a.e1 + b.e1, a.e2 + b.e2, a.e3 + b.e3⟩

/-- `ORR`: bitwise or. -/
def ORR (a b : V) : V := ⟨a.e0 ||| b.e0, a.e1 ||| b.e1, a.e2 ||| b.e2, a.e3 ||| b.e3⟩

/-- `AND`: bitwise and. -/
def AND (a b : V) : V := ⟨a.e0 &&& b.e0, a.e1 &&& b.e1, a.e2 &&& b.e2, a.e3 &&& b.e3⟩

/-- `USHR <Vd>.4S, <Vn>.4S, #n`: every element shifted right, zeros in. -/
def USHR (a : V) (n : Nat) : V := ⟨a.e0 >>> n, a.e1 >>> n, a.e2 >>> n, a.e3 >>> n⟩

/-- `SHL <Vd>.4S, <Vn>.4S, #n`: every element shifted left. -/
def SHL (a : V) (n : Nat) : V := ⟨a.e0 <<< n, a.e1 <<< n, a.e2 <<< n, a.e3 <<< n⟩

/-- `EXT` at two elements (`vextq_u32(a, b, 2)`): the top two of `a`, then
the bottom two of `b`. -/
def EXT2 (a b : V) : V := ⟨a.e2, a.e3, b.e0, b.e1⟩

/-- `EXT` at three elements (`vextq_u32(a, b, 3)`): the top one of `a`, then
the bottom three of `b`. -/
def EXT3 (a b : V) : V := ⟨a.e3, b.e0, b.e1, b.e2⟩

/-- Four bytes in memory order as one element after `REV32` on bytes: the
first byte is the most significant. -/
def beWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b0 ++ b1 ++ b2 ++ b3

/-- The four bytes of an element after `REV32`, in memory order. -/
def beBytes (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

/-- Whether the processor running the program has the `neon` and `sha2`
features: what `is_aarch64_feature_detected!` answers for both. It is opaque,
and nothing is assumed about its value: every statement about the crate is
proved for both answers.

It is not only an input to the feature test. The wrappers of the instructions
(`Slhdsa/FunsExternal.lean`) fail when it is `false`, because executing one of
them on a processor without the features is undefined behaviour in Rust. So
the proofs about the crate hold only if the code runs an instruction just when
the test has said yes: a program that skipped the test, or got it the wrong
way round, would fail for one of the two values, and its theorems could not be
proved without knowing which value this is. -/
opaque haveSha2 : Bool

/-! ## The SHA-512 instructions (FEAT_SHA512)

The instruction descriptions of `SHA512H`, `SHA512H2`, `SHA512SU0` and
`SHA512SU1` in the Arm ARM, and the plain vector operations the SHA-512
kernel of `rust/src/sha512.rs`, module `hw::arm`, uses, on a 128-bit
register viewed as two 64-bit elements. In the pseudocode `X<63:0>` is
element 0 (`e0`) and `X<127:64>` element 1 (`e1`). -/

/-- A 128-bit register as two 64-bit elements: `e0` is bits 63:0. -/
structure V2 where
  e0 : BitVec 64
  e1 : BitVec 64
deriving DecidableEq, Inhabited, Repr

/-- `ROR(x, n)` on 64 bits. -/
def ROR64 (x : BitVec 64) (n : Nat) : BitVec 64 := x.rotateRight n

/-- `LSR(x, n)` on 64 bits (the pseudocode's `Zeros(n) : x<63:n>`). -/
def LSR64 (x : BitVec 64) (n : Nat) : BitVec 64 := x >>> n

/-- `SHA512H <Qd>, <Qn>, <Vm>.2D`:
```
X = V[n]; Y = V[m]; W = V[d];
MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>);
tmp = Vtmp<127:64> + Y<63:0>;
MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>);
Vtmp<63:0> = (Vtmp<63:0> + MSigma1 + W<63:0>);
V[d] = Vtmp;
``` -/
def SHA512H (d n m : V2) : V2 :=
  let X := n
  let Y := m
  let W := d
  let sig1 (x : BitVec 64) : BitVec 64 := ROR64 x 14 ^^^ ROR64 x 18 ^^^ ROR64 x 41
  let hi := ((Y.e1 &&& X.e0) ^^^ (~~~Y.e1 &&& X.e1)) + sig1 Y.e1 + W.e1
  let tmp := hi + Y.e0
  let lo := ((tmp &&& Y.e1) ^^^ (~~~tmp &&& X.e0)) + sig1 tmp + W.e0
  ⟨lo, hi⟩

/-- `SHA512H2 <Qd>, <Qn>, <Vm>.2D`:
```
X = V[n]; Y = V[m]; W = V[d];
NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR (Y<127:64> AND Y<63:0>);
Vtmp<127:64> = (Vtmp<127:64> + NSigma0 + W<127:64>);
NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR ROR(Vtmp<127:64>, 39);
Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR (Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>);
Vtmp<63:0> = (Vtmp<63:0> + NSigma0 + W<63:0>);
V[d] = Vtmp;
``` -/
def SHA512H2 (d n m : V2) : V2 :=
  let X := n
  let Y := m
  let W := d
  let sig0 (x : BitVec 64) : BitVec 64 := ROR64 x 28 ^^^ ROR64 x 34 ^^^ ROR64 x 39
  let hi := ((X.e0 &&& Y.e1) ^^^ (X.e0 &&& Y.e0) ^^^ (Y.e1 &&& Y.e0)) + sig0 Y.e0 + W.e1
  let lo := ((hi &&& Y.e0) ^^^ (hi &&& Y.e1) ^^^ (Y.e1 &&& Y.e0)) + sig0 hi + W.e0
  ⟨lo, hi⟩

/-- `SHA512SU0 <Vd>.2D, <Vn>.2D`:
```
X = V[n]; W = V[d];
sig0 = ROR(W<127:64>, 1) EOR ROR(W<127:64>, 8) EOR ('0000000':W<127:71>);
Vtmp<63:0> = W<63:0> + sig0;
sig0 = ROR(X<63:0>, 1) EOR ROR(X<63:0>, 8) EOR ('0000000':X<63:7>);
Vtmp<127:64> = W<127:64> + sig0;
V[d] = Vtmp;
``` -/
def SHA512SU0 (d n : V2) : V2 :=
  let s (x : BitVec 64) : BitVec 64 := ROR64 x 1 ^^^ ROR64 x 8 ^^^ LSR64 x 7
  ⟨d.e0 + s d.e1, d.e1 + s n.e0⟩

/-- `SHA512SU1 <Vd>.2D, <Vn>.2D, <Vm>.2D`:
```
X = V[n]; Y = V[m]; W = V[d];
sig1 = ROR(X<127:64>, 19) EOR ROR(X<127:64>, 61) EOR ('000000':X<127:70>);
Vtmp<127:64> = W<127:64> + sig1 + Y<127:64>;
sig1 = ROR(X<63:0>, 19) EOR ROR(X<63:0>, 61) EOR ('000000':X<63:6>);
Vtmp<63:0> = W<63:0> + sig1 + Y<63:0>;
V[d] = Vtmp;
``` -/
def SHA512SU1 (d n m : V2) : V2 :=
  let s (x : BitVec 64) : BitVec 64 := ROR64 x 19 ^^^ ROR64 x 61 ^^^ LSR64 x 6
  ⟨d.e0 + s n.e0 + m.e0, d.e1 + s n.e1 + m.e1⟩

/-- `ADD <Vd>.2D, <Vn>.2D, <Vm>.2D`: element-wise sum modulo 2^64. -/
def ADD2 (a b : V2) : V2 := ⟨a.e0 + b.e0, a.e1 + b.e1⟩

/-- `EXT` at one 64-bit element (`vextq_u64(a, b, 1)`): the top element of
`a`, then the bottom element of `b`. -/
def EXT1 (a b : V2) : V2 := ⟨a.e1, b.e0⟩

/-- Eight bytes in memory order as one element after `REV64` on bytes: the
first byte is the most significant. -/
def beWord64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7

/-- Whether the processor running the program has the `neon` and `sha3`
features (Rust's name for FEAT_SHA3 with FEAT_SHA512): what
`is_aarch64_feature_detected!` answers for both. Opaque, independent of
`haveSha2`, and used in the same way: the SHA-512 wrappers fail when it is
`false`, and every statement about the crate is proved for both answers. -/
opaque haveSha512 : Bool

end Arm
