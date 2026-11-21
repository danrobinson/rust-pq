module

@[expose] public section

/-!
# The Arm instructions used by the `hw-sha2` backend

This file is the meaning the proofs give to the processor instructions that
`rust/src/sha256.rs`, module `hw::arm`, wraps. It is a transcription of the
pseudocode in the Arm Architecture Reference Manual for A-profile
architecture (DDI 0487): the instruction descriptions of `SHA256H`,
`SHA256H2`, `SHA256SU0` and `SHA256SU1`, and the shared functions
`SHA256hash`, `SHAchoose`, `SHAmajority`, `SHAhashSIGMA0` and
`SHAhashSIGMA1`. The other instructions (element-wise add, logical
operations, shifts, `EXT`, loads and stores) are simple enough to state
directly.

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

/-- Whether the processor has the `neon` and `sha2` features. Nothing is
assumed about it: every statement is proved for both answers. -/
opaque haveSha2 : Bool

end Arm
