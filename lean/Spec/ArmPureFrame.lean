import Spec.ArmKeygen

/-! Word-level abstract execution of the shared SHAKE pure framing helper. The
three allocator branch decisions are nondeterministic (first capacity equals one,
context requires reserve, message requires reserve). Each is consumed only after
comparing the correct operands. Input pointers/lengths, live allocation, capacity
and slice offsets have distinct symbolic cells. Moving allocation preserves its
initialized prefix. Sums and unsigned differences are interpreted on the domain
in which all slice lengths and the successful allocation fit isize. -/
namespace Spec.ArmPureFrame
open ArmKeygen

structure Image where
  entry : Nat
  words : Array Nat
  grow : Nat
  reserve : Nat
  copy : Nat

inductive Piece | domain | length | context | message deriving BEq, DecidableEq, Repr
structure Choices where
  firstOne : Bool
  reserveC : Bool
  reserveM : Bool
  emptyC : Bool
  emptyM : Bool
deriving Repr

def choices (n : Nat) : Choices := ⟨n.testBit 0,n.testBit 1,n.testBit 2,n.testBit 3,n.testBit 4⟩
def expected (b : Choices) : List Piece :=
  [.domain,.length] ++ (if b.emptyC then [] else [.context]) ++ (if b.emptyM then [] else [.message])

private def clen := unknown 3 2
private def mlen := unknown 1 2
private def midLen := unknown 70 2 -- 2 + |ctx|
private def fullLen := unknown 71 2 -- 2 + |ctx| + |msg|
private def availC := unknown 72 2 -- live capacity - 2
private def availM := unknown 73 2 -- live capacity - (2 + |ctx|)
private def cap (epoch : Nat) := unknown (80+epoch) 2
private def heap (epoch : Nat) := unknown (90+epoch) 2
private def destC (epoch : Nat) := unknown (100+epoch) 2 -- live pointer + 2
private def destM (epoch : Nat) := unknown (110+epoch) 2 -- live pointer + 2 + |ctx|
private def outAddr := 0x900000

def run (a : Image) (b : Choices) : Option (List Piece) := do
  let c : Config := ⟨0,0,0,a.entry,0,0,[],true,.shake⟩
  let start : State := put {pc := a.entry} 8 (num outAddr)
  let mut s := start
  let mut equalityFlags := false
  let mut epoch := 0
  let mut parts : List Piece := []
  for _ in [:128] do
    if s.pc == stop then
      guard (epoch > 0 && s.sp == stack && (List.range 13).all (fun i => g s (18+i) == g start (18+i)))
      guard ((← read s.m outAddr 24) == cap epoch ++ heap epoch ++ fullLen)
      return parts
    guard (s.pc ≥ a.entry && (s.pc-a.entry)%4 == 0)
    let w ← a.words[(s.pc-a.entry)/4]?
    let pc := s.pc
    let next := {s with pc := pc+4}
    let d := w%32
    let n := w/32%32
    let m := w/65536%32
    let imm := w/1024%4096
    let target := addr pc (4*signExt (w/32%2^19) 19)
    let branch := fun (yes : Bool) => {next with pc := if yes then target else pc+4}
    if w &&& 0xfc000000 == 0x94000000 then
      let call := addr pc (4*signExt (w%2^26) 26)
      if call == a.grow || call == a.reserve then
        let vec ← natVal (g s 0)
        guard (region vec 24 s.sp (stack-s.sp) && vec%4 == 0)
        let len ← read s.m (vec+16) 8
        if epoch == 0 then
          guard (call == a.grow && (← read s.m vec 24) == num 0 ++ num 1 ++ num 0 && parts.isEmpty)
        else
          guard ((← read s.m vec 16) == cap epoch ++ heap epoch)
          if call == a.grow then
            guard (epoch == 1 && len == num 1 && parts == [.domain])
          else
            guard (g s 1 == len && g s 3 == num 1 && g s 4 == num 1)
            guard ((len == num 2 && g s 2 == clen && parts == [.domain,.length]) ||
              (len == midLen && g s 2 == mlen && parts == [.domain,.length] ++ (if b.emptyC then [] else [.context])))
        epoch := epoch+1
        s := {clobber next (200+80*epoch) with m := write s.m vec (cap epoch ++ heap epoch)}
      else
        guard (call == a.copy && epoch > 0)
        if g s 0 == destC epoch then
          guard (g s 1 == unknown 2 2 && g s 2 == clen && parts == [.domain,.length])
          parts := parts ++ [.context]
        else
          guard (g s 0 == destM epoch && g s 1 == unknown 0 2 && g s 2 == mlen &&
            parts == [.domain,.length] ++ (if b.emptyC then [] else [.context]))
          parts := parts ++ [.message]
        s := clobber next 700
    else if w &&& 0xffc00000 == 0x39000000 then -- STRB unsigned offset
      guard (epoch > 0 && g s n == heap epoch)
      if imm == 0 then
        guard (d == 31 && parts.isEmpty)
        parts := [.domain]
      else
        guard (imm == 1 && d < 31 && g s d == clen && parts == [.domain])
        parts := parts ++ [.length]
      s := next
    else if w &&& 0xffc0001f == 0xf100001f then
      guard (imm == 1 && epoch == 1 && g s n == cap epoch)
      equalityFlags := true
      s := {next with ls := some b.firstOne}
    else if w &&& 0xff00001f == 0x54000001 || w &&& 0xff00001f == 0x54000008 then
      guard ((w &&& 0xff00001f == 0x54000001) == equalityFlags)
      let flag ← s.ls
      s := branch (!flag)
    else if w &&& 0xffc00000 == 0xd1000000 && d < 31 && g s n == cap epoch then
      guard (epoch > 0 && imm == 2)
      s := put next d availC
    else if w &&& 0xffe0fc1f == 0xeb00001f then -- CMP unshifted
      let enough ← if g s n == clen && g s m == availC then some (!b.reserveC || b.emptyC)
        else if g s n == mlen && g s m == availM then some (!b.reserveM || b.emptyM) else none
      equalityFlags := false
      s := {next with ls := some enough}
    else if w &&& 0xff000000 == 0xb4000000 then
      let empty ← if g s d == clen then some b.emptyC else if g s d == mlen then some b.emptyM else none
      s := branch empty
    else if w &&& 0xffe0fc00 == 0x8b000000 then -- ADD unshifted
      let x := g s n
      let y := g s m
      let v ← if x == heap epoch && y == num 2 then some (destC epoch) else
        if x == heap epoch && y == midLen then some (destM epoch) else
        if x == num 2 && y == clen then some midLen else if x == midLen && y == mlen then some fullLen else none
      s := put next d v
    else if w &&& 0xffe0fc00 == 0xcb000000 then
      guard (g s n == cap epoch && g s m == midLen)
      s := put next d availM
    else s ← step c s w (some ([],[(outAddr,24)]))
  none

def bytes (m ctx : Bytes) : Piece → Bytes
  | .domain => [0]
  | .length => [BitVec.ofNat 8 ctx.length]
  | .context => ctx
  | .message => m

theorem expected_bytes (b : Choices) (m ctx : Bytes)
    (hc : b.emptyC = decide (ctx = [])) (hm : b.emptyM = decide (m = [])) :
    (expected b).flatMap (bytes m ctx) = withContext m ctx := by
  by_cases c : ctx = [] <;> by_cases msg : m = [] <;>
    simp [expected,bytes,hc,hm,c,msg,withContext,toByte,List.range_succ]

theorem of_run {a b parts} (checked : run a b = some (expected b)) (h : run a b = some parts)
    (m ctx : Bytes) (hc : b.emptyC = decide (ctx = [])) (hm : b.emptyM = decide (m = [])) :
    parts.flatMap (bytes m ctx) = withContext m ctx := by
  rw [checked] at h
  cases h
  exact expected_bytes b m ctx hc hm
end Spec.ArmPureFrame
