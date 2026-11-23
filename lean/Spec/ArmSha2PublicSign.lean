import Spec.ArmPureWrapper

/-! SHA-2 signing public entry and the shared width-specific dispatcher. A
call contract returns fresh signature descriptor cells. On the segmented tail
call the checked arguments include the original message and context slices.
Successful allocation, Rust Vec ownership and the AArch64 ABI are assumed. -/
namespace Spec.ArmSha2PublicSign
open ArmKeygen
structure Image where
  n : Nat
  deterministic : Bool
  entry : Nat
  words : Array Nat
  dispatch : Nat
  dispatchWords : Array Nat
  param : Nat
  frame : Nat
  core : Nat
  segmented : Nat
  free : Nat
inductive Route | rejected | contiguous | segmented deriving BEq, DecidableEq, Repr

private def cap := unknown 110 2
private def buf := unknown 111 2
private def length := unknown 112 2
private def descriptor := unknown 114 6
private def resultAddr := 0x900000

private def randomOK (s : State) (a : Image) (r : Nat) : Bool := Id.run do
  if !a.deterministic then return g s r == unknown 5 2
  let some ptr := natVal (g s r) | return false
  return region ptr a.n s.sp (stack-s.sp) && read s.m ptr a.n == some (ArmKeygen.block a.n 2)

def run (a : Image) (valid short : Bool) : Option Route := do
  let c : Config := ⟨a.n,0,0,a.entry,0,a.param,[],true,.shake⟩
  let s0 := put (put {pc := a.entry} 4 (num sk)) 8 (num resultAddr)
  let mut s := {s0 with m := write s0.m sk (secret a.n)}
  let mut phase := 0
  let mut routed := false
  let mut cmpC := false
  let mut cmpM := false
  for _ in [:128] do
    let pc := s.pc
    if pc == stop then
      guard (routed && cmpC && cmpM == valid && s.sp == stack &&
        (List.range 12).all (fun i => g s (18+i) == g s0 (18+i)))
      if !valid then
        guard (phase == 0 && (← read s.m resultAddr 8) == num (2^64-1))
        return .rejected
      guard ((← read s.m resultAddr 24) == descriptor)
      if short then guard (phase == 3); return .contiguous
      guard (phase == 4)
      return .segmented
    if pc == a.dispatch then
      guard (!routed && g s 0 == num a.param && g s 1 == unknown 0 2 && g s 2 == unknown 1 2 &&
        g s 3 == unknown 2 2 && g s 4 == unknown 3 2 && g s 5 == num sk &&
        g s 6 == num (4*a.n) && randomOK s a 7 && g s 8 == num resultAddr)
      routed := true
    if pc == a.segmented then
      guard (routed && cmpC && cmpM && valid && !short && phase == 0 &&
        g s 0 == num a.param && g s 1 == unknown 0 2 && g s 2 == unknown 1 2 &&
        g s 3 == unknown 2 2 && g s 4 == unknown 3 2 && g s 5 == num sk &&
        g s 6 == num (4*a.n) && randomOK s a 7 && g s 8 == num resultAddr)
      let ret ← if g s 30 == unknown 30 2 then some stop else natVal (g s 30)
      -- An ordinary successful callee returns to the incoming LR.
      let after := clobber s 350
      s := {after with pc := ret, m := write s.m resultAddr descriptor}
      phase := 4
      continue
    let (start,words) := if region pc 4 a.entry (4*a.words.size) then (a.entry,a.words)
      else (a.dispatch,a.dispatchWords)
    guard (pc ≥ start && (pc-start)%4 == 0)
    let w ← words[(pc-start)/4]?
    let next := {s with pc := pc+4}
    if w &&& 0xffc0001f == 0xf100001f then
      guard routed
      let reg := g s (w/32%32)
      let imm := w/1024%4096
      if imm == 255 then
        guard (!cmpC && reg == unknown 3 2)
        cmpC := true
        s := {next with ls := some valid}
      else
        guard (cmpC && valid && !cmpM && imm == 1023 && reg == unknown 1 2)
        cmpM := true
        s := {next with ls := some short}
    else if w &&& 0xfc000000 == 0x94000000 && addr pc (4*signExt (w%2^26) 26) != a.dispatch then
      let call := addr pc (4*signExt (w%2^26) 26)
      guard (cmpM && short)
      if call == a.frame then
        guard (phase == 0 && g s 0 == unknown 0 2 && g s 1 == unknown 1 2 &&
          g s 2 == unknown 2 2 && g s 3 == unknown 3 2)
        let slot ← natVal (g s 8)
        guard (region slot 24 s.sp (stack-s.sp) && slot%4 == 0)
        s := {clobber next 150 with m := write s.m slot (cap ++ buf ++ length)}
        phase := 1
      else if call == a.core then
        guard (phase == 1 && g s 0 == num a.param && g s 1 == buf && g s 2 == length &&
          g s 3 == num sk && g s 4 == num (4*a.n) && randomOK s a 5)
        let slot ← natVal (g s 8)
        guard (region slot 24 s.sp (stack-s.sp) && slot%4 == 0)
        s := {clobber next 200 with m := write s.m slot descriptor}
        phase := 2
      else
        guard (call == a.free && phase == 2 && g s 0 == buf && g s 1 == cap && g s 2 == num 1)
        s := clobber next 250
        phase := 3
    else if w &&& 0xff000000 == 0xb4000000 then
      guard (phase == 2 && g s (w%32) == cap)
      s := next
    else if w &&& 0xffffffe0 == 0x92800000 then
      s := put next (w%32) (num (2^64-1))
    else s ← step c s w (some ([(sk,4*a.n)],[(resultAddr,24)]))
  none

def execute (a : Image) (msg ctx : Bytes) := run a (decide (ctx.length ≤ 255)) (decide (msg.length ≤ 1023))

def expected (valid short : Bool) : Route := if valid then (if short then .contiguous else .segmented) else .rejected
end Spec.ArmSha2PublicSign
