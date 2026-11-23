import Spec.ApplePureFrameWitness

/-! Restricted word interpreter for SHAKE pure API wrappers on the measured Apple image.
The shared frame builder has its own byte-construction certificate. Its successful
call returns a live, nonempty-capacity Vec. The internal operation returns arbitrary
abstract ABI data. Only transfers can preserve these cells to the public result. -/
namespace Spec.ArmPureWrapper
open ArmKeygen

inductive Mode | verify | sign | deterministic deriving BEq, DecidableEq, Repr
structure Image where
  mode : Mode
  n : Nat
  param : Nat
  entry : Nat
  words : Array Nat
  frame : Nat
  core : Nat
  free : Nat
deriving Repr

inductive Result | rejected | forwarded deriving BEq, DecidableEq, Repr

private def capacity := unknown 110 2
private def framed := unknown 111 2
private def frameLen := unknown 112 2
private def verdict := unknown 113 2
private def descriptor := unknown 114 6
private def resultAddr := 0x900000
private def ctxReg (a : Image) := if a.mode == .verify then 5 else 3

def run (a : Image) (short : Bool) : Option Result := do
  let c : Config := ⟨a.n,0,0,a.entry,0,a.param,[],true,.shake⟩
  let initial : State := {pc := a.entry}
  let mut s := initial
  if a.mode != .verify then
    s := put (put s 8 (num resultAddr)) 4 (num sk)
    s := {s with m := write s.m sk (secret a.n)}
  let mut phase := 0
  let mut compared := false
  for _ in [:96] do
    if s.pc == stop then
      guard (compared && s.sp == stack && (List.range 13).all (fun i => g s (18+i) == g initial (18+i)))
      if short then
        guard (phase == 3)
        if a.mode == .verify then guard (g s 0 == verdict)
        else guard ((← read s.m resultAddr 24) == descriptor)
        return .forwarded
      guard (phase == 0)
      if a.mode == .verify then guard (g s 0 == num 0)
      else guard ((← read s.m resultAddr 8) == num (2^64-1))
      return .rejected
    let pc := s.pc
    guard (pc ≥ a.entry && (pc-a.entry)%4 == 0)
    let w ← a.words[(pc-a.entry)/4]?
    let next := {s with pc := pc+4}
    if w &&& 0xffc0001f == 0xf100001f then
      guard (!compared && (w/1024)%4096 == 255 && g s (w/32%32) == unknown (ctxReg a) 2)
      compared := true
      s := {next with ls := some short}
    else if w &&& 0xfc000000 == 0x94000000 then
      let target := addr pc (4*signExt (w%2^26) 26)
      if target == a.frame then
        guard (short && compared && phase == 0)
        guard (g s 0 == unknown 0 2 && g s 1 == unknown 1 2 &&
          g s 2 == unknown (ctxReg a-1) 2 && g s 3 == unknown (ctxReg a) 2)
        let out ← natVal (g s 8)
        guard (region out 24 s.sp (stack-s.sp) && out%4 == 0)
        s := {clobber next 150 with m := write s.m out (capacity ++ framed ++ frameLen)}
        phase := 1
      else if target == a.core then
        guard (phase == 1 && g s 0 == num a.param && g s 1 == framed && g s 2 == frameLen)
        if a.mode == .verify then
          guard (g s 3 == unknown 2 2 && g s 4 == unknown 3 2 && g s 5 == unknown 6 2 && g s 6 == num (2*a.n))
          s := put (clobber next 200) 0 verdict
        else
          guard (g s 3 == num sk && g s 4 == num (4*a.n))
          if a.mode == .deterministic then
            let r ← natVal (g s 5)
            guard (region r a.n s.sp (stack-s.sp) && (← read s.m r a.n) == ArmKeygen.block a.n 2)
          else guard (g s 5 == unknown 5 2)
          let out ← natVal (g s 8)
          guard (region out 24 s.sp (stack-s.sp) && out%4 == 0)
          s := {clobber next 200 with m := write s.m out descriptor}
        phase := 2
      else
        guard (phase == 2 && target == a.free && g s 0 == framed && g s 1 == capacity && g s 2 == num 1)
        s := clobber next 250
        phase := 3
    else if w &&& 0xff000000 == 0xb4000000 then
      -- CBZ of the frame capacity. A Vec holding the two framing bytes has positive capacity.
      guard (phase == 2 && g s (w%32) == capacity)
      s := next
    else if w &&& 0xffffffe0 == 0x92800000 then
      s := put next (w%32) (num (2^64-1))
    else
      s ← step c s w (some ([(sk,4*a.n)], if a.mode == .verify then [] else [(resultAddr,24)]))
  none

/-- Successful shared-framer observation used by both public consumers. Slice/Vec
sizes fit the signed allocation limit, and the context guard selected this path. -/
structure Frame (msg ctx : Bytes) where
  choices : ArmPureFrame.Choices
  parts : List ArmPureFrame.Piece
  short : ctx.length ≤ 255
  fits : 2 + ctx.length + msg.length < 2^63
  result : ArmPureFrame.run LinkedApplePureFrame.image choices = some parts
  contextEmpty : choices.emptyC = decide (ctx = [])
  messageEmpty : choices.emptyM = decide (msg = [])

/-- The frame observation exists for every bounded input and every successful
allocator branch history, including empty context and empty message. -/
def Frame.ofAllocation (msg ctx : Bytes) (short : ctx.length ≤ 255)
    (fits : 2 + ctx.length + msg.length < 2^63) (firstOne reserveC reserveM : Bool) : Frame msg ctx :=
  let b : ArmPureFrame.Choices :=
    ⟨firstOne,reserveC,reserveM,decide (ctx = []),decide (msg = [])⟩
  ⟨b,ArmPureFrame.expected b,short,fits,LinkedApplePureFrame.checked b,rfl,rfl⟩

def Frame.payload {msg ctx} (f : Frame msg ctx) := f.parts.flatMap (ArmPureFrame.bytes msg ctx)

theorem Frame.payload_eq {msg ctx} (f : Frame msg ctx) : f.payload = withContext msg ctx :=
  LinkedApplePureFrame.framed f.result msg ctx f.contextEmpty f.messageEmpty

/-- Specialize the opaque unsigned context-length comparison to the supplied slice. -/
def execute (a : Image) (ctx : Bytes) := run a (decide (ctx.length ≤ 255))

theorem longContext {a ctx} (long : run a false = some .rejected) (h : 255 < ctx.length) :
    execute a ctx = some .rejected := by simp [execute,show ¬ctx.length ≤ 255 by omega,long]

theorem validContext {a ctx} (normal : run a true = some .forwarded) (h : ctx.length ≤ 255) :
    execute a ctx = some .forwarded := by simp [execute,h,normal]

def verifyReturn (r : Result) (v : Bool) := if r = .forwarded then v else false
def signReturn (r : Result) (sig : Bytes) := if r = .forwarded then some sig else none

theorem verify_eq {a p msg sig ctx pk r verdict}
    (normal : run a true = some .forwarded) (long : run a false = some .rejected)
    (actual : execute a ctx = some r)
    (core : ctx.length ≤ 255 → verdict = slhVerifyInternal p (withContext msg ctx) sig pk) :
    verifyReturn r verdict = slhVerify p msg sig ctx pk := by
  by_cases h : ctx.length ≤ 255
  · simp [execute,h,normal] at actual
    subst r
    simpa [verifyReturn,slhVerify,show ¬ ctx.length > 255 by omega] using core h
  · simp [execute,h,long] at actual
    subst r
    simp [verifyReturn,slhVerify,show ctx.length > 255 by omega]

theorem sign_eq {a p msg ctx sk rand r sig}
    (normal : run a true = some .forwarded) (long : run a false = some .rejected)
    (actual : execute a ctx = some r)
    (core : ctx.length ≤ 255 → sig = slhSignInternal p (withContext msg ctx) sk rand) :
    signReturn r sig = slhSign p msg ctx sk rand := by
  by_cases h : ctx.length ≤ 255 <;> simp [execute,h,normal,long] at actual <;> subst r
  · simp [signReturn,slhSign,show ¬ ctx.length > 255 by omega,core h]
  · simp [signReturn,slhSign,show ctx.length > 255 by omega]
end Spec.ArmPureWrapper
