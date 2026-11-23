import Spec.ArmSha2Verify
import Spec.ArmPureWrapper

namespace Spec.ArmSha2PublicVerify
open ArmKeygen
open ArmVerifyBody (Control Action arg frame has cellBuffer digestPtr digestCap root verdict)

structure Image where
  internal : ArmSha2Verify.Image
  publicEntry : Nat
  publicWords : Array Nat
  dispatcher : Nat
  dispatchWords : Array Nat
  segmented : Nat
  segmentedWords : Array Nat
  digest : Nat

inductive Result | contextRejected | signatureRejected | framed | segmented deriving BEq, DecidableEq, Repr
structure State where
  ctrl : Control
  ctxTest : Bool := false
  msgTest : Bool := false
  sigTest : Bool := false
  inLong : Bool := false
  frameLive : Bool := false
  shortCall : Bool := false

def route (ctxOK small sigOK : Bool) : Result :=
  if !ctxOK then .contextRejected else if !sigOK then .signatureRejected else if small then .framed else .segmented

private def frameCap := unknown 7000 2
private def framePtr := unknown 7001 2
private def frameLen := unknown 7002 2
private def lenTag := unknown 3 2

def longImage (a : Image) : ArmSha2Verify.Image :=
  {a.internal with core := {a.internal.core with body := a.segmented, words := a.segmentedWords}}

/-- The two words of the public root have been saved separately by the segmented 128-bit routine. -/
def compare16Words := [0xa97623a9,0xf94017ea,0xeb0a013f,0xf9401be9,0xfa490100,0x1a9f17e0]
theorem compare16 (m : LinkedArm.RootComparison.ByteMemory) (s : LinkedArm.RootComparison.State) :
    LinkedArm.RootComparison.verdict compare16Words (LinkedArm.RootComparison.load64 m) s =
      some (if LinkedArm.RootComparison.byteSlice m (s.regs 29-160) 16 =
        (LinkedArm.RootComparison.byteSlice m (s.sp+40) 8 ++ LinkedArm.RootComparison.byteSlice m (s.sp+48) 8) then 1 else 0) := by
  simp [compare16Words,LinkedArm.RootComparison.verdict,LinkedArm.RootComparison.step,
    LinkedArm.RootComparison.base,LinkedArm.RootComparison.operand,LinkedArm.RootComparison.write,
    LinkedArm.RootComparison.load64_eq,LinkedArm.RootComparison.byteSlice,List.range_succ,List.foldlM,
    Bool.and_eq_true,and_assoc,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- The SHA2-128 segmented seed circuit computes the same seeded compression with X10
as its message-ring pointer and X11 as the ABCD constant pointer. The code and its two
PC-relative literal pages must match before this summary can fire. -/
def seed128 (a : Image) (c : Control) : Option Control := do
  let s := c.machine
  let i := (longImage a).core
  let pc := s.pc
  guard (i.p.n == 16 && pc == 0x10006fcd8 && !s.seeded && q s 0 == ArmKeygen.block 16 1 && (← arg s 8) == 0)
  let real ← (List.range 42).mapM (fun j => ArmVerifyBody.code i (pc+4*(if j<38 then j else j+2)))
  let patches : List (Nat × Nat) := [(2,0xad0507e0),(3,0xad0607e1),(4,0x910283ea),(5,0xd0000329),
    (6,0x3dc3cd20),(7,0xb000036c),(8,0x9111c18c),(9,0xd000032b),(10,0x3dc3d161),
    (20,0x54000280),(22,0x3cee7942),(27,0x3cef7943),(32,0x3cf07943),(34,0x3cef7945),
    (36,0x3cae7944),(38,0x3dc3d161)]
  guard (real == inlineWords.zipIdx.map (fun (w,j) => (patches.lookup j).getD w))
  let h0 := SHA256.H0.map BitVec.toNat
  guard (a.internal.iv == h0.drop 4 ++ h0.take 4 && a.internal.constants == SHA256.K.map BitVec.toNat)
  let regs := (List.range 9).foldl (fun t j => t.insert (8+j) (unknown (512+j) 2)) s.g
  let simd := (List.range 6).foldl (fun t j => t.insert j (unknown (576+j) 4)) s.q
  let h := ArmKeygen.block 32 4
  guard (frame s (s.sp+160) 64)
  let ns := {s with
    g := regs, q := (simd.insert 1 (h.take 4)).insert 0 (h.drop 4),
    m := write s.m (s.sp+160) (unknown 611 16), pc := pc+176, seeded := true}
  return {c with flags := none, machine := ns}

def code (a : Image) (pc : Nat) : Option Nat := do
  guard (pc%4 == 0)
  if region pc 4 a.publicEntry (4*a.publicWords.size) then a.publicWords[(pc-a.publicEntry)/4]?
  else if region pc 4 a.dispatcher (4*a.dispatchWords.size) then a.dispatchWords[(pc-a.dispatcher)/4]?
  else ArmVerifyBody.code (longImage a).core pc

def tick (a : Image) (ctxOK small sigOK : Bool) (st : State) : Option State := do
  let i := a.internal.core
  let p := i.p
  let n := p.n
  let c := st.ctrl
  let s := c.machine
  let pc := s.pc
  let reg := arg s
  let setS := fun t => {st with ctrl := {c with machine := t}}
  let regs := fun r => g s r
  let fresh := fun j => unknown j 2
  if pc == a.internal.core.body then
    guard (ctxOK && small && st.ctxTest && st.msgTest && st.frameLive && !st.shortCall &&
      (← reg 0) == i.gate.param && regs 1 == framePtr && regs 2 == frameLen && (← reg 3) == sk &&
      regs 4 == lenTag && (← reg 5) == base && (← reg 6) == 2*n)
    let t := put (clobber s 400) 0 (if sigOK then verdict else num 0)
    return {setS {t with pc := ← reg 30} with shortCall := true}
  if pc == LinkedApplePureFrame.image.entry then
    guard (st.ctxTest && st.msgTest && ctxOK && small && !st.frameLive &&
      regs 0 == fresh 0 && regs 1 == fresh 1 && regs 2 == fresh 4 && regs 3 == fresh 5)
    let out ← reg 8
    guard (frame s out 24)
    let t := {clobber s 300 with pc := ← reg 30,m := write s.m out (frameCap++framePtr++frameLen)}
    return {setS t with frameLive := true}
  if pc == i.free && !st.inLong then
    guard (st.frameLive && st.shortCall && regs 0 == framePtr && regs 1 == frameCap && (← reg 2) == 1)
    return {setS {clobber s 500 with pc := ← reg 30} with frameLive := false}
  if pc == a.digest then
    guard (st.inLong && st.sigTest && sigOK && c.actions.isEmpty && (← reg 1) == p.m && (← reg 2) == sk &&
      (← reg 3) == base && (← reg 4) == base+n && regs 5 == fresh 4 && regs 6 == fresh 5 &&
      regs 7 == fresh 0 && has s s.sp (fresh 1) && has s sk (ArmKeygen.block n 0) &&
      has s base (ArmKeygen.block n 1 ++ ArmKeygen.block n 2))
    let t ← ArmVerifyBody.writeVec s (← reg 0) digestCap digestPtr p.m
    return {st with ctrl := {c with
      machine := {clobber t 64 with pc := ← reg 30},
      epoch := 1, actions := [.hash], flags := none, liveHash := true}}
  if st.inLong && [i.xmss,i.fors,i.free,a.internal.seedStart].contains pc then
    return {st with ctrl := ← ArmSha2Verify.tick (longImage a) c}
  let w ← code a pc
  let next := {s with pc := pc+4}
  let cfg := ArmVerifyBody.config i
  if pc == a.segmented then
    guard (st.ctxTest && st.msgTest && ctxOK && !small && !st.inLong && (← reg 0) == i.gate.param &&
      regs 1 == fresh 0 && regs 2 == fresh 1 && regs 3 == fresh 4 && regs 4 == fresh 5 &&
      (← reg 5) == sk && regs 6 == lenTag && (← reg 7) == base && has s s.sp (num (2*n)))
    return {setS (← step cfg s w) with inLong := true}
  if !st.inLong || region pc 4 a.publicEntry (4*a.publicWords.size) then
    if w &&& 0xffc0001f == 0xf100001f then
      let imm := w/1024%4096
      let operand := regs (w/32%32)
      if imm == 255 then
        guard (!st.ctxTest && operand == fresh 5)
        return {setS {next with ls := some ctxOK} with ctxTest := true}
      guard (st.ctxTest && !st.msgTest && ctxOK && imm == 1023 && operand == fresh 1)
      return {setS {next with ls := some small} with msgTest := true}
    if w &&& 0xff000000 == 0xb4000000 then
      guard (st.frameLive && st.shortCall && regs (w%32) == frameCap)
      return setS next
    return setS (← step cfg s w (some ([],[])))
  if w &&& 0xffe0fc1f == 0xeb00001f && !st.sigTest then
    guard (regs (w/32%32) == lenTag && (← reg (w/65536%32)) == p.sigBytes)
    let t := (List.range 31).foldl (fun t r => if g t r == lenTag && sigOK then put t r (num p.sigBytes) else t) next
    return {st with sigTest := true, ctrl := {c with machine := t, flags := some (sigOK,false)}}
  if st.sigTest && sigOK && c.actions.isEmpty then
    if w &&& 0xff00001f == 0x54000009 || w &&& 0xffc0001f == 0xf100001f then
      return setS (← step cfg s w)
    if w == 0xa9c16088 then
      let ptr ← reg 4
      guard (ptr == base)
      let words ← read s.m (ptr+16) 16
      return setS (put (put (put next 4 (num (ptr+16))) 8 (words.take 2)) 24 (words.drop 2))
  if n == 16 && w == 0x6e200800 then return {st with ctrl := ← seed128 a c}
  if n == 16 && w == compare16Words.head! then
    guard ((← (List.range 6).mapM (fun j => code a (pc+4*j))) == compare16Words && c.layers == p.d &&
      cellBuffer s ((← reg 29)-160) (root n c.layers) &&
      has s (s.sp+40) ((ArmKeygen.block n 2).take 2) && has s (s.sp+48) ((ArmKeygen.block n 2).drop 2))
    let t := [8,9,10].foldl (fun t r => put t r (unknown (9300+r) 2)) next
    return {st with ctrl := {c with
      machine := {put t 0 verdict with pc := pc+24},
      actions := c.actions++[.compare], flags := none}}
  return {st with ctrl := ← ArmSha2Verify.tick (longImage a) c}

def init (a : Image) : State := Id.run do
  let i := a.internal.core
  let p := i.p
  let words := (List.range 9).map fun j =>
    ((i.gate.params.drop (4*j)).take 4).zipIdx.foldl (fun sum (b,k) => sum+b*256^k) 0
  let m := write (write (write {} i.gate.param words) sk (ArmKeygen.block p.n 0)) base (ArmKeygen.block p.n 1 ++ ArmKeygen.block p.n 2)
  let s := put (put {pc := a.publicEntry, m} 2 (num sk)) 6 (num base)
  return {ctrl := {machine := s}}

def run (a : Image) (ctxOK small sigOK : Bool) : Option Result := do
  let p := a.internal.core.p
  guard (a.internal.core.gate.params == parameterBytes p)
  let mut st := init a
  for _ in [:2500] do
    if st.ctrl.machine.pc == stop then break
    st ← tick a ctxOK small sigOK st
  let c := st.ctrl
  let s := c.machine
  guard (s.pc == stop && s.sp == stack && st.ctxTest && !st.frameLive && !c.liveHash &&
    (List.range 13).all (fun j => g s (18+j) == unknown (18+j) 2) &&
    (List.range 8).all (fun j => (q s (8+j)).take 2 == (unknown (40+j) 4).take 2))
  if !ctxOK then
    guard (!st.msgTest && !st.sigTest && !st.shortCall && !st.inLong && c.actions.isEmpty && g s 0 == num 0)
    return .contextRejected
  guard (st.msgTest && st.shortCall == small && st.inLong == !small && st.sigTest == !small)
  if !sigOK then
    guard (c.actions.isEmpty && g s 0 == num 0)
    return .signatureRejected
  guard (g s 0 == verdict)
  if small then
    guard c.actions.isEmpty
    return .framed
  guard (s.seeded && c.actions == ArmSha2Verify.expected p)
  return .segmented


/-- The short branch materializes the proven framing Vec. The segmented digest
consumes the same logical bytes as separate mode, context and message pieces. -/
def input (msg ctx : Bytes) (choices : Fin 8) : Bytes :=
  if h : ctx.length ≤ 255 ∧ msg.length ≤ 1023 then
    (ArmPureWrapper.Frame.ofAllocation msg ctx h.1 (by omega)
      (choices.val.testBit 0) (choices.val.testBit 1) (choices.val.testBit 2)).payload
  else withContext msg ctx

theorem input_eq (msg ctx : Bytes) (choices : Fin 8) : input msg ctx choices = withContext msg ctx := by
  unfold input
  split
  · exact ArmPureWrapper.Frame.payload_eq _
  · rfl

def evaluate (a : Image) (msg ctx sig : Bytes) :=
  run a (decide (ctx.length ≤ 255)) (decide (msg.length ≤ 1023)) (decide (sig.length = a.internal.core.p.sigBytes))

def verdictOf (r : Result) (core : Bool) := match r with
  | .contextRejected | .signatureRejected => false
  | .framed | .segmented => core

def verified {a : Image} {msg ctx sig pk} {choices : Fin 8}
    (v : ArmSha2Verify.Callees a.internal.core.p (input msg ctx choices) sig pk) :=
  (evaluate a msg ctx sig).map (fun r => verdictOf r
    (ArmSha2Verify.returned v (ArmSha2Verify.expected a.internal.core.p)))

theorem valid_eq {a : Image} {msg ctx sig pk} {choices : Fin 8}
    (paths : ∀ c m s, run a c m s = some (route c m s))
    (checked : ArmSha2Verify.run a.internal = some (ArmSha2Verify.expected a.internal.core.p))
    (row : a.internal.core.p.mdBytes+a.internal.core.p.treeBytes+a.internal.core.p.leafBytes ≤ a.internal.core.p.m)
    (v : ArmSha2Verify.Callees a.internal.core.p (input msg ctx choices) sig pk) :
    verified v = some (slhVerify a.internal.core.p msg sig ctx pk) := by
  have inner := (ArmSha2Verify.trace checked checked row v).eq_spec.trans
    (congrArg (fun m => slhVerifyInternal a.internal.core.p m sig pk) (input_eq msg ctx choices))
  have cond : (ctx.length > 255) ↔ ¬ctx.length ≤ 255 := by omega
  by_cases h : ctx.length ≤ 255 <;> by_cases m : msg.length ≤ 1023 <;>
    simp [verified,evaluate,paths,route,verdictOf,slhVerify,v.sigSize,h,m,inner,
      cond]

theorem malformed_eq {a : Image} (paths : ∀ c m s, run a c m s = some (route c m s))
    (msg ctx sig pk : Bytes) (bad : sig.length ≠ a.internal.core.p.sigBytes) (core : Bool) :
    (evaluate a msg ctx sig).map (fun r => verdictOf r core) = some (slhVerify a.internal.core.p msg sig ctx pk) := by
  have cond : (ctx.length > 255) ↔ ¬ctx.length ≤ 255 := by omega
  by_cases h : ctx.length ≤ 255 <;>
    simp [evaluate,paths,route,verdictOf,slhVerify,slhVerifyInternal,bad,h,
      cond]

theorem oversized_ctx {a : Image} (paths : ∀ c m s, run a c m s = some (route c m s))
    (msg ctx sig : Bytes) (h : ctx.length > 255) :
    evaluate a msg ctx sig = some .contextRejected := by
  simp [evaluate,paths,route,show ¬ctx.length ≤ 255 by omega]

end Spec.ArmSha2PublicVerify
