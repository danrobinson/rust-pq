import Spec.ArmSha2ReferenceCalls

/-! Successful long-message SHA-2 entry, prefix copy and both hash call interfaces.
    Byte provenance is independent of key, randomness, message and context values.
    The inline SHA loops between the three instruction windows are cutpoints. -/
namespace Spec.ArmSegmentedFrame
open ArmKeygen (addr signExt)

/-- Every symbolic byte has a distinct source and offset. Pointer and numeric
    arithmetic is permitted only on little-endian literal words, except for the
    explicit addition to the arbitrary valid context length. -/
inductive Atom where
  | lit (v : Nat) | key (i : Nat) | random (i : Nat) | ctxSize (i : Nat)
  | msgSize (i : Nat) | prefixSize (extra i : Nat) | unknown (r i : Nat)
deriving DecidableEq, Repr
abbrev Value := List Atom
def bytes (n : Nat) (f : Nat → Atom) := (List.range n).map f
def lit (v : Nat) (n : Nat := 8) := bytes n (fun i => .lit ((v / 256^i)%256))
def natV : Value → Option Nat
  | [] => some 0
  | .lit b :: rest => return b + 256*(← natV rest)
  | _ => none

structure Image where
  p : Params
  param : Nat
  record : List Nat
  entry : Nat
  memcpy : Nat
  continued : Nat
  digest : Nat
  words : Array Nat
  /-- Offsets are checked by executing through the exact target calls. -/
  copyEnd : Nat
  innerStart : Nat
  innerEnd : Nat
  digestStart : Nat
  digestEnd : Nat
structure State where
  pc : Nat
  sp : Nat
  g : Std.TreeMap Nat Value := {}
  q : Std.TreeMap Nat Value := {}
  mem : Std.TreeMap Nat Atom := {}
  cmp : Option (Bool × Bool) := none -- LS and HS
def stack := 0x200000
def key := ArmKeygen.base
def rand := ArmInternalSigner.rand
def ctx := 0x900000
def msg := ArmInternalSigner.msg
def out := ArmInternalSigner.descriptor
def g (s : State) (r : Nat) := if r == 31 then lit 0 else s.g.getD r (bytes 8 (.unknown r))
def q (s : State) (r : Nat) := s.q.getD r (bytes 16 (.unknown (32+r)))
def base (s : State) (r : Nat) := if r == 31 then some s.sp else natV (g s r)
def put (s : State) (r : Nat) (v : Value) := {s with g := s.g.insert r v}
def write (s : State) (a : Nat) (v : Value) :=
  {s with mem := v.zipIdx.foldl (fun m (b,i) => m.insert (a+i) b) s.mem}
def read (s : State) (a k : Nat) := (List.range k).mapM fun i => s.mem[a+i]?
def init (im : Image) := Id.run do
  let n := im.p.n
  let s : State := {pc := im.entry, sp := stack}
  let s := write (write (write s key (bytes (4*n) .key)) rand (bytes n .random)) im.param (im.record.map .lit)
  let vs := [lit im.param,lit msg,bytes 8 .msgSize,lit ctx,bytes 8 .ctxSize,lit key,lit (4*n),lit rand,lit out]
  return vs.zipIdx.foldl (fun s (v,r) => put s r v) s

def transfer (s : State) (ld simd : Bool) (r a k : Nat) : Option State := do
  if ld then
    let v ← read s a k
    return if simd then {s with q := s.q.insert r (v ++ lit 0 (16-k))}
           else put s r (v ++ lit 0 (8-k))
  guard (s.sp ≤ a && a+k ≤ stack)
  return write s a ((if simd then q s r else g s r).take k)

def step (s : State) (w : Nat) : Option State := do
  let t := {s with pc := s.pc+4}
  let mask := fun n => w &&& n
  let d := w%32
  let b := w/32%32
  let imm := w/1024%4096
  let ld := w/2^22%2 == 1
  if mask 0xffe0ffe0 == 0xaa0003e0 then
    return put t d (g s (w/65536%32))
  if mask 0xffc00000 == 0x91000000 || mask 0xffc00000 == 0xd1000000 then
    if b != 31 && g s b == bytes 8 .ctxSize then
      guard (d < 31 && mask 0xffc00000 == 0x91000000)
      return put t d (bytes 8 (.prefixSize imm))
    let a ← base s b
    let a := addr a (if w/2^30%2 == 0 then (imm : Int) else -(imm : Int))
    if d == 31 then
      guard (stack-2048 ≤ a && a ≤ stack && a%16 == 0)
      return {t with sp := a}
    return put t d (lit a)
  if mask 0xffc0001f == 0xf100001f then
    if g s b == bytes 8 .ctxSize then
      guard (255 < imm)
      return {t with cmp := some (true,false)}
    let a ← base s b
    return {t with cmp := some (a ≤ imm,a ≥ imm)}
  if mask 0xff000010 == 0x54000000 then
    let (ls,hs) ← s.cmp
    guard (w%16 == 9 || w%16 == 2)
    let taken := if w%16 == 9 then ls else hs
    return {t with pc := if taken then addr s.pc (4*signExt (w/32%2^19) 19) else t.pc}
  if mask 0xffe00000 == 0x52800000 then return put t d (lit (w/32%65536))
  if mask 0xffffffe0 == 0x6f00e400 then return {t with q := s.q.insert d (lit 0 16)}
  let a ← base s b
  let mode := mask 0xff800000
  if [0xa9000000,0xad000000,0xa9800000,0x6d800000].contains mode then
    let simd := mode == 0xad000000 || mode == 0x6d800000
    let k : Nat := if mode == 0xad000000 then 16 else 8
    let a := addr a (k * signExt (w/2^15%128) 7)
    let mut t := t
    if mode == 0xa9800000 || mode == 0x6d800000 then
      guard (b == 31 && stack-2048 ≤ a && a ≤ stack && a%16 == 0)
      t := {t with sp := a}
    let r := w/1024%32
    guard (!ld || d != r)
    let u ← transfer t ld simd d a k
    transfer u ld simd r (a+k) k
  else
    let kind := mask 0xffc00000
    let unscaled := mask 0xffc00c00
    let (simd,k,scaled) ←
      if [0x3d800000,0x3dc00000].contains kind then some (true,(16 : Nat),true)
      else if [0xfd000000,0xfd400000].contains kind then some (true,8,true)
      else if [0xf9000000,0xf9400000].contains kind then some (false,8,true)
      else if kind == 0x39000000 then some (false,1,true)
      else if [0x3c800000,0x3cc00000,0x3cc00c00].contains unscaled then some (true,16,false)
      else if unscaled == 0xf8000000 then some (false,8,false)
      else none
    let a := addr a (if scaled then (imm*k : Int) else signExt (w/4096%512) 9)
    let t ← transfer t ld simd d a k
    return if unscaled == 0x3cc00c00 then put t b (lit a) else t

/-- Requiring fall-through after each instruction prevents accidentally dropping
    a conditional branch, entering an omitted block or accepting a shorter path. -/
def window (im : Image) (s : State) (first last target : Nat) : Option State := do
  guard (first ≤ last && last < im.words.size && s.pc == im.entry+4*first)
  let mut t := s
  for i in [first:last] do
    guard (t.pc == im.entry+4*i)
    t ← step t (← im.words[i]?)
  let w ← im.words[last]?
  guard (t.pc == im.entry+4*last && w/2^26 == 0x25 && addr t.pc (4*signExt (w%2^26) 26) == target)
  return t

/-- Preserve only the forwarded argument registers, frame pointer and frame at
    the two inline-SHA cutpoints. Scratch values cannot supply a checked argument. -/
def cutpoint (n : Nat) (s : State) (pc : Nat) : State :=
  let live := if n == 16 then [20,21,22,23,24,25,26,29] else [20,21,23,24,25,29]
  let regs := (List.range 31).foldl
    (fun m r => if live.contains r then m else m.insert r (bytes 8 (.unknown (100+r)))) s.g
  {s with pc, cmp := none, q := {}, g := regs}

structure Layout where
  n : Nat
  frameBase : Nat
  outer : Nat
  inner : Nat
  state : Nat
  vec : Nat

def layout (n : Nat) : Option Layout :=
  match n with
  | 16 => some ⟨16,192,96,528,496,120⟩
  | 24 => some ⟨24,288,176,656,592,208⟩
  | 32 => some ⟨32,304,192,672,608,224⟩
  | _ => none

inductive Fragment where | random | zero | size | context | message deriving DecidableEq, Repr
structure Frame where
  inner : List Fragment
  digest : List Fragment
deriving DecidableEq, Repr

def atDigest (im : Image) : Option (State × Frame) := do
  let l ← layout im.p.n
  guard (im.record == ArmKeygen.parameterBytes im.p && im.p.family == .sha2 &&
    im.copyEnd < im.innerStart && im.innerEnd < im.digestStart)
  let s ← window im (init im) 0 im.copyEnd im.memcpy
  let pref := s.sp+l.frameBase
  -- The inlined ipad and opad block code consumes the staged SK.prf.
  let staged ← if l.n == 16 then read s (s.sp+64) 16
    else if l.n == 24 then do pure ((← read s (s.sp+80) 16) ++ (q s 8).take 8)
    else do pure ((← read s (s.sp+96) 16) ++ (← read s (s.sp+80) 16))
  guard (staged == bytes l.n (fun i => .key (l.n+i)))
  let hlen := if l.n == 16 then 32 else 64
  guard (ArmKeygen.disjoint pref (l.n+2+255) (s.sp+l.state) hlen &&
    ArmKeygen.disjoint pref (l.n+2+255) (s.sp+l.inner) hlen &&
    ArmKeygen.disjoint (s.sp+l.inner) hlen (s.sp+l.state) hlen)
  guard (g s 0 == lit (pref+l.n+2) && g s 1 == lit ctx && g s 2 == bytes 8 .ctxSize &&
    pref+l.n+2+255 ≤ stack && (← read s pref l.n) == bytes l.n .random &&
    (← read s (pref+l.n) 2) == [.lit 0,.ctxSize 0])
  let t ← window im (cutpoint l.n s (im.entry+4*im.innerStart)) im.innerStart im.innerEnd im.continued
  guard (g t 0 == lit (s.sp+l.inner) && g t 1 == lit (s.sp+l.state) &&
    g t 2 == lit (if l.n == 16 then 64 else 128) && g t 3 == lit pref &&
    g t 4 == bytes 8 (.prefixSize (l.n+2)) && g t 5 == lit msg && g t 6 == bytes 8 .msgSize)
  let u ← window im (cutpoint l.n t (im.entry+4*im.digestStart)) im.digestStart im.digestEnd im.digest
  guard (g u 0 == lit (s.sp+l.vec) && g u 1 == lit im.p.m && g u 2 == lit (s.sp+l.outer) &&
    g u 3 == lit (key+2*l.n) && g u 4 == lit (key+3*l.n) && g u 5 == lit ctx &&
    g u 6 == bytes 8 .ctxSize && g u 7 == lit msg && (← read u s.sp 8) == bytes 8 .msgSize)
  return (u,⟨[.random,.zero,.size,.context,.message],[.zero,.size,.context,.message]⟩)

def checked (im : Image) : Option Frame := (atDigest im).map Prod.snd

def evaluate (random ctx msg : Bytes) (fs : List Fragment) : Bytes :=
  fs.flatMap fun f => match f with
    | .random => random | .zero => [0] | .size => [BitVec.ofNat 8 ctx.length]
    | .context => ctx | .message => msg

def expected : Frame := ⟨[.random,.zero,.size,.context,.message],[.zero,.size,.context,.message]⟩

theorem framed {im f} (cert : checked im = some expected) (actual : checked im = some f)
    (random ctx msg : Bytes) :
    evaluate random ctx msg f.inner = random ++ withContext msg ctx ∧
    evaluate random ctx msg f.digest = withContext msg ctx := by
  rw [cert] at actual
  cases Option.some.inj actual
  simp [evaluate,expected,withContext,toByte]

end Spec.ArmSegmentedFrame
