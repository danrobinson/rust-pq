import Spec.ArmKeygen

/-! Abstract execution of the linked internal verifier's public ABI wrapper, size
calculation and malformed-signature return. Incoming registers are independent
arbitrary two-cell words. In particular X3 is the caller's exact signature length.
Only moves and spill/reload can transport an opaque input. Arithmetic requires
literal operands. The comparison records the unsigned 64-bit condition on X3;
the equal edge ends at the actual fallthrough PC. -/
namespace Spec.ArmVerifyLength
open ArmKeygen

structure Path where
  entry : Nat
  param : Nat
  params : List Nat
  before : List (Nat × Nat)
  cmp : Nat × Nat
  branch : Nat × Nat
  reject : List (Nat × Nat)
deriving Repr

private def config (p : Path) : Config :=
  ⟨0,0,0,p.entry,0,p.param,p.params,true,.shake⟩

private def start (p : Path) : State :=
  let words := (List.range 9).map fun i =>
    ((p.params.drop (4*i)).take 4).zipIdx.foldl (fun a (b,j) => a+b*256^j) 0
  {pc := p.entry, m := write {} p.param words}

private def number (s : State) (r : Nat) : Option Nat :=
  if r == 31 then some 0 else natVal (g s r)

/-- This decoder admits only straight-line operations, tail B, RET, and bounded
stack/parameter transfers. No function calls or message, key or signature reads. -/
private def op (c : Config) (s : State) (item : Nat × Nat) : Option State := do
  let (pc,w) := item
  guard (pc == s.pc && pc % 4 == 0 && w < 2^32)
  let d := w % 32
  let n := w / 32 % 32
  let m := w / 65536 % 32
  let next := {s with pc := pc+4}
  if w &&& 0x7fe08000 == 0x1b000000 then -- 32/64-bit MADD
    guard (d < 31)
    let a ← number s n
    let b ← number s m
    let e ← number s (w / 1024 % 32)
    return put next d (num ((a*b+e) % (if w/2^31 == 0 then 2^32 else 2^64)))
  if w &&& 0xffe00000 == 0x8b000000 then -- ADD shifted register (LSL)
    guard (d < 31)
    let a ← number s n
    let b ← number s m
    return put next d (num ((a + b*2^(w/1024%64)) % 2^64))
  let mem := [0xa9000000,0x29000000,0xf9000000].contains (w &&& 0xff800000)
  if mem then
    let a ← baseVal s n
    guard (a == c.param && w/2^22%2 == 1 || decide (s.sp ≤ a ∧ a ≤ stack))
  else
    guard (w &&& 0xffe0ffe0 == 0xaa0003e0 || w &&& 0xffc00000 == 0x91000000 ||
      w &&& 0xffc00000 == 0xd1000000 || w &&& 0x9f000000 == 0x90000000 ||
      w &&& 0xffe00000 == 0x52800000 || w &&& 0xfc000000 == 0x14000000 ||
      w == 0xd65f03c0)
  step c s w

structure Summary where
  length : Nat
  equalPC : Nat
  unequalReturn : Bool
deriving BEq, DecidableEq, Repr

def inspect (p : Path) : Option Summary := do
  guard (p.params.length == 36 && p.params.all (· < 256))
  let initial := start p
  let s ← p.before.foldlM (op (config p)) initial
  let (pc,cmp) := p.cmp
  -- CMP Xn, Xm (unshifted): Xn must be exactly the incoming public X3.
  guard (s.pc == pc && pc % 4 == 0 && cmp < 2^32 && cmp &&& 0xffe0fc1f == 0xeb00001f &&
    g s (cmp/32%32) == unknown 3 2)
  let threshold ← number s (cmp/65536%32)
  let (bpc,b) := p.branch
  guard (bpc == pc+4 && b < 2^32 && b &&& 0xff00001f == 0x54000001)
  let target := addr bpc (4*signExt (b/32%2^19) 19)
  let last ← p.reject.foldlM (op (config p)) {s with pc := target}
  guard (last.pc == stop && last.sp == stack && (List.range 13).all
    (fun i => g last (18+i) == g initial (18+i)))
  let result ← natVal (g last 0)
  guard (result ≤ 1)
  return ⟨threshold, bpc+4, result == 1⟩

inductive Outcome where
  | continued (pc : Nat)
  | returned (value : Bool)
deriving DecidableEq, Repr

/-- Specialize the checked compare/branch summary to a caller's register value. -/
def execute (path : Path) (length : Nat) : Option Outcome :=
  if length < 2^64 then do
    let t ← inspect path
    return if length = t.length then .continued t.equalPC else .returned t.unequalReturn
  else none

theorem acceptedEdge {p : Params} {path next}
    (checked : inspect path = some ⟨p.sigBytes,next,false⟩) (fits : p.sigBytes < 2^64) :
    execute path p.sigBytes = some (.continued next) := by simp only [execute, fits, ↓reduceIte, checked]; simp

/-- The linked conditional and return establish the premise of the actual
`wrongLength` constructor, without a supplied assumption that the result is false. -/
def toVerifyTrace {p : Params} {path next}
    (checked : inspect path = some ⟨p.sigBytes,next,false⟩)
    (msg sig pk : Bytes) (v : Bool)
    (actual : execute path sig.length = some (.returned v)) :
    LinkedArm.Signer.VerifyTrace p msg sig pk v := by
  by_cases fits : sig.length < 2^64
  · by_cases same : sig.length = p.sigBytes
    · simp only [execute, fits, ↓reduceIte, checked] at actual
      simp [same] at actual
    · simp only [execute, fits, ↓reduceIte, checked] at actual
      simp [same] at actual
      cases actual
      exact .wrongLength same
  · simp only [execute, fits, ↓reduceIte, reduceCtorEq] at actual

theorem rejects {p : Params} {path next}
    (checked : inspect path = some ⟨p.sigBytes,next,false⟩)
    (sig : Bytes) (fits : sig.length < 2^64) (bad : sig.length ≠ p.sigBytes) :
    execute path sig.length = some (.returned false) := by
  simp only [execute, fits, ↓reduceIte, checked]
  simp [bad]

structure HashCall where
  randomizer : Cells
  publicSeed : Cells
  publicRoot : Cells
deriving DecidableEq, Repr

def expectedCall (n : Nat) : HashCall := ⟨ArmKeygen.block n 0, ArmKeygen.block n 1, ArmKeygen.block n 2⟩

/-- Replay the equal-length edge, from the public ABI to the actual BL target.
The signature and public key start at disjoint modeled locations. Message pointer
and length remain independent opaque register values. The signature suffix need
not be materialized: a read from an uninitialized cell fails. -/
def hashCall (p : Path) (n sigLen entry : Nat) (tail : List (Nat × Nat)) : Option HashCall := do
  let gate ← inspect p
  guard (gate.length == sigLen && n % 4 == 0 && n ≤ 32)
  let c := {config p with n := n}
  let s := start p
  let s := put (put (put s 2 (num sk)) 3 (num sigLen)) 4 (num base)
  let m := write (write s.m sk (ArmKeygen.block n 0)) base (ArmKeygen.block n 1 ++ ArmKeygen.block n 2)
  let s ← p.before.foldlM (op c) {s with m := m}
  guard (s.pc == p.cmp.1 && (← number s (p.cmp.2/32%32)) == sigLen &&
     (← number s (p.cmp.2/65536%32)) == sigLen)
  let s ← tail.foldlM (fun s (pc,w) => do
    guard (s.pc == pc && pc % 4 == 0 && w < 2^32)
    -- BL, B.LS and CMP immediate; loads/stores are restricted to initialized
    -- input and stack cells by the shared decoder.
    if w &&& 0xfc000000 == 0x94000000 || w &&& 0xff00001f == 0x54000009 ||
       w &&& 0xffc0001f == 0xf100001f then step c s w
    else if [0xad000000,0x3d800000,0xf9000000].contains (w &&& 0xff800000) ||
          w &&& 0xff800c00 == 0x3c800000 then
      if w/2^22%2 == 0 then
        let a ← baseVal s (w/32%32)
        guard (s.sp ≤ a && a ≤ stack)
      step c s w
    else op c s (pc,w)) {s with pc := gate.equalPC}
  let (lastPc,lastWord) ← tail.getLast?
  guard (lastWord &&& 0xfc000000 == 0x94000000 && s.pc == entry &&
    (← number s 30) == lastPc+4 && (← number s 0) == p.param &&
    g s 4 == unknown 0 2 && g s 5 == unknown 1 2)
  let out ← number s 8
  let r ← number s 1
  let seed ← number s 2
  let root ← number s 3
  guard (region out 24 s.sp (stack-s.sp) && disjoint r n out 24 &&
    disjoint seed n out 24 && disjoint root n out 24)
  return ⟨← read s.m r n, ← read s.m seed n, ← read s.m root n⟩

def hashSources (p : Params) (sig pk : Bytes) : Nat → Bytes
  | 0 => sig.take p.n
  | 1 => Spec.block p pk 0
  | 2 => Spec.block p pk 1
  | _ => []

/-- The named H_msg contract applied to the buffers read at the machine call
yields precisely the digest premise of VerifyBody. -/
theorem digestPremise {p : Params} {path entry tail call}
    (checked : hashCall path p.n p.sigBytes entry tail = some (expectedCall p.n))
    (actual : hashCall path p.n p.sigBytes entry tail = some call)
    (msg sig pk digest : Bytes) (sigSize : p.n ≤ sig.length) (pkSize : 2*p.n ≤ pk.length)
    (multiple : p.n % 4 = 0) (bound : p.n ≤ 32)
    (target : let v := interpret (hashSources p sig pk)
      digest = Hmsg p (bytes v call.randomizer) (bytes v call.publicSeed) (bytes v call.publicRoot) msg) :
    digest = Hmsg p (sig.take p.n) (Spec.block p pk 0) (Spec.block p pk 1) msg := by
  rw [checked] at actual
  cases Option.some.inj actual
  let src := hashSources p sig pk
  have size0 : (src 0).length = p.n := by simp [src,hashSources,Nat.min_eq_left sigSize]
  have size1 : (src 1).length = p.n := by
    simp [src,hashSources,Spec.block,Nat.min_eq_left (show p.n ≤ pk.length by omega)]
  have size2 : (src 2).length = p.n := by
    simp [src,hashSources,Spec.block,Nat.min_eq_left (show p.n ≤ pk.length - p.n by omega)]
  change digest = Hmsg p (bytes (interpret src) (ArmKeygen.block p.n 0))
    (bytes (interpret src) (ArmKeygen.block p.n 1)) (bytes (interpret src) (ArmKeygen.block p.n 2)) msg at target
  rw [bytes_block size0 multiple bound, bytes_block size1 multiple bound, bytes_block size2 multiple bound] at target
  exact target

end Spec.ArmVerifyLength
