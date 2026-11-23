import Spec.ArmSegmentedKernels

/-! Word-level long SHA-2 driver under inline HMAC/seed compression, segmented
    hash, FORS, hypertree, vector allocation and ABI contracts. -/
namespace Spec.ArmSegmentedSigner
open ArmKeygen ArmInternalSigner


structure Image where
  frame : ArmSegmentedFrame.Image
  hooks : List (Nat × Op)
  coordinate : Nat
  seed : Seed
  constants : Literals

def cfg (im : Image) : Config :=
  let f := im.frame
  ⟨f.p.n,f.p.d,f.p.hp,f.entry,0,f.param,f.record,false,im.seed⟩
def core (im : Image) : ArmInternalSigner.Image :=
  ⟨cfg im,im.frame.p,im.frame.entry,#[],im.frame.words,im.coordinate,im.hooks⟩

/-- Import a previously observed register or stack word. Unknown or mixed input
    bytes cannot turn into a literal pointer or another secret-key block. -/
def cell (n : Nat) (bs : ArmSegmentedFrame.Value) : Option Nat := do
  guard (bs.length == 4)
  if let some v := ArmSegmentedFrame.natV bs then return v
  match ← bs[0]? with
  | .unknown r i =>
    guard (i%4 == 0 && bs == ArmSegmentedFrame.bytes 4 (fun j => .unknown r (i+j)))
    return (unknown r (i/4+1))[i/4]!
  | .key i =>
    guard (n > 0 && i%4 == 0 && i+4 ≤ 4*n && bs == ArmSegmentedFrame.bytes 4 (fun j => .key (i+j)))
    return token (i/n) (i%n/4)
  | _ => none

def asCells (n : Nat) (v : ArmSegmentedFrame.Value) : Option Cells := do
  guard (v.length%4 == 0)
  (List.range (v.length/4)).mapM fun j => cell n ((v.drop (4*j)).take 4)

/-- Only these live slots pass through the SHA cutpoints. In particular, no
    capacity, output bytes, address or digest coordinates are imported from the
    contracts. The digest vector is created with the checked callee ABI. -/
def postDigest (im : Image) (u : ArmSegmentedFrame.State) : Option Control := do
  let f := im.frame
  let p := f.p
  let n := p.n
  let l ← ArmSegmentedFrame.layout n
  let mut s : State := {pc := u.pc+4, sp := u.sp}
  if n == 24 then
    -- The measured HMAC loops modify D8 and D9. Only the actual epilogue
    -- loads from the original saved slots may establish ABI restoration.
    s := {s with q := (s.q.insert 8 (unknown 2008 4)).insert 9 (unknown 2009 4)}
  for r in [19:30] do
    let v := (asCells n (ArmSegmentedFrame.g u r)).getD (unknown (700+r) 2)
    s := put s r v
  -- Only saved registers, the return slot, SK.seed, PK.seed are needed.
  let saved := if n == 24 then 112 else 96
  let skSlot := if n == 16 then 80 else if n == 24 then 112 else 128
  let pkSlot := if n == 16 then 16 else if n == 24 then 144 else 160
  let mut m := (init (cfg im)).m
  m := write m base (List.range 4 |>.flatMap (ArmKeygen.block n))
  for (a,k) in [(stack-saved,saved),(u.sp+8,8),(u.sp+skSlot,n),(u.sp+pkSlot,n)] do
    let bs ← ArmSegmentedFrame.read u a k
    m := write m a (← asCells n bs)
  -- R is the HMAC result in the checked x2 input slot of message::digest.
  let rSlot ← ArmSegmentedFrame.natV (ArmSegmentedFrame.g u 2)
  guard (rSlot == u.sp+l.outer && stackOK s rSlot n)
  m := write m rSlot (randomizer n)
  if n == 16 then
    -- HMAC code also spills the real SHA-256 IV for the narrow seed block.
    let h := SHA256.H0.map BitVec.toNat
    m := write m (u.sp+48) (h.take 4 ++ h.drop 4)
    s := put (put s 27 (num 0x1000d5000)) 28 (num 0x1000d5000)
  s := {s with m}
  let dst ← ArmSegmentedFrame.natV (ArmSegmentedFrame.g u 0)
  let c : Control := {machine := put s 8 (num dst), crypto := sha2Schedule.take 2}
  let c ← newVec c digestID p.m 1
  return {c with machine := {clobber c.machine 960 with pc := u.pc+4}}

/-- Coordinate decoder certifies integer register transformations, the tree/type
    store and the narrow path's interleaved vector loads before materialization. -/
def coordinates (im : Image) (c : Control) : Option Control := do
  let f := im.frame
  let p := f.p
  let n := p.n
  let narrow := n == 16
  let s := c.machine
  let dg ← heap c digestID
  let dr := if narrow then 20 else 21
  let pr := if narrow then 21 else 20
  guard (!c.coord && c.crypto == sha2Schedule.take 2 && (← arg s dr) == dg.ptr &&
    (← arg s 2) == p.m && (← arg s pr) == f.param && (← arg s 11) == p.a &&
    (← arg s 9) == p.k && (← arg s 8) == p.hp && (← arg s 10) == 7)
  let j := (s.pc-f.entry)/4
  let count := if narrow then 45 else 39
  let words := f.words.extract j (j+count)
  guard (ArmSignCoordinates.result p words true true == some (ArmSignCoordinates.expected p))
  -- Bind the effective address and the source registers of the side-effecting STP.
  let store := if narrow then 0xa90a2ff8 else if n == 24 then 0xa9102bf9 else 0xa9112bf9
  guard (words[if narrow then 41 else 37]? == some store)
  let slot := s.sp+8*(store/32768%128)
  guard (stackOK s slot 16)
  let dead := [1,8,9,10,11,12,13,14]
  let s := dead.foldl (fun st r => put st r (unknown (1500+r) 2)) s
  let mut s := put (put (put s 23 (num p.mdBytes)) (if narrow then 24 else 25) tree) (if narrow then 25 else 26) leaf
  if narrow then
    s := put s 9 (num 0)
    s ← transfer (cfg im) s true true 0 (s.sp+16) 16
    s ← transfer (cfg im) s true true 5 (s.sp+48) 16
    s ← transfer (cfg im) s true true 4 (s.sp+64) 16
  return {c with machine := {s with m := write s.m slot (tree ++ num (3*2^32)), pc := s.pc+4*count, ls := none}, coord := true}

def narrowSeedWords : List Nat := [
  0x6e200800, 0x6f00e401, 0xad0607e0, 0x910303e8, 0xd000036a, 0x9111c14a, 0xad0707e1, 0x1400000a,
  0x3ce97941, 0x4ea08421, 0x4ea51ca0, 0x5e014080, 0x5e0150a4, 0x4ea01c05, 0xaa0b03e9, 0xf100417f,
  0x54000240, 0x9240052c, 0x3cec7900, 0x9100052b, 0xf100313f, 0x54fffe62, 0x9240056d, 0x3ced7901,
  0x4ea01c02, 0x5e282822, 0x5100052d, 0xd27f018e, 0x3cee7901, 0x924005ad, 0x3ced7903, 0x5e036022,
  0x3cac7902, 0x17ffffe7, 0x3dc3d381, 0x4ea18400, 0x3dc3cf61, 0x4ea18481]

def seedBlock (im : Image) (c : Control) : Option Control := do
  let .inlined start words iv rounds := im.seed | none
  let s := c.machine
  let f := im.frame
  let h := SHA256.H0.map BitVec.toNat
  let j := (start-f.entry)/4
  guard (f.p.n == 16 && s.pc == 0x10006e2a0 && s.pc == start && !s.seeded &&
    c.coord && c.crypto == sha2Schedule.take 2 && words == narrowSeedWords &&
    (f.words.extract j (j+words.length)).toList == words && iv == h.drop 4 ++ h.take 4 &&
    rounds == SHA256.K.map BitVec.toNat && q s 5 == h.take 4 && q s 4 == h.drop 4 &&
    q s 0 == ArmKeygen.block 16 2 && (← arg s 9) == 0 &&
    (← arg s 27) == 0x1000d5000 && (← arg s 28) == 0x1000d5000)
  let ring := s.sp+192
  guard (stackOK s ring 64)
  let regs := (List.range 6).foldl (fun t i => t.insert (8+i) (unknown (1700+i) 2)) s.g
  let simd := (List.range 6).foldl (fun t i => t.insert i (unknown (1750+i) 4)) s.q
  let dg := ArmKeygen.block 32 15
  let t := {s with g := regs, q := (simd.insert 0 (dg.take 4)).insert 1 (dg.drop 4)}
  let s := {t with m := write s.m ring (unknown 1800 16), pc := s.pc+4*words.length, ls := none, seeded := true}
  return {c with machine := s, crypto := c.crypto ++ [.seed]}

def tick (im : Image) (profile : Nat) (c : Control) : Option Control := do
  let s := c.machine
  if s.pc == im.coordinate then return ← coordinates im c
  if let .inlined entry .. := im.seed then
    if s.pc == entry then return ← seedBlock im c
  if let some op := im.hooks.lookup s.pc then return ← call (core im) profile c op
  let f := im.frame
  guard (region s.pc 4 f.entry (4*f.words.size) && s.pc%4 == 0)
  let w ← f.words[(s.pc-f.entry)/4]?
  if w == 0x6cc723e9 then -- LDP D9,D8,[SP],#112 (SHA2-192)
    guard (f.p.n == 24 && s.sp == stack-112)
    let t ← transfer (cfg im) s true true 9 s.sp 8
    let t ← transfer (cfg im) t true true 8 (s.sp+8) 8
    return {c with machine := {t with sp := stack, pc := s.pc+4}}
  return {c with machine := ← ordinary (core im) c w}

def run (im : Image) (profile : Nat) : Option (ArmSegmentedFrame.Frame × Observation) := do
  guard (profile < 4 && pinned im.frame im.constants)
  let (u,frame) ← ArmSegmentedFrame.atDigest im.frame
  let mut c ← postDigest im u
  for _ in [:512] do
    if c.machine.pc == stop then break
    c ← tick im profile c
  let s := c.machine
  let p := im.frame.p
  guard (s.pc == stop && s.sp == stack && g s 30 == unknown 30 2 && c.heaps.isEmpty &&
    c.output != 0 && (← usize s descriptor) == c.cap && (← usize s (descriptor+8)) == c.output &&
    (← usize s (descriptor+16)) == total p && c.cap ≥ total p && has s c.output (randomizer p.n))
  guard (((List.range 12).map (·+18)).all (fun r => g s r == unknown r 2))
  guard (((List.range 8).map (·+8)).all (fun r => (q s r).take 2 == (unknown (32+r) 4).take 2))
  return (frame,⟨c.crypto,.r :: c.parts⟩)

def expected := (ArmSegmentedFrame.expected,ArmInternalSigner.Sha2.expected)

theorem frames {im profile f obs} (actual : run im profile = some (f,obs))
    (cert : run im profile = some expected) (random ctx msg : Bytes) :
    ArmSegmentedFrame.evaluate random ctx msg f.inner = random ++ withContext msg ctx ∧
    ArmSegmentedFrame.evaluate random ctx msg f.digest = withContext msg ctx := by
  have eq := congrArg Prod.fst (Option.some.inj (actual.symm.trans cert))
  change f = ArmSegmentedFrame.expected at eq
  cases eq
  simp [ArmSegmentedFrame.evaluate,ArmSegmentedFrame.expected,withContext,toByte]

/-- Construct the structured trace from the actual returned layout, using
    local callee data for the message read at the segmented digest call. -/
def signature {im profile frame obs ctx msg sk random}
    (actual : run im profile = some (frame,obs)) (cert : run im profile = some expected)
    (row : im.frame.p.mdBytes+im.frame.p.treeBytes+im.frame.p.leafBytes ≤ im.frame.p.m)
    (v : ArmInternalSigner.Sha2.Callees im.frame.p
      (ArmSegmentedFrame.evaluate random ctx msg frame.digest) sk random) :
    LinkedArm.Signer.Sha2.Signature im.frame.p (withContext msg ctx) sk random
      (ArmInternalSigner.Sha2.materialize v obs) := by
  have t := ArmInternalSigner.Sha2.traceOfObservation
    (congrArg Prod.snd (Option.some.inj (actual.symm.trans cert))) row v
  exact (frames actual cert random ctx msg).2 ▸ t

/-- Total for the modeled successful allocation profiles and a valid long input.
    The structured cryptographic values are computed from the reference functions. -/
theorem referenceResult {im profile}
    (cert : run im profile = some expected) (row : im.frame.p ∈ LinkedArm.NativeSession.sha2Sets)
    (msg ctx sk random : Bytes) (keySize : sk.length = 4*im.frame.p.n)
    (randomSize : random.length = im.frame.p.n) (validCtx : ctx.length ≤ 255) (_long : 1024 ≤ msg.length) :
    (run im profile).map (fun (f,o) => ArmInternalSigner.Sha2.materialize
      (LinkedArm.NativeSession.referenceSha2Signer row (ArmSegmentedFrame.evaluate random ctx msg f.digest)
        sk random keySize randomSize) o) = slhSign im.frame.p msg ctx sk random := by
  let p := im.frame.p
  have rows : p.Valid ∧ p.family = .sha2 := by
    change p ∈ LinkedArm.NativeSession.sha2Sets at row
    simp only [LinkedArm.NativeSession.sha2Sets,List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with h|h|h|h|h|h <;> rw [h] <;> exact ⟨by constructor <;> decide, by decide⟩
  let v := LinkedArm.NativeSession.referenceSha2Signer row
    (ArmSegmentedFrame.evaluate random ctx msg expected.1.digest) sk random keySize randomSize
  have t := signature cert cert rows.1.m_eq.symm.le v
  rw [cert]
  simpa [expected,slhSign,show ¬ctx.length > 255 by omega,v] using congrArg some (t.eq_spec rows.2)

#print axioms signature
#print axioms referenceResult
end Spec.ArmSegmentedSigner
