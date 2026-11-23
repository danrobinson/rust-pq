import Spec.ArmVerifyLength
import Spec.ArmSignCoordinates
import Spec.ArmRootComparison

/-! Restricted interpreter for the linked SHAKE internal verification drivers.
The public wrapper and first H_msg call are replayed by ArmVerifyLength.hashEntry.
The remaining instructions read symbolic digest byte offsets, authorize each
callee against its actual arguments, and propagate opaque root/coordinate cells
to the final bytewise comparison and return. Unknown instruction forms fail. -/
namespace Spec.ArmVerifyBody
open ArmKeygen ArmVerifyLength
abbrev V := ArmSignCoordinates.V

structure Image where
  p : Params
  gate : Path
  hashPath : List (Nat × Nat)
  body : Nat
  words : Array Nat
  hmsg : Nat
  digits : Nat
  fors : Nat
  xmss : Nat
  free : Nat
  ht : Nat
  htWords : Array Nat

def config (im : Image) : Config := ⟨im.p.n,im.p.d,im.p.hp,im.gate.entry,0,im.gate.param,im.gate.params,true,.shake⟩
def digestPtr := 0x1000000
def digitPtr := 0x2000000
def digestCap := unknown 5000 2
def digitCap := unknown 5001 2
def digitBytes := unknown 5002 2
def verdict := [token 5003 0,0]
def tree (j : Nat) := [token (1000+j) 0,token (1000+j) 1]
def leaf (j : Nat) := [token (2000+j) 0,0]
def root (n j : Nat) := ArmKeygen.block n (100+j)

inductive Action where | hash | digits | fors | layer (j : Nat) | compare deriving DecidableEq, Repr
structure Control where
  machine : State
  actions : List Action := []
  liveHash : Bool := false
  liveDigits : Bool := false
  layers : Nat := 0
  flags : Option (Bool × Bool) := none
  expressions : List (Cells × V) := []
  epoch : Nat := 0

def arg (s : State) (r : Nat) := natVal (g s r)
def frame (s : State) (a n : Nat) := region a n s.sp (stack-s.sp) && a%4 == 0
def has (s : State) (a : Nat) (data : Cells) := read s.m a (4*data.length) == some data
def cellBuffer (s : State) (a : Nat) (v : Cells) := frame s a (4*v.length) && has s a v
def writeVec (s : State) (dst : Nat) (cap : Cells) (ptr len : Nat) : Option State := do
  guard (frame s dst 24)
  return {s with m := write s.m dst (cap ++ num ptr ++ num len)}

def action (im : Image) (c : Control) : Option Control := do
  let s := c.machine
  let a := arg s
  let p := im.p
  let n := p.n
  let orig := c
  let mut c := c
  let s ← if s.pc == im.hmsg then do
    guard (c.actions.isEmpty)
    c := {c with actions := [.hash], liveHash := true}
    writeVec s (← a 8) digestCap digestPtr p.m
  else if s.pc == im.digits then do
    guard (c.actions == [.hash] && c.liveHash && (← a 0) == digestPtr && (← a 1) == p.mdBytes &&
      (← a 2) == p.a && (← a 3) == p.k)
    c := {c with actions := c.actions ++ [.digits], liveDigits := true}
    writeVec s (← a 8) digitCap digitPtr p.k
  else if s.pc == im.fors then do
    guard (c.actions == [.hash,.digits] && c.liveDigits && (← a 0) == im.gate.param &&
      (← a 1) == digitPtr && (← a 2) == p.k && (← a 3) == sk+n && (← a 4) == p.forsSigBytes &&
      cellBuffer s (← a 5) (ArmKeygen.block n 1) &&
      cellBuffer s (← a 6) (tree 0 ++ [0,3,(leaf 0).head!,0,0]))
    let out ← a 8
    guard (frame s out n && disjoint out n (← a 5) n && disjoint out n (← a 6) 28)
    c := {c with actions := c.actions ++ [.fors]}
    pure {s with m := write s.m out (root n 0)}
  else if s.pc == im.xmss then do
    let j := c.layers
    guard (j < p.d && c.actions == [.hash,.digits,.fors] ++ (List.range j).map Action.layer &&
      (← a 0) == im.gate.param && g s 1 == leaf j &&
      (← a 2) == sk+n+p.forsSigBytes+j*p.xmssSigBytes && (← a 3) == p.xmssSigBytes &&
      cellBuffer s (← a 4) (root n j) && cellBuffer s (← a 5) (ArmKeygen.block n 1) &&
      cellBuffer s (← a 6) (tree j ++ [j,0,0,0,0]))
    let out ← a 8
    guard (frame s out n && disjoint out n (← a 4) n && disjoint out n (← a 5) n && disjoint out n (← a 6) 28)
    c := {c with layers := j+1, actions := c.actions ++ [.layer j]}
    pure {s with m := write s.m out (root n (j+1))}
  else if s.pc == im.free then do
    if (← a 0) == digestPtr then
      guard (c.liveHash && g s 1 == digestCap && (← a 2) == 1)
      c := {c with liveHash := false}
    else
      guard ((← a 0) == digitPtr && c.liveDigits && g s 1 == digitBytes && (← a 2) == 4)
      c := {c with liveDigits := false}
    pure s
  else none
  let ret ← arg orig.machine 30
  return {c with machine := {clobber s (64+64*c.epoch) with pc := ret}, epoch := c.epoch+1, flags := none}

/-- These five words implement equality of the two complete initialized
16-byte spans (including both 64-bit halves). This theorem checks the same
decoder as the standalone linked root comparison witness. -/
def compareWords : List Nat := [0xa97623a9,0xa9442beb,0xeb0b013f,0xfa4a0100,0x1a9f17e0]

theorem compareBytes (m : LinkedArm.RootComparison.ByteMemory) (s : LinkedArm.RootComparison.State) :
    LinkedArm.RootComparison.verdict compareWords (LinkedArm.RootComparison.load64 m) s =
      some (if LinkedArm.RootComparison.byteSlice m (s.regs 29 - 160) 16 =
        LinkedArm.RootComparison.byteSlice m (s.sp + 64) 16 then 1 else 0) := by
  simp [compareWords, LinkedArm.RootComparison.verdict, LinkedArm.RootComparison.step,
    LinkedArm.RootComparison.base, LinkedArm.RootComparison.operand, LinkedArm.RootComparison.write,
    LinkedArm.RootComparison.load64_eq, LinkedArm.RootComparison.byteSlice,
    List.range_succ, List.foldlM, Bool.and_eq_true, and_assoc,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

def wideCompare (n : Nat) : List Nat :=
  if n == 24 then [0xa94227e8,0xf94007ed,0xa9402daa,0xf9401bec,0xf94009ad,0xeb0a011f,0xfa4b0120,0xfa4d0180,0x1a9f17e0]
  else [0xa94227e8,0xf94007ef,0xa9402dea,0xa94337ec,0xa9413dee,0xeb0a011f,0xfa4b0120,0xfa4e0180,0xfa4f01a0,0x1a9f17e0]

theorem compareWideBytes (n : Nat) (width : n = 24 ∨ n = 32)
    (m : LinkedArm.RootComparison.ByteMemory) (s : LinkedArm.RootComparison.State) :
    LinkedArm.RootComparison.verdict (wideCompare n) (LinkedArm.RootComparison.load64 m) s =
      some (if LinkedArm.RootComparison.byteSlice m (s.sp + 32) n =
        LinkedArm.RootComparison.byteSlice m (LinkedArm.RootComparison.load64 m (s.sp + 8)) n then 1 else 0) := by
  rcases width with rfl | rfl <;>
    simp [wideCompare, LinkedArm.RootComparison.verdict, LinkedArm.RootComparison.step,
      LinkedArm.RootComparison.base, LinkedArm.RootComparison.operand, LinkedArm.RootComparison.write,
      LinkedArm.RootComparison.load64_eq, LinkedArm.RootComparison.byteSlice,
      List.range_succ, List.foldlM, Bool.and_assoc, Bool.and_eq_true, and_assoc,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The normalization rule carries the proof for its actual instruction list.
`lhs` and `rhs` are the source addresses read by the hardware comparison. -/
structure CertifiedComparison (n : Nat) where
  words : List Nat
  lhs : LinkedArm.RootComparison.State → LinkedArm.RootComparison.Word
  rhs : LinkedArm.RootComparison.ByteMemory → LinkedArm.RootComparison.State → LinkedArm.RootComparison.Word
  correct : ∀ m s, LinkedArm.RootComparison.verdict words (LinkedArm.RootComparison.load64 m) s =
    some (if LinkedArm.RootComparison.byteSlice m (lhs s) n =
      LinkedArm.RootComparison.byteSlice m (rhs m s) n then 1 else 0)

def cmp16 : CertifiedComparison 16 :=
  ⟨compareWords,fun s => s.regs 29-160,fun _ s => s.sp+64,compareBytes⟩
def cmp24 : CertifiedComparison 24 :=
  ⟨wideCompare 24,fun s => s.sp+32,fun m s => LinkedArm.RootComparison.load64 m (s.sp+8),
    compareWideBytes 24 (Or.inl rfl)⟩
def cmp32 : CertifiedComparison 32 :=
  ⟨wideCompare 32,fun s => s.sp+32,fun m s => LinkedArm.RootComparison.load64 m (s.sp+8),
    compareWideBytes 32 (Or.inr rfl)⟩

def value (c : Control) (r : Nat) : Option V :=
  if let some x := arg c.machine r then some (.num x)
  else c.expressions.lookup (g c.machine r)

def assign (im : Image) (c : Control) (r : Nat) (v : V) : Control := Id.run do
  let s := c.machine
  if let .num n := v then return {c with machine := put s r (num n)}
  let expected := ArmSignCoordinates.expected im.p
  let key := if v == expected.1 then tree 0 else if v == expected.2 then leaf 0
    else unknown (6000+c.expressions.length) 2
  return {c with machine := put s r key, expressions := (key,v)::c.expressions}

def coordOp (im : Image) (c : Control) (w : Nat) : Option Control := do
  let n := w/32%32
  let m := w/65536%32
  let src := ArmSignCoordinates.dst (ArmSignCoordinates.dst {} n (← value c n)) m (← value c m)
  let target ← ArmSignCoordinates.exec im.p src w
  return assign im c (w%32) (← ArmSignCoordinates.regs target (w%32))

def code (im : Image) (pc : Nat) : Option Nat := do
  guard (pc%4 == 0)
  if region pc 4 im.body (4*im.words.size) then im.words[(pc-im.body)/4]?
  else
    guard (region pc 4 im.ht (4*im.htWords.size))
    im.htWords[(pc-im.ht)/4]?

def tick (im : Image) (c : Control) : Option Control := do
  let s := c.machine
  let pc := s.pc
  if [im.hmsg,im.digits,im.fors,im.xmss,im.free].contains pc then return ← action im c
  let w ← code im pc
  let d := w%32
  let n := w/32%32
  let m := w/65536%32
  let imm := w/1024%4096
  let next := {s with pc := pc+4}
  let cont := {c with machine := next}
  let mask := fun k => w &&& k
  let a := arg s
  let reg := fun r => if r == 31 then some 0 else a r
  let set := fun r val => {cont with machine := put next r (num val)}
  let jump := fun (b : Bool) => {c with machine := {s with pc := if b then addr pc (4*signExt (w/32%2^19) 19) else pc+4}}
  if im.p.n != 16 && w == 0xa94227e8 then
    let seq := if im.p.n == 24 then cmp24.words else cmp32.words
    guard ((← (List.range seq.length).mapM (fun j => code im (pc+4*j))) == seq && c.layers == im.p.d)
    let pkRoot ← natVal (← read s.m (s.sp+8) 8)
    guard (cellBuffer s (s.sp+32) (root im.p.n c.layers) && cellBuffer s pkRoot (ArmKeygen.block im.p.n 2))
    let next := (List.range 8).foldl (fun t j => put t (8+j) (unknown (9008+j) 2)) next
    return {c with machine := {put next 0 verdict with pc := pc+4*seq.length},
                   actions := c.actions ++ [.compare], flags := none}
  if im.p.n == 16 && w == cmp16.words.head! then
    guard ((← (List.range 5).mapM (fun j => code im (pc+4*j))) == cmp16.words &&
      c.layers == im.p.d && cellBuffer s ((← a 29)-160) (root 16 c.layers) &&
      cellBuffer s (s.sp+64) (ArmKeygen.block 16 2))
    -- All comparison temporaries/flags are forgotten except the output W0.
    let next := [8,9,10,11].foldl (fun t r => put t r (unknown (9000+r) 2)) next
    return {c with machine := {put next 0 verdict with pc := pc+20}, actions := c.actions ++ [.compare], flags := none}
  if mask 0xff000010 == 0x54000000 then
    let (zero,carry) ← c.flags
    let cond ← match w%16 with
      | 1 => some (!zero) | 2 => some carry | 3 => some (!carry)
      | 8 => some (carry && !zero) | _ => none
    return jump cond
  if mask 0xff000000 == 0x34000000 || mask 0xff000000 == 0xb4000000 then
    let r := g s d
    -- Both allocated Vec capacities are at least their positive initialized length.
    if r == digestCap || r == digitCap then return jump false
    return jump ((← a d)%(if w/2^31 == 0 then radix else 2^64) == 0)
  if mask 0xfffffc00 == 0x38401400 then
    let ptr ← a n
    guard (c.liveHash && digestPtr ≤ ptr && ptr < digestPtr+im.p.m && n != d)
    return assign im {cont with machine := put next n (num (ptr+1))} d (.byte (ptr-digestPtr))
  if mask 0xffe0fc00 == 0x0a200000 && c.layers > 0 then
    guard (g s n == tree (c.layers-1) && (← a m)%radix == radix-2^im.p.hp)
    return {cont with machine := put next d (leaf c.layers)}
  if mask 0xffe0fc00 == 0x9ac02400 && c.layers > 0 then
    guard (g s n == tree (c.layers-1) && (← a m)%64 == im.p.hp)
    return {cont with machine := put next d (tree c.layers)}
  if [0xaa002000,0x9ac02000,0x9ac02400,0x0a200000].contains (mask 0xffe0fc00) then
    return ← coordOp im cont w
  if w == 0x92800009 then return set 9 (2^64-1)
  if w == 0xd2c00068 then return set 8 (3*radix)
  if w == 0xd37ef501 then
    guard (g s 8 == digitCap)
    return {cont with machine := put next 1 digitBytes}
  if mask 0xfffffc00 == 0x92401400 then return set d ((← a n)%64)
  if mask 0xffe00000 == 0x8b000000 then
    return set d (((← reg n)+((← reg m) <<< (w/1024%64)))%2^64)
  if mask 0x7fe08000 == 0x1b000000 then
    return set d (((← reg n)*(← reg m)+(← reg (w/1024%32)))%(if w/2^31 == 0 then radix else 2^64))
  if mask 0xffc0fc00 == 0x53007c00 then return set d (((← a n)%radix) >>> (w/65536%32))
  if mask 0xffe0fc00 == 0x4b000000 then return set d (((← reg n)+radix-(← reg m)%radix)%radix)
  if mask 0xffc00000 == 0x11000000 then return set d (((← a n)+imm)%radix)
  if mask 0x7fe0fc00 == 0x0b000000 then return set d (((← reg n)+(← reg m))%(if w/2^31 == 0 then radix else 2^64))
  if mask 0xffc00000 == 0xb1000000 || mask 0xffe0fc00 == 0xab000000 then
    let operand ← if mask 0xffc00000 == 0xb1000000 then some imm else reg m
    let v := (← a n)+operand
    let t := if d == 31 then cont else set d (v%2^64)
    return {t with flags := some (v%2^64 == 0, decide (v ≥ 2^64))}
  if mask 0xffc00000 == 0xf1000000 || mask 0xffe0fc00 == 0xeb000000 then
    let x ← a n
    let y ← if mask 0xffc00000 == 0xf1000000 then some imm else reg m
    let t := if d == 31 then cont else set d ((x+2^64-y)%2^64)
    return {t with flags := some (x == y, decide (x ≥ y))}
  return {cont with machine := ← step (config im) s w (some ([(im.gate.param,36),(base,2*im.p.n),(sk,im.p.n)],[]))}

def expected (p : Params) := [.hash,.digits,.fors] ++ (List.range p.d).map Action.layer ++ [.compare]

def init (im : Image) : Option Control := do
  let p := im.p
  guard ([16,24,32].contains p.n && p.hp ≤ 32 && p.h-p.h/p.d ≤ 64 && im.gate.params == parameterBytes p)
  let (s,args) ← hashEntry im.gate p.n p.sigBytes im.hmsg im.hashPath
  guard (args == expectedCall p.n)
  return {machine := s}

def run (im : Image) : Option (List Action) := do
  let mut c ← init im
  for _ in [:2048] do
    if c.machine.pc == stop then break
    c ← tick im c
  let s := c.machine
  guard (s.pc == stop && g s 0 == verdict && !c.liveHash && !c.liveDigits && s.sp == stack &&
    (List.range 13).all (fun i => g s (18+i) == unknown (18+i) 2) &&
    (List.range 8).all (fun i => (q s (8+i)).take 2 == (unknown (40+i) 4).take 2))
  return c.actions

/-- Interpret the coordinate tokens emitted by the initial mask and each pair
of LSR/BIC instructions. The cleared high bits leave the low hp bits. -/
def location (p : Params) (dg : Bytes) : Nat → Nat × Nat
  | 0 => (ArmSignCoordinates.eval dg (ArmSignCoordinates.expected p).1,
          ArmSignCoordinates.eval dg (ArmSignCoordinates.expected p).2)
  | j+1 => let t := (location p dg j).1
           (t >>> p.hp, t &&& (2^p.hp-1))

theorem wordLeaf (t hp : Nat) (width : hp ≤ 32) :
    (t % 2^32) &&& (2^hp-1) = t % 2^hp := by
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 width)]

theorem nextLocation (p : Params) (dg : Bytes) (j : Nat) :
    location p dg (j+1) = ((location p dg j).1 >>> p.hp, (location p dg j).1 % 2^p.hp) := by
  simp [location,Nat.and_two_pow_sub_one_eq_mod]

def nativeAddress (p : Params) (dg : Bytes) : Adrs :=
  {{Adrs.zero with tree := (location p dg 0).1}.setTypeAndClear FORS_TREE with keypair := (location p dg 0).2}

/-- Local contracts on the result of each checked call. Each layer receives
its own contiguous slice and the preceding layer's root. The native Boolean
return and the equality between the recovered and public roots are not inputs. -/
structure Callees (p : Params) (msg sig pk : Bytes) where
  digest : Bytes
  digits : List Nat
  roots : Nat → Bytes
  sigSize : sig.length = p.sigBytes
  keySize : pk.length = 2*p.n
  digestSize : digest.length = p.m
  rootSize : ∀ j, j ≤ p.d → (roots j).length = p.n
  hash : digest = Hmsg p (sig.take p.n) (Spec.block p pk 0) (Spec.block p pk 1) msg
  decode : digits = base2b (digest.take p.mdBytes) p.a p.k
  forest : roots 0 = LinkedArm.Signer.forsRoots p digits ((sig.drop p.n).take p.forsSigBytes)
    (Spec.block p pk 0) (nativeAddress p digest)
  layer : ∀ j, j < p.d → LinkedArm.Signer.LayerRoot p (roots j) (Spec.block p pk 0)
    ((sig.drop (p.n+p.forsSigBytes+j*p.xmssSigBytes)).take p.xmssSigBytes)
    (location p digest j).2 {Adrs.zero with layer := j, tree := (location p digest j).1} (roots (j+1))

/-- Interpret the tag returned in W0. The decoder produces that tag only for
the proven full-width byte comparison, and checks it survives cleanup and RET. -/
def returned {p msg sig pk} (v : Callees p msg sig pk) (events : List Action) : Bool :=
  if events.getLast? == some .compare then v.roots (events.filter (fun a => match a with
    | .layer _ => true | _ => false)).length == Spec.block p pk 1 else false

private theorem expectedReturn {p msg sig pk} (v : Callees p msg sig pk) :
    returned v (expected p) = (v.roots p.d == Spec.block p pk 1) := by
  have last : (expected p).getLast? = some .compare := List.getLast?_concat
  unfold returned
  rw [last]
  simp [expected,List.filter_map,Function.comp_def]

def trace {im msg sig pk events} (actual : run im = some events)
    (checked : run im = some (expected im.p))
    (row : im.p.mdBytes+im.p.treeBytes+im.p.leafBytes ≤ im.p.m)
    (v : Callees im.p msg sig pk) :
    LinkedArm.Signer.VerifyTrace im.p msg sig pk (returned v events) := by
  rw [checked] at actual
  cases Option.some.inj actual
  obtain ⟨t,l⟩ := ArmSignCoordinates.interpretation im.p v.digest (v.digestSize ▸ row)
  have ad : nativeAddress im.p v.digest = LinkedArm.Signer.forsAddress im.p v.digest := by
    simp only [nativeAddress,LinkedArm.Signer.forsAddress,location,t,l]
  apply LinkedArm.Signer.VerifyTrace.checked v.sigSize
  refine { digest := v.digest
           digits := v.digits
           forsRoot := v.roots 0
           digest_eq := v.hash
           indices := v.decode
           forest := ad ▸ v.forest
           layers := { states := fun j => (v.roots j,location im.p v.digest j)
                       start := ?_
                       recover := ?_
                       coords := ?_ }
           result := ?_ }
  · simp only [location,t,l]
  · intro j hj
    simpa only [List.drop_drop, Nat.add_comm (j*im.p.xmssSigBytes)] using v.layer j hj
  · intro j _
    exact nextLocation im.p v.digest j
  · exact expectedReturn v

end Spec.ArmVerifyBody
