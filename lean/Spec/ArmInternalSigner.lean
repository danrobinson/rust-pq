import Spec.ArmSignCoordinates

namespace Spec.ArmInternalSigner
open ArmKeygen
inductive Op where
  | absorb | finish | hmsg | digits | fors | recover | ht | reserve | copy | free
deriving DecidableEq, Repr
structure Image where
  cfg : Config
  p : Params
  body : Nat
  entryWords : Array Nat
  bodyWords : Array Nat
  coordinates : Nat
  hooks : List (Nat × Op)
structure Heap where
  id : Nat
  ptr : Nat
  count : Nat
  align : Nat
deriving DecidableEq, Repr
inductive Part where | r | fors | ht deriving DecidableEq,Repr
structure Control where
  machine : State
  crypto : List Op := []
  serial : Nat := 0
  heaps : List Heap := []
  parts : List Part := [] -- bulk-copy provenance; R remains in cell-addressable memory
  output : Nat := 0
  cap : Nat := 0
  epoch : Nat := 0
  coord : Bool := false

def schedule := [Op.absorb,.absorb,.absorb,.finish,.hmsg,.digits,.fors,.digits,.recover,.ht]
def rand := 0x600000
def msg := 0x700000
def msgSize := unknown 220 2 -- arbitrary slice length, passed through both consumers
def descriptor := 0x800000
def buf (i : Nat) := 0x1000000 + i*0x10000
def randomizer (n : Nat) := ArmKeygen.block n 6
def spongeState (i : Nat) := ArmKeygen.block 208 (8+i)
def root (n : Nat) := ArmKeygen.block n 7
def tree := [token 13 0, token 13 1]
def leaf := [token 13 2,0]
def digestID := 1
def forsID := 3
def htID := 5
def htLen (p : Params) := p.d*p.xmssSigBytes
def total (p : Params) := p.n+p.forsSigBytes+htLen p

def initial (im : Image) : Control := Id.run do
  let c := im.cfg
  let mut s := init c
  s := {s with m := write (write s.m base (List.range 4 |>.flatMap (ArmKeygen.block c.n))) rand (ArmKeygen.block c.n 4)}
  s := put (put (put (put (put s 0 (num msg)) 1 msgSize) 2 (num base)) 3 (num rand)) 8 (num descriptor)
  return {machine := s}

def arg (s : State) (i : Nat) := natVal (g s i)
def stackOK (s : State) (a k : Nat) := region a k s.sp (stack-s.sp) && a%4 == 0
def locations (p : Params) (c : Control) : Regions :=
  ([(base,4*p.n),(rand,p.n)], [(descriptor,24)] ++
    (if c.output == 0 then [] else [(c.output,p.n)]))

def heap (c : Control) (id : Nat) := c.heaps.find? (fun h => h.id == id)
def usize (s : State) (a : Nat) : Option Nat := do natVal (← read s.m a 8)
def vec (s : State) (dst cap ptr len : Nat) : Option State := do
  guard (stackOK s dst 24)
  return {s with m := write s.m dst (num cap ++ num ptr ++ num len)}
def newVec (c : Control) (id len align : Nat) : Option Control := do
  guard ((heap c id).isNone && len > 0 && len*align ≤ 0x10000)
  let ptr := buf (c.serial+1)
  let s ← vec c.machine (← arg c.machine 8) len ptr len
  return {c with machine := s, serial := c.serial+1, heaps := ⟨id,ptr,len,align⟩ :: c.heaps}
def has (s : State) (a : Nat) (v : Cells) := read s.m a (4*v.length) == some v

def inputHas (p : Params) (s : State) (a : Nat) (v : Cells) :=
  let k := 4*v.length
  (stackOK s a k || region a k base (4*p.n) || region a k rand p.n) && has s a v

def call (im : Image) (profile : Nat) (c : Control) (op : Op) : Option Control := do
  let p := im.p
  let n := p.n
  let s := c.machine
  let ret ← arg s 30
  let a := arg s
  let old := c.crypto.length
  let mut c := c
  if !([Op.reserve,.copy,.free].contains op) then
    guard (schedule[old]? == some op)
    c := {c with crypto := c.crypto ++ [op]}
  let s ← match op with
    | .absorb => do
      let dst ← a 0
      guard (stackOK s dst 208 && has s dst (if old == 0 then List.replicate 52 0 else spongeState old))
      if old < 2 then
        guard ((← a 2) == n && inputHas p s (← a 1) (ArmKeygen.block n (if old == 0 then 1 else 4)))
      else guard ((← a 1) == msg && g s 2 == msgSize)
      pure {s with m := write s.m dst (spongeState (old+1))}
    | .finish => do
      let ctx ← a 0
      let dst ← a 1
      guard (stackOK s ctx 208 && stackOK s dst n && disjoint dst n ctx 208 && has s ctx (spongeState 3) && (← a 2) == n)
      pure {s with m := write (write s.m ctx (spongeState 4)) dst (randomizer n)}
    | .hmsg => do
      guard ((← a 0) == im.cfg.param && inputHas p s (← a 1) (randomizer n) &&
        inputHas p s (← a 2) (ArmKeygen.block n 2) && inputHas p s (← a 3) (ArmKeygen.block n 3) && (← a 4) == msg && g s 5 == msgSize)
      c ← newVec c digestID p.m 1
      pure c.machine
    | .digits => do
      let dg ← heap c digestID
      guard (c.coord && (← a 0) == dg.ptr && (← a 1) == p.mdBytes && (← a 2) == p.a && (← a 3) == p.k)
      c ← newVec c 2 p.k 4
      pure c.machine
    | .fors | .recover => do
      let ds ← heap c 2
      guard ((← a 0) == im.cfg.param && (← a 1) == ds.ptr && (← a 2) == p.k)
      let signing := op == .fors
      let ad ← a (if signing then 5 else 6)
      guard (stackOK s ad 28 && has s ad (tree ++ [0,3] ++ [leaf.head!,0,0]))
      if signing then
        guard (inputHas p s (← a 3) (ArmKeygen.block n 0) && inputHas p s (← a 4) (ArmKeygen.block n 2))
        c ← newVec c forsID p.forsSigBytes 1
        pure c.machine
      else
        let f ← heap c forsID
        let dst ← a 8
        guard ((← a 3) == f.ptr && (← a 4) == f.count && inputHas p s (← a 5) (ArmKeygen.block n 2) && stackOK s dst n)
        pure {s with m := write s.m dst (root n)}
    | .ht => do
      guard ((← a 0) == im.cfg.param && inputHas p s (← a 1) (root n) && inputHas p s (← a 2) (ArmKeygen.block n 0) &&
        inputHas p s (← a 3) (ArmKeygen.block n 2) && g s 4 == tree && g s 5 == leaf)
      c ← newVec c htID (htLen p) 1
      pure c.machine
    | .reserve => do
      let desc ← a 0
      let used ← a 1
      let add ← a 2
      guard (stackOK s desc 24 && (← a 3) == 1 && (← a 4) == 1 && (← usize s (desc+16)) == used && add > 0)
      let first := used == 0
      guard ((← usize s desc) == c.cap && (← usize s (desc+8)) == (if first then 1 else c.output))
      let mut data := []
      if first then guard (c.output == 0 && add == n && c.parts.isEmpty)
      else
        guard (c.output != 0 && c.cap ≥ used && c.cap < used+add)
        data ← read s.m c.output n
        guard (data == randomizer n && ((used == n && add == p.forsSigBytes && c.parts.isEmpty) ||
          (used == n+p.forsSigBytes && add == htLen p && c.parts == [.fors])))
      let newCap := if first && profile%2 == 1 then (if profile ≥ 2 then total p else n+p.forsSigBytes)
                    else if !first && add == p.forsSigBytes && profile ≥ 2 then total p
                    else used+add
      guard (newCap ≤ 0x10000)
      let ptr := buf (c.serial+1)
      let s ← vec s desc newCap ptr used
      c := {c with output := ptr, cap := newCap, serial := c.serial+1}
      pure {s with m := write s.m ptr data}
    | .copy => do
      let part := if c.parts.isEmpty then Part.fors else Part.ht
      let h ← heap c (if part == .fors then forsID else htID)
      let off := if part == .fors then n else n+p.forsSigBytes
      guard (c.parts.length < 2 && (← a 0) == c.output+off && (← a 1) == h.ptr &&
        (← a 2) == h.count && c.cap ≥ off+h.count && has s c.output (randomizer n))
      c := {c with parts := c.parts ++ [part]}
      pure s
    | .free => do
      let ptr ← a 0
      let some h := c.heaps.find? (fun h => h.ptr == ptr) | none
      guard ((← a 1) == h.count*h.align && (← a 2) == h.align)
      c := {c with heaps := c.heaps.filter (fun v => v.ptr != ptr)}
      pure s
  let s := clobber s (256+64*c.epoch)
  return {c with machine := {s with pc := ret}, epoch := c.epoch+1}

def ordinary (im : Image) (c : Control) (w : Nat) : Option State := do
  let s := c.machine
  let rs := locations im.p c
  let rs := some ((im.cfg.param,36)::rs.1,rs.2)
  let d := w%32
  let n := w/32%32
  let m := w/65536%32
  let pc := s.pc
  let next := {s with pc := pc+4}
  let mask := fun k => w &&& k
  if w == 0xa9ba6ffc then -- STP X28,X27,[SP,#-96]!
    guard (s.sp == stack)
    let t := {next with sp := s.sp-96}
    let t ← transfer im.cfg t false false 28 t.sp 8 rs
    transfer im.cfg t false false 27 (t.sp+8) 8 rs
  else if w == 0xa8c66ffc then -- LDP X28,X27,[SP],#96
    guard (s.sp == stack-96)
    let t ← transfer im.cfg next true false 28 s.sp 8 rs
    let t ← transfer im.cfg t true false 27 (s.sp+8) 8 rs
    return {t with sp := stack}
  else if mask 0xffe0fc00 == 0x8b000000 || mask 0xffe0fc00 == 0xcb000000 then
    guard (d < 31 && n < 31 && m < 31)
    let a ← arg s n
    let b ← arg s m
    return put next d (num (if w/2^30%2 == 0 then a+b else a+2^64-b))
  else if w == 0xd2c00068 then return put next 8 (num (3*2^32))
  else if w == 0xd37ef501 then return put next 1 (num (4*(← arg s 8)))
  else if mask 0xffe0fc1f == 0xeb00001f then
    return {next with ls := some ((← arg s n) ≤ (← arg s m))}
  else if mask 0xff00001f == 0x54000008 then
    let ls ← s.ls
    return {next with pc := if ls then pc+4 else addr pc (4*signExt (w/32%2^19) 19)}
  else if mask 0xff000000 == 0xb4000000 then
    return {next with pc := if (← arg s d) == 0 then addr pc (4*signExt (w/32%2^19) 19) else pc+4}
  else if mask 0xffe0fc00 == 0x3ca06800 then
    transfer im.cfg next false true d ((← arg s n)+(← arg s m)) 16 rs
  else step im.cfg s w rs

def coord (im : Image) (c : Control) : Option Control := do
  let s := c.machine
  let p := im.p
  let dg ← heap c digestID
  guard (!c.coord && c.crypto == schedule.take 5 && (← arg s 19) == dg.ptr && (← arg s 2) == p.m &&
    (← arg s 21) == im.cfg.param && (← arg s 25) == p.a && (← arg s 24) == p.k &&
    (← arg s 8) == p.hp && (← arg s 9) == 7)
  let j := (s.pc-im.body)/4
  guard (ArmSignCoordinates.result p (im.bodyWords.extract j (j+37)) == some (ArmSignCoordinates.expected p))
  -- All live scalar outputs are recovered below. Forget the other modified
  -- registers and flags, so no subsequent proof may silently rely on stale data.
  let dead := [1,8,9,10,11,12,13,14]
  let s := dead.foldl (fun st r => put st r (unknown (1500+r) 2)) s
  let s := put (put (put s 23 (num p.mdBytes)) 26 tree) 28 leaf
  return {c with machine := {s with pc := s.pc+4*37, ls := none}, coord := true}

def tick (im : Image) (profile : Nat) (c : Control) : Option Control := do
  let pc := c.machine.pc
  if let some op := im.hooks.lookup pc then call im profile c op
  else if pc == im.coordinates then coord im c
  else
    guard (pc%4 == 0)
    let w ← if region pc 4 im.cfg.entry (4*im.entryWords.size)
      then im.entryWords[(pc-im.cfg.entry)/4]?
      else if region pc 4 im.body (4*im.bodyWords.size)
      then im.bodyWords[(pc-im.body)/4]? else none
    let s ← ordinary im c w
    return {c with machine := s}

structure Observation where
  calls : List Op
  parts : List Part
deriving DecidableEq, Repr

def run (im : Image) (profile : Nat) : Option Observation := do
  let p := im.p
  guard (profile < 4 && im.cfg.params == parameterBytes p && im.cfg.n == p.n)
  let start := initial im
  let mut c := start
  for _ in [:512] do
    if c.machine.pc == stop then break
    c ← tick im profile c
  let s := c.machine
  guard (s.pc == stop && s.sp == stack && g s 30 == unknown 30 2 && c.heaps.isEmpty &&
    c.output != 0 && (← usize s descriptor) == c.cap && (← usize s (descriptor+8)) == c.output &&
    (← usize s (descriptor+16)) == total p && c.cap ≥ total p &&
    has s c.output (randomizer p.n))
  guard (((List.range 12).map (·+18)).all (fun r => g s r == g start.machine r))
  guard (((List.range 8).map (·+8)).all (fun r => (q s r).take 2 == (q start.machine r).take 2))
  return ⟨c.crypto,.r :: c.parts⟩

def expected : Observation := ⟨schedule,[.r,.fors,.ht]⟩

/-- Each call contract gives the result of that operation on its checked inputs.
  There is no final-signature correspondence premise. -/
def nativeTree (p : Params) (dg : Bytes) := ArmSignCoordinates.eval dg (ArmSignCoordinates.expected p).1
def nativeLeaf (p : Params) (dg : Bytes) := ArmSignCoordinates.eval dg (ArmSignCoordinates.expected p).2
def nativeAddress (p : Params) (dg : Bytes) : Adrs :=
  { { Adrs.zero with tree := nativeTree p dg }.setTypeAndClear FORS_TREE with keypair := nativeLeaf p dg }

structure Callees (p : Params) (msg key random : Bytes) where
  scratch : LinkedArm.Signer.Scratch
  r : Bytes
  dg : Bytes
  digits : List Nat
  forest : Bytes
  root : Bytes
  layers : LinkedArm.Signer.Layers
  keySize : key.length = 4*p.n
  randomSize : random.length = p.n
  rSize : r.length = p.n
  dgSize : dg.length = p.m
  forestSize : forest.length = p.forsSigBytes
  rootSize : root.length = p.n
  absorbed : Nat → Keccak.State × Nat
  absorbKey : absorbed 0 = (Spec.block p key 1).foldl Keccak.feed Keccak.initial
  absorbRandom : absorbed 1 = random.foldl Keccak.feed (absorbed 0)
  absorbMessage : absorbed 2 = msg.foldl Keccak.feed (absorbed 1)
  finish : r = LinkedArm.Digest.finish scratch (absorbed 2) p.n
  digest : dg = LinkedArm.Signer.sponge scratch (r ++ Spec.block p key 2 ++ Spec.block p key 3 ++ msg) p.m
  decode : digits = base2b (dg.take p.mdBytes) p.a p.k
  fors : forest = LinkedArm.Signer.forsRows p digits (Spec.block p key 0) (Spec.block p key 2)
    (nativeAddress p dg)
  recover : root = LinkedArm.Signer.forsRoots p digits forest (Spec.block p key 2)
    (nativeAddress p dg)
  ht : LinkedArm.Signer.LayerCalls p (Spec.block p key 0) (Spec.block p key 2)
    ([],root,nativeTree p dg,nativeLeaf p dg) layers
  htSize : (LinkedArm.Signer.afterLayers p layers ([],root,nativeTree p dg,nativeLeaf p dg) p.d).1.length = htLen p

def materialize {p msg key random} (v : Callees p msg key random) (o : Observation) :=
  o.parts.flatMap fun part => match part with
    | .r => v.r
    | .fors => v.forest
    | .ht => (LinkedArm.Signer.afterLayers p v.layers
        ([],v.root,digestTree p v.dg,digestLeaf p v.dg) p.d).1

def trace {im profile msg key random o} (actual : run im profile = some o)
    (certificate : run im profile = some expected) (row : im.p.mdBytes+im.p.treeBytes+im.p.leafBytes ≤ im.p.m)
    (v : Callees im.p msg key random) :
    LinkedArm.Signer.Signature im.p msg key random (materialize v o) := by
  rw [certificate] at actual
  cases Option.some.inj actual
  obtain ⟨ht,hl⟩ := ArmSignCoordinates.interpretation im.p v.dg (v.dgSize ▸ row)
  have treeEq : nativeTree im.p v.dg = digestTree im.p v.dg := ht
  have leafEq : nativeLeaf im.p v.dg = digestLeaf im.p v.dg := hl
  have ad : nativeAddress im.p v.dg = LinkedArm.Signer.forsAddress im.p v.dg := by simp only [nativeAddress,LinkedArm.Signer.forsAddress,treeEq,leafEq]
  exact { scratch := v.scratch, r := v.r, digest := v.dg, digits := v.digits,
          sigFors := v.forest, pkFors := v.root, layers := v.layers, randomness := by
            simpa only [v.absorbMessage,v.absorbRandom,v.absorbKey,LinkedArm.Signer.sponge,List.foldl_append] using v.finish,
          digest_eq := v.digest, decode := v.decode, forest_sig := ad ▸ v.fors,
          forest_pk := ad ▸ v.recover, layer_calls := by simpa only [treeEq,leafEq] using v.ht,
          layout := by simp [materialize, expected] }
end Spec.ArmInternalSigner
