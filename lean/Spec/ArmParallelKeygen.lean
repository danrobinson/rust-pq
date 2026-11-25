import Spec.ArmPublicKeygen

namespace Spec.ArmParallelKeygen
open ArmKeygen

/-- ABI of the optional parallel top-root call and the immediately following
byte load of its discriminant. The payload is installed only on success. -/
def workerReturn (c : Config) (used : Bool) (s : State) (pc w : Nat) : Option State := do
  guard (g s 0 == num c.param && s.seeded == (c.seed != .shake) && !s.called)
  let ret ← natVal (g s 30)
  let result ← natVal (g s 8)
  let key ← natVal (g s 1)
  let seed ← natVal (g s 2)
  let adrs ← natVal (g s 3)
  let n := c.n
  let k := (seedContext c).length*4
  guard (ret == pc && readable c s key n && readable c s seed k && readable c s adrs 28 &&
    region result (n+1) s.sp (stack-s.sp) && (result+1)%4 == 0 &&
    disjoint result (n+1) key n && disjoint result (n+1) seed k && disjoint result (n+1) adrs 28)
  guard ((← read s.m key n) == ArmKeygen.block n 0 && (← read s.m seed k) == seedContext c &&
    (← read s.m adrs 28) == [0,0,c.d-1,0,0,0,0])
  let after := clobber s 192
  let baseAddr ← baseVal after (w/32%32)
  let tagAddr ← if w &&& 0xffc00000 == 0x39400000 then some (addr baseAddr ((w/1024%4096 : Nat) : Int))
                else if w &&& 0xffe00c00 == 0x38400000 then some (addr baseAddr (signExt (w/4096%512) 9))
                else none
  guard (tagAddr == result && w%32 < 31)
  -- Erase every old word overlapping the Option, including its tag.
  let mem := s.m.filter (fun a _ => disjoint a 4 result (n+1))
  let mem := if used then write mem (result+1) (ArmKeygen.block n 3) else mem
  return {put after (w%32) (num (if used then 1 else 0)) with pc:=pc+4, m:=mem, called:=used}

def stepHi (c : Config) (s : State) (w : Nat) : Option State := do
  if w &&& 0xff00001f == 0x54000008 then
    let ls ← s.ls
    return {s with pc:=if ls then s.pc+4 else addr s.pc (4*signExt (w/32%2^19) 19)}
  step c s w

/-- Local SHA-256 seed-block contract for the pinned parallel executable. Its
register assignment and scratch area differ from the serial consumer. -/
def seedWords : List Nat :=
  [0x6e200800, 0x6f00e401, 0xad0007e0, 0xad0107e1, 0xd000038a, 0x3dc08940,
    0xd000038b, 0x3dc08d61, 0x910003ec, 0x900003cd, 0x911b01ad, 0x1400000a,
    0x3ce979a3, 0x4ea28463, 0x4ea11c22, 0x5e034002, 0x5e035020, 0x4ea21c41,
    0xaa0e03e9, 0xf10041df, 0x54000240, 0x9240052f, 0x3cef7982, 0x9100052e,
    0xf100313f, 0x54fffe62, 0x924005d0, 0x3cf07983, 0x4ea21c44, 0x5e282864,
    0x51000530, 0xd27f01f1, 0x3cf17983, 0x92400610, 0x3cf07985, 0x5e056064,
    0x3caf7984, 0x17ffffe7, 0x5100051c, 0x3dc08d61, 0x4ea18441, 0x3dc08942,
    0x4ea28400]

def workerSeed (c : Config) (s : State) (words iv rounds : List Nat) : Option State := do
  guard (c.n==16 && !s.seeded && !s.called && q s 0 == ArmKeygen.block c.n 2 && g s 9 == num 0)
  let d ← natVal (g s 8)
  guard (s.pc==0x1000cc908 && words==seedWords && d==c.d && region s.sp 64 s.sp (stack-s.sp))
  let h := Spec.SHA256.H0.map BitVec.toNat
  guard (iv==h.drop 4++h.take 4 && rounds==Spec.SHA256.K.map BitVec.toNat)
  let regs := (List.range 9).foldl (fun t i => t.insert (9+i) (unknown (128+i) 2)) s.g
  let vectors := (List.range 6).foldl (fun t i => t.insert i (unknown (160+i) 4)) s.q
  let digest := ArmKeygen.block 32 4
  return {s with
    g := regs.insert 28 (num ((d+radix-1)%radix))
    q := (vectors.insert 1 (digest.take 4)).insert 0 (digest.drop 4)
    m := write s.m s.sp ((List.range 16).map (token 5))
    pc := s.pc+4*words.length
    ls := none
    seeded := true}

def advance (c : Config) (worker : Nat) (used : Bool) (state : Bool × State) (op : Nat × Nat) :
    Option (Bool × State) := do
  let (seen,s) := state
  let (pc,w) := op
  guard (pc%4 == 0 && w<2^32)
  let s ← match c.seed with
    | .external entry => if s.pc==entry then externalSeed c s else some s
    | .inlined entry words iv rounds => if s.pc==entry then workerSeed c s words iv rounds else some s
    | .shake => some s
  if s.pc==worker then
    guard (!seen)
    return (true,← workerReturn c used s pc w)
  let s ← if s.pc==c.root then do
    guard (seen && !used)
    match c.seed with
    | .shake => ArmPublicKeygen.rootCall c s
    | _ => subtree c s
    else some s
  guard (s.pc==pc)
  return (seen,← stepHi c s w)

def run (c : Config) (worker : Nat) (used : Bool) (trace : List (Nat × Nat)) : Option (Cells × Cells) := do
  guard (c.params.length==36 && c.params.all (·<256) && [16,24,32].contains c.n)
  let start := init c
  let (seen,s) ← trace.foldlM (advance c worker used) (false,start)
  guard (seen && s.called && s.pc==stop && g s 30 == unknown 30 2 && s.sp==stack)
  guard (((List.range 12).map (·+18)).all (fun r => g s r == g start r))
  guard (((List.range 8).map (·+8)).all (fun r => (q s r).take 2 == (q start r).take 2))
  return (← read s.m sk (4*c.n), ← read s.m (if c.internal then sk+4*c.n else pk) (2*c.n))

theorem fips (p : Params) (v : p.Valid) (c : Config) (worker : Nat) (used : Bool) (trace : List (Nat × Nat))
    (checked : run c worker used trace=some (secret p.n,publicKey p.n)) (aligned : p.n%4=0) (small : p.n≤32)
    (s r k : Bytes) (hs : s.length=p.n) (hr : r.length=p.n) (hk : k.length=p.n) :
    (run c worker used trace).map (fun keys =>
      let f := interpret (ArmPublicKeygen.inputs p s r k)
      (bytes f keys.1,bytes f keys.2))=some (slhKeygenInternal p s r k) := by
  have size (i : Nat) (hi : i<4) : (ArmPublicKeygen.inputs p s r k i).length=p.n := by
    interval_cases i <;> first | exact hs | exact hr | exact hk | apply xmssNode_length p v
  have blockEq (i) (hi : i<4) := bytes_block (size i hi) aligned small
  have append (a b : Cells) : bytes (interpret (ArmPublicKeygen.inputs p s r k)) (a++b) =
      bytes (interpret (ArmPublicKeygen.inputs p s r k)) a ++ bytes (interpret (ArmPublicKeygen.inputs p s r k)) b :=
    List.flatMap_append
  rw [checked]
  simp only [Option.map_some,secret,publicKey,append,blockEq 0 (by decide),blockEq 1 (by decide),
    blockEq 2 (by decide),blockEq 3 (by decide)]
  rfl

end Spec.ArmParallelKeygen
