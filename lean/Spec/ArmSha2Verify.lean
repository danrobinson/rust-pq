import Spec.ArmVerifyBody

/-! Linked Apple SHA2 verification, specialized to the internal successful-length driver.
The malformed-length arm is replayed independently by ArmVerifyLength. -/
namespace Spec.ArmSha2Verify
open ArmKeygen ArmVerifyLength
open ArmVerifyBody (Control Action arg frame cellBuffer has writeVec digestCap digestPtr tree leaf root verdict)

structure Image where
  core : ArmVerifyBody.Image
  seedStart : Nat
  iv : List Nat
  constants : List Nat

def seedCells (n : Nat) := if n == 16 then
  List.replicate 16 0 ++ ArmKeygen.block 32 4 ++ ArmKeygen.block n 1 else ArmKeygen.block (96+n) 4

def wideWords (n : Nat) : List Nat :=
  if n == 24 then [0xa94127e8,0xf94003ed,0xa9402daa,0xf94013ec,0xf94009ad,0xeb0a011f,0xfa4b0120,0xfa4d0180,0x1a9f17e0]
  else [0xa94127e8,0xf94003ef,0xa9402dea,0xa94237ec,0xa9413dee,0xeb0a011f,0xfa4b0120,0xfa4e0180,0xfa4f01a0,0x1a9f17e0]

theorem compareWide (n : Nat) (width : n = 24 ∨ n = 32)
    (m : LinkedArm.RootComparison.ByteMemory) (s : LinkedArm.RootComparison.State) :
    LinkedArm.RootComparison.verdict (wideWords n) (LinkedArm.RootComparison.load64 m) s =
      some (if LinkedArm.RootComparison.byteSlice m (s.sp+16) n =
        LinkedArm.RootComparison.byteSlice m (LinkedArm.RootComparison.load64 m s.sp) n then 1 else 0) := by
  rcases width with rfl | rfl <;>
    simp [wideWords,LinkedArm.RootComparison.verdict,LinkedArm.RootComparison.step,
      LinkedArm.RootComparison.base,LinkedArm.RootComparison.operand,LinkedArm.RootComparison.write,
      LinkedArm.RootComparison.load64_eq,LinkedArm.RootComparison.byteSlice,
      List.range_succ,List.foldlM,Bool.and_assoc,Bool.and_eq_true,and_assoc,
      BitVec.add_assoc]

def certifiedWide (n : Nat) (w : n = 24 ∨ n = 32) : ArmVerifyBody.CertifiedComparison n :=
  ⟨wideWords n,fun s => s.sp+16,fun m s => LinkedArm.RootComparison.load64 m s.sp,compareWide n w⟩

/-- The SHA-256 prefix circuit has the same SHA operations and schedule as
the checked keygen seed circuit, with a different stack offset, literal page
relocations and an exit branch around the verifier's rejection stub. -/
def seedPrefix (im : Image) (c : Control) : Option Control := do
  let s := c.machine
  guard (im.core.p.n == 16 && s.pc == im.seedStart && !s.seeded &&
    q s 0 == ArmKeygen.block 16 1 && (← arg s 8) == 0)
  let h0 := SHA256.H0.map BitVec.toNat
  guard (im.iv == h0.drop 4 ++ h0.take 4 && im.constants == SHA256.K.map BitVec.toNat)
  let mapIndex := fun (i : Nat) => if i < 38 then i else i+2
  let actual ← (List.range 42).mapM (fun i => ArmVerifyBody.code im.core (s.pc+4*mapIndex i))
  let changes : List (Nat × Nat) := [(2,0xad0507e0),(3,0xad0607e1),(4,0xd00002c9),
    (6,0xd00002ca),(8,0x910283eb),(9,0xb000030c),(20,0x54000280)]
  guard (s.pc == 0x10007b3c8 && actual == (inlineWords.zipIdx.map (fun (w,i) => (changes.lookup i).getD w)))
  let regs := (List.range 9).foldl (fun t i => t.insert (8+i) (unknown (512+i) 2)) s.g
  let simd := (List.range 6).foldl (fun t i => t.insert i (unknown (576+i) 4)) s.q
  let digest := ArmKeygen.block 32 4
  guard (frame s (s.sp+160) 64)
  let result := { s with
    g := regs,
    q := (simd.insert 1 (digest.take 4)).insert 0 (digest.drop 4),
    m := write s.m (s.sp+160) (unknown 611 16), pc := s.pc+176, seeded := true}
  return {c with flags := none, machine := result}

def expected (p : Params) := [.hash,.fors] ++ (List.range p.d).map Action.layer ++ [.compare]

def tick (im : Image) (c : Control) : Option Control := do
  let i := im.core
  let s := c.machine
  let p := i.p
  let n := p.n
  let a := arg s
  let pc := s.pc
  if pc == im.seedStart then
    if n == 16 then return ← seedPrefix im c
    guard ([24,32].contains n && !s.seeded && c.actions == [.hash] && cellBuffer s (← a 0) (ArmKeygen.block n 1))
    let out ← a 8
    guard (frame s out (96+n) && disjoint out (96+n) (← a 0) n)
    let new := {clobber s (64+64*c.epoch) with pc := ← a 30,m := write s.m out (seedCells n),seeded := true}
    return {c with machine := new, epoch := c.epoch+1, flags := none}
  if pc == i.hmsg || pc == i.free then return ← ArmVerifyBody.action i c
  if pc == i.fors || pc == i.xmss then
    let (actions,layers,out,result) ← if pc == i.fors then do
      guard (s.seeded && c.liveHash && c.actions == [.hash] && (← a 0) == i.gate.param &&
        (← a 1) == sk+n && (← a 2) == p.forsSigBytes && (← a 3) == digestPtr &&
        (← a 4) == p.mdBytes && cellBuffer s (← a 5) (seedCells n) &&
        cellBuffer s (← a 6) (tree 0 ++ [0,3,(leaf 0).head!,0,0]))
      let out ← a 8
      guard (frame s out n && disjoint out n (← a 5) (96+n) && disjoint out n (← a 6) 28)
      pure (c.actions ++ [.fors],0,out,root n 0)
    else do
      let j := c.layers
      guard (j < p.d && c.actions == [.hash,.fors] ++ (List.range j).map Action.layer &&
        (← a 1) == p.hp && g s 2 == leaf j &&
        (← a 3) == sk+n+p.forsSigBytes+j*p.xmssSigBytes && (← a 4) == p.xmssSigBytes &&
        cellBuffer s (← a 5) (root n j) && cellBuffer s (← a 6) (seedCells n) &&
        cellBuffer s (← a 7) (tree j ++ [j,0,0,0,0]))
      let out ← a 0
      guard (frame s out n && disjoint out n (← a 5) n && disjoint out n (← a 6) (96+n) &&
        disjoint out n (← a 7) 28)
      pure (c.actions ++ [.layer j],j+1,out,root n (j+1))
    let ret ← a 30
    return {c with
      actions := actions, layers := layers, flags := none, epoch := c.epoch+1,
      machine := {clobber s (64+64*c.epoch) with pc := ret,m := write s.m out result}}
  let w ← ArmVerifyBody.code i pc
  let d := w%32
  let next := {s with pc := pc+4}
  if n != 16 && w == 0xa94127e8 then
    let seq := if n == 24 then (certifiedWide 24 (Or.inl rfl)).words else (certifiedWide 32 (Or.inr rfl)).words
    guard ((← (List.range seq.length).mapM (fun j => ArmVerifyBody.code i (pc+4*j))) == seq &&
      c.layers == p.d && cellBuffer s (s.sp+16) (root n c.layers))
    let pkRoot ← natVal (← read s.m s.sp 8)
    guard (pkRoot == base+n && has s pkRoot (ArmKeygen.block n 2))
    let next := (List.range 8).foldl (fun t j => put t (8+j) (unknown (9100+j) 2)) next
    return {c with machine := {put next 0 verdict with pc := pc+4*seq.length},
                   actions := c.actions ++ [.compare], flags := none}
  if w &&& 0xffffffe0 == 0x92800000 then return {c with machine := put next d (num (2^64-1))}
  if w &&& 0xffffffe0 == 0xd2c00060 then return {c with machine := put next d (num (3*radix))}
  if w == 0x924016a8 then return {c with machine := put next d (num ((← a 21)%64))}
  return ← ArmVerifyBody.tick i c

def run (im : Image) : Option (List Action) := do
  let mut c ← ArmVerifyBody.init im.core
  for _ in [:2048] do
    if c.machine.pc == stop then break
    c ← tick im c
  let s := c.machine
  guard (s.pc == stop && g s 0 == verdict && s.seeded && !c.liveHash && s.sp == stack &&
    (List.range 13).all (fun j => g s (18+j) == unknown (18+j) 2) &&
    (List.range 8).all (fun j => (q s (8+j)).take 2 == (unknown (40+j) 4).take 2))
  return c.actions

/-- The linked SHA2 FORS callee decodes its own digest prefix. Expose that
contract at its direct ABI without an artificial digit-decoder call. -/
abbrev Callees := ArmVerifyBody.Callees
abbrev returned {p msg sig pk} (v : Callees p msg sig pk) := ArmVerifyBody.returned v

def trace {im msg sig pk events} (actual : run im = some events) (checked : run im = some (expected im.core.p))
    (row : im.core.p.mdBytes+im.core.p.treeBytes+im.core.p.leafBytes ≤ im.core.p.m)
    (v : Callees im.core.p msg sig pk) :
    LinkedArm.Signer.VerifyTrace im.core.p msg sig pk (returned v events) := by
  let p := im.core.p
  rw [checked] at actual
  cases Option.some.inj actual
  obtain ⟨t,l⟩ := ArmSignCoordinates.interpretation p v.digest (v.digestSize ▸ row)
  have ad : ArmVerifyBody.nativeAddress p v.digest = LinkedArm.Signer.forsAddress p v.digest := by
    simp only [ArmVerifyBody.nativeAddress,LinkedArm.Signer.forsAddress,ArmVerifyBody.location,t,l]
  apply LinkedArm.Signer.VerifyTrace.checked v.sigSize
  refine { digest := v.digest
           digits := v.digits
           forsRoot := v.roots 0
           digest_eq := v.hash
           indices := v.decode
           forest := ad ▸ v.forest
           layers := { states := fun j => (v.roots j,ArmVerifyBody.location p v.digest j)
                       start := ?_
                       recover := ?_
                       coords := ?_ }
           result := ?_ }
  · simp only [ArmVerifyBody.location,t,l]; rfl
  · intro j hj
    simpa only [List.drop_drop,Nat.add_comm (j*p.xmssSigBytes)] using v.layer j hj
  · intro j _
    exact ArmVerifyBody.nextLocation p v.digest j
  · have last : (expected p).getLast? = some .compare := List.getLast?_concat
    have cnt : ((List.range p.d).filter (fun _ => true)).length = p.d := by simp
    change returned v (expected p) = _
    unfold returned ArmVerifyBody.returned
    rw [last]
    simp [expected,List.filter_map,Function.comp_def,p]

end Spec.ArmSha2Verify
