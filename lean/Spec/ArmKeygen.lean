import Spec.AppleSignatureRoundTrip

/-! Restricted little-endian AArch64 semantics for the two linked fixed-size SHAKE
key-generation entries. Memory and registers contain four-byte symbolic cells.
Literal cells are below 2^32. Higher values are distinct input, root or unknown
cells. No instruction may do arithmetic on an opaque cell. -/
namespace Spec.ArmKeygen
set_option maxRecDepth 32768

abbrev Cells := List Nat
abbrev Memory := Std.TreeMap Nat Nat

def base := 0x100000
def stack := 0x200000
def sk := 0x300000
def pk := 0x400000
def stop := 0x500000
def radix := 2^32
def num (x : Nat) : Cells := [x % radix, x / radix % radix]
def disjoint (a na b nb : Nat) := a+na ≤ b || b+nb ≤ a
def natVal : Cells → Option Nat
  | [lo,hi] => if lo < radix && hi < radix then some (lo+hi*radix) else none
  | _ => none

def token (i j : Nat) := radix + 64*i + j
def block (n i : Nat) := (List.range (n/4)).map (token i)
def secret (n : Nat) := block n 0 ++ block n 1 ++ block n 2 ++ block n 3
def publicKey (n : Nat) := block n 2 ++ block n 3

def write (m : Memory) (a : Nat) (v : Cells) : Memory :=
  (v.zipIdx).foldl (fun t (w,i) => t.insert (a+4*i) w) m
def read (m : Memory) (a k : Nat) := (List.range (k/4)).mapM (fun i => m[a+4*i]?)

structure Config where
  n : Nat
  d : Nat
  hp : Nat
  entry : Nat
  root : Nat
  param : Nat
  params : List Nat -- 36 actual bytes at the linked parameter address
  internal : Bool

/-- Native parameter layout in the measured artifact, with no reads of trailing padding. -/
def parameterBytes (p : Spec.Params) : List Nat :=
  [(p.n,8),(p.m,8),(p.h,4),(p.d,4),(p.hp,4),(p.a,4),(p.k,4)].flatMap
    (fun (v,len) => (List.range len).map (fun i => (v / 256^i) % 256))

structure State where
  pc : Nat
  sp : Nat := stack
  g : Std.TreeMap Nat Cells := {}
  q : Std.TreeMap Nat Cells := {}
  m : Memory := {}
  ls : Option Bool := none
  called : Bool := false

def unknown (r k : Nat) := (List.range k).map (fun j => 2*radix + 8*r+j)
def g (s : State) (r : Nat) := s.g.getD r (unknown r 2)
def q (s : State) (r : Nat) := s.q.getD r (unknown (32+r) 4)
def put (s : State) (r : Nat) (v : Cells) : State := {s with g := s.g.insert r v}
def region (a k start len : Nat) := decide (start ≤ a ∧ a+k ≤ start+len)
def writable (c : Config) (s : State) (a k : Nat) :=
  region a k s.sp (stack-s.sp) ||
    (if c.internal then region a k sk (6*c.n) else region a k sk (4*c.n) || region a k pk (2*c.n))
def readable (c : Config) (s : State) (a k : Nat) :=
  writable c s a k || region a k base (3*c.n) || region a k c.param 36

def init (c : Config) : State := Id.run do
  let mut s : State := {pc := c.entry}
  if c.internal then s := put s 8 (num sk)
  s := put (put (put s 0 (num base))
    1 (num (if c.internal then base+c.n else sk))) 2 (num (if c.internal then base+2*c.n else pk))
  let m := write s.m base ((block c.n 0) ++ (block c.n 1) ++ (block c.n 2))
  let words := (List.range 9).map fun i =>
    ((c.params.drop (4*i)).take 4).zipIdx.foldl (fun v (b,j) => v+b*256^j) 0
  return {s with m := write m c.param words}

def signExt (v bits : Nat) : Int :=
  if v < 2^(bits-1) then v else (v : Int)-2^bits
def addr (a : Nat) (off : Int) := (((a : Int)+off) % 2^64).toNat
def baseVal (s : State) (r : Nat) := if r == 31 then some s.sp else natVal (g s r)

def transfer (c : Config) (s : State) (ld vec : Bool) (r a k : Nat) : Option State := do
  guard (a%4 == 0)
  if ld then
    guard (readable c s a k && r != 31)
    let v ← read s.m a k
    return if vec then {s with q := s.q.insert r v}
           else put s r (if k == 4 then v ++ [0] else v)
  else
    guard (writable c s a k)
    let v := if vec then q s r else if r == 31 then num 0 else g s r
    guard (v.length*4 ≥ k)
    return {s with m := write s.m a (v.take (k/4))}

def step (c : Config) (s : State) (w : Nat) : Option State := do
  guard (w < 2^32)
  let pc := s.pc
  let s := {s with pc := pc+4}
  let d := w%32
  let n := (w/32)%32
  let m := (w/65536)%32
  let imm := (w/1024)%4096
  let mask := fun bits => w &&& bits
  if mask 0xffe0ffe0 == 0xaa0003e0 then
    guard (m < 31 && d < 31)
    return put s d (g s m)
  else if mask 0xffc00000 == 0x91000000 || mask 0xffc00000 == 0xd1000000 then
    let start ← baseVal s n
    let a := addr start (if w/2^30%2 == 0 then (imm : Int) else -(imm : Int))
    if d == 31 then
      guard (stack-2048 ≤ a && a ≤ stack && a%16 == 0)
      return {s with sp := a}
    return put s d (num a)
  else if mask 0x9f000000 == 0x90000000 then
    guard (d < 31)
    let pages := signExt (((w/32)%2^19)*4 + (w/2^29)%4) 21
    return put s d (num (addr (pc/4096*4096) (4096*pages)))
  else if mask 0xffe00000 == 0x52800000 then
    guard (d < 31)
    return put s d (num (w/32%65536))
  else if mask 0xffc00000 == 0x51000000 then
    guard (d < 31 && n < 31)
    let v ← natVal (g s n)
    return put s d (num ((v%radix + radix - imm)%radix))
  else if mask 0xffc0001f == 0xf100001f then
    let v ← baseVal s n
    return {s with ls := some (v ≤ imm)}
  else if mask 0xff00001f == 0x54000009 then
    let ls ← s.ls
    return {s with pc := if ls then addr pc (4*signExt ((w/32)%2^19) 19) else s.pc}
  else if mask 0x7c000000 == 0x14000000 then
    let s := if w/2^31 == 1 then put s 30 (num (pc+4)) else s
    return {s with pc := addr pc (4*signExt (w%2^26) 26)}
  else if w == 0xd65f03c0 then
    if g s 30 == unknown 30 2 then return {s with pc := stop}
    return {s with pc := ← natVal (g s 30)}
  else if mask 0xffffffe0 == 0x6f00e400 then return {s with q := s.q.insert d [0,0,0,0]}
  else
    let ld := w/2^22%2 == 1
    let mode := mask 0xff800000
    let a ← baseVal s n
    if mode == 0xa9000000 || mode == 0xad000000 || mode == 0x29000000 then
      let k : Nat := if mode == 0xa9000000 then 8 else if mode == 0xad000000 then 16 else 4
      let a := addr a (k * signExt (w/2^15%128) 7)
      let r := w/1024%32
      guard (!ld || d != r)
      let s ← transfer c s ld (k==16) d a k
      transfer c s ld (k==16) r (a+k) k
    else
      let mode := mask 0xff800c00
      let kind := mask 0xff800000
      let scaled := kind == 0x3d800000 || kind == 0xf9000000 || kind == 0xb9000000
      guard (scaled || mode == 0x3c800000 || mode == 0xf8000000 || mode == 0xb8000000)
      let k : Nat := if w/2^24%256 < 128 then 16 else if w/2^24%256 < 192 then 4 else 8
      let off := if scaled then (imm*k : Int) else signExt (w/4096%512) 9
      transfer c s ld (k==16) d (addr a off) k

/-- The single opaque call checks all five XMSS arguments and its indirect result slot.
    The caller receives distinct fresh unknown values for volatile register cells. -/
def subtree (c : Config) (s : State) : Option State := do
  guard (!s.called)
  let arg := fun r => natVal (g s r)
  let a ← arg 0
  let seed ← arg 3
  let adrs ← arg 4
  let out ← arg 8
  guard (readable c s a c.n && readable c s seed c.n && readable c s adrs 28 &&
    region out c.n s.sp (stack-s.sp) && out%4 == 0 &&
    disjoint out c.n a c.n && disjoint out c.n seed c.n && disjoint out c.n adrs 28)
  guard ((← read s.m a c.n) == block c.n 0 && (← read s.m seed c.n) == block c.n 2)
  guard ((← arg 1) == 0 && (← arg 2) == c.hp &&
    (← read s.m adrs 28) == [0,0,c.d-1,0,0,0,0])
  let ret ← arg 30
  let regs := (List.range 18 ++ [30]).foldl (fun t r => t.insert r (unknown (64+r) 2)) s.g
  let simd := (List.range 32).foldl (fun t r =>
    let fresh := unknown (96+r) 4
    t.insert r (if 8 ≤ r && r < 16 then (q s r).take 2 ++ fresh.drop 2 else fresh)) s.q
  return {s with m := write s.m out (block c.n 3), pc := ret, g := regs, q := simd,
                 called := true, ls := none}

/-- Every candidate instruction includes its linked address. A return, branch, or
    call that disagrees with the next PC invalidates the complete witness. -/
def run (c : Config) (path : List (Nat × Nat)) : Option (Cells × Cells) := do
  guard (c.params.length == 36 && c.params.all (· < 256) && [16,24,32].contains c.n)
  let start := init c
  let s ← path.foldlM (fun s (pc,w) => do
    let s ← if s.pc == c.root then subtree c s else some s
    guard (s.pc == pc && pc%4 == 0)
    step c s w) start
  guard (s.pc == stop && g s 30 == unknown 30 2 && s.sp == stack && s.called)
  guard (((List.range 12).map (·+18)).all (fun r => g s r == g start r))
  guard (((List.range 8).map (·+8)).all (fun r => (q s r).take 2 == (q start r).take 2))
  return (← read s.m sk (4*c.n), ← read s.m (if c.internal then sk+4*c.n else pk) (2*c.n))

/-- Interpret each four-byte symbolic cell as its arbitrary four bytes. -/
def bytes (values : Nat → Spec.Bytes) (cells : Cells) : Spec.Bytes := cells.flatMap values

/-- Transfer from a completed symbolic run to the key-generation trace. Inputs and
    the root are interpreted with the same valuation as the returned key buffers. -/
def toKeyGeneration {p : Spec.Params} {out : Cells × Cells} {c : Config} {path}
    (runEq : run c path = some out)
    (checked : run c path = some (secret p.n, publicKey p.n))
    (values : Nat → Spec.Bytes)
    (tree : LinkedArm.Signer.Node p (bytes values (block p.n 0)) (bytes values (block p.n 2))
      {Spec.Adrs.zero with layer := p.d-1} 0 p.hp (bytes values (block p.n 3))) :
    LinkedArm.Signer.KeyGeneration p (bytes values (block p.n 0)) (bytes values (block p.n 1))
      (bytes values (block p.n 2)) (bytes values out.1) (bytes values out.2) := by
  rw [checked] at runEq
  cases Option.some.inj runEq
  exact { root := _, tree, secretBytes := by simp [secret,bytes],
          publicBytes := by simp [publicKey,bytes] }

/-- Interpret a tagged source cell by slicing the arbitrary actual source bytes. -/
def interpret (sources : Nat → Spec.Bytes) (cell : Nat) :=
  let index := cell - radix
  ((sources (index / 64)).drop (4*(index % 64))).take 4

private theorem take_chunks (v : Spec.Bytes) (k : Nat) :
    (List.range k).flatMap (fun j => (v.drop (4*j)).take 4) = v.take (4*k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih, Nat.mul_succ]
    rw [List.take_drop]
    have h := List.take_append_drop (4*k) (v.take (4*k+4))
    simpa [List.take_take, Nat.min_eq_left (show 4*k ≤ 4*k+4 by omega)] using h

theorem bytes_block {sources : Nat → Spec.Bytes} {n i : Nat}
    (size : (sources i).length = n) (multiple : n % 4 = 0) (bound : n ≤ 32) :
    bytes (interpret sources) (block n i) = sources i := by
  unfold bytes block
  rw [List.flatMap_map]
  have cells : (List.range (n/4)).flatMap (fun j => interpret sources (token i j)) =
      (List.range (n/4)).flatMap (fun j => ((sources i).drop (4*j)).take 4) := by
    apply List.flatMap_congr
    intro j hj
    have small := List.mem_range.mp hj
    simp only [interpret, token]
    have hi : (radix + 64*i+j-radix)/64 = i := by omega
    have hj' : (radix + 64*i+j-radix)%64 = j := by omega
    rw [hi,hj']
  rw [cells,take_chunks,List.take_of_length_le (by omega)]

/-- Instantiate the symbolic replay with arbitrary, independently chosen input and
    subtree-root byte strings of the requisite width. Outputs are interpreted
    directly from the successful executor's final memory reads. -/
def concreteKeyGeneration {p : Spec.Params} {out : Cells × Cells} {c : Config} {path}
    (actual : run c path = some out)
    (checked : run c path = some (secret p.n, publicKey p.n))
    (sources : Nat → Spec.Bytes) (sizes : ∀ i < 4, (sources i).length = p.n)
    (multiple : p.n % 4 = 0) (bound : p.n ≤ 32)
    (tree : LinkedArm.Signer.Node p (sources 0) (sources 2)
      {Spec.Adrs.zero with layer := p.d-1} 0 p.hp (sources 3)) :
    LinkedArm.Signer.KeyGeneration p (sources 0) (sources 1) (sources 2)
      (bytes (interpret sources) out.1) (bytes (interpret sources) out.2) := by
  have hb (i) (hi : i < 4) := bytes_block (sizes i hi) multiple bound
  have t := toKeyGeneration actual checked (interpret sources)
  rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)] at t
  exact t tree

end Spec.ArmKeygen
