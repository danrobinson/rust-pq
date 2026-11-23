import Spec.ArmKeygen

namespace Spec.ArmSignCoordinates
open ArmKeygen

/-- Data registers carry the ordered digest byte offsets aggregated by the native
    ORR loop. Only disjoint shifts and whole-byte insertions are admitted. -/
inductive V where
  | num (v : Nat)
  | ptr (offset : Nat)
  | params
  | byte (offset : Nat)
  | be (offsets : List Nat)
  | shifted (offsets : List Nat) (count : Nat)
  | low (offsets : List Nat) (bits : Nat)
deriving DecidableEq, Repr
structure CState where
  regs : Std.TreeMap Nat V := {}
  ip : Nat := 0
  z : Option Bool := none
  hi : Option Bool := none
  vectorLoads : List Nat := [] -- stack loads interleaved with segmented SHA2-128 coordinate decoding
  saved : List (V × V) := [] -- paired tree/type store in the SHA2-192/256 coordinate block

def regs (s : CState) (n : Nat) := s.regs[n]?
def dst (s : CState) (d : Nat) (v : V) := {s with regs := s.regs.insert d v}
def number (s : CState) (n : Nat) : Option Nat := do
  let .num v ← regs s n | none
  return v
def octets (s : CState) (n : Nat) : Option (List Nat) := do
  match ← regs s n with
  | .num 0 => return []
  | .be xs => return xs
  | _ => none

def exec (p : Params) (s : CState) (w : Nat) (segmented : Bool := false) : Option CState := do
  let s := {s with ip := s.ip+1}
  let d := w%32
  let n := w/32%32
  let m := w/65536%32
  let imm := w/1024%4096
  let mask := fun k => w &&& k
  let jump := fun (take : Bool) => {s with ip := if take then addr (s.ip-1) (signExt (w/32%2^19) 19) else s.ip}
  if mask 0xffe08000 == 0x1b000000 then
    return dst s d (.num (((← number s n)*(← number s m)+(← number s (w/1024%32)))%radix))
  else if mask 0xffc0fc00 == 0x53007c00 then return dst s d (.num ((← number s n) >>> (w/65536%32)))
  else if w == 0xb94012aa || w == 0xb94012ca || (segmented && w == 0xb940128a) then
    guard (regs s n == some .params)
    return dst s 10 (.num p.h)
  else if mask 0xffe0fc00 == 0x4b000000 then
    let a ← if n == 31 then some 0 else number s n
    return dst s d (.num ((a+radix-(← number s m))%radix))
  else if mask 0xffc00000 == 0x11000000 then return dst s d (.num (((← number s n)+imm)%radix))
  else if mask 0xffe0fc00 == 0x8b000000 then
    match ← regs s n, ← regs s m with
    | .num a, .num b => return dst s d (.num ((a+b)%2^64))
    | .ptr a, .num b | .num b, .ptr a => return dst s d (.ptr (a+b))
    | _,_ => none
  else if mask 0xffe0fc00 == 0x0b400c00 then
    return dst s d (.num (((← number s n)+((← number s m) >>> 3))%radix))
  else if mask 0xffe0ffff == 0xeb00003f then
    let a ← number s n
    let b ← number s m
    return {s with hi := some (a > b), z := some (a == b)}
  else if mask 0xff00001f == 0x54000008 then return jump (← s.hi)
  else if mask 0xffffffe0 == 0xd2800000 then return dst s d (.num 0)
  else if mask 0xff000000 == 0x34000000 then return jump ((← number s d)%radix == 0)
  else if mask 0xfffffc00 == 0x38401400 then
    guard (n != d)
    let .ptr a ← regs s n | none
    guard (a < p.m)
    return dst (dst s n (.ptr (a+1))) d (.byte a)
  else if mask 0xffe0fc00 == 0xaa002000 then
    let .byte a ← regs s n | none
    let xs ← octets s m
    guard (xs.length < 8)
    return dst s d (.be (xs ++ [a]))
  else if mask 0xffc00000 == 0xf1000000 then
    let v := ((← number s n)+2^64-imm)%2^64
    return {(dst s d (.num v)) with z := some (v == 0), hi := some ((← number s n) > imm)}
  else if mask 0xff00001f == 0x54000001 then return jump (!(← s.z))
  else if segmented && [0x3dc007e0,0xad4193e5].contains w then
    return {s with vectorLoads := s.vectorLoads ++ [w]}
  else if segmented && w == 0x14000003 then return {s with ip := s.ip+2}
  else if w == 0xd2c0006a || (segmented && w == 0xd2c0006b) then return dst s d (.num (3*2^32))
  else if w == 0xa9392bb9 || (segmented && w == (if p.n == 16 then 0xa90a2ff8
      else if p.n == 24 then 0xa9102bf9 else 0xa9112bf9)) then
    return {s with saved := s.saved ++ [(← regs s d, ← regs s (w/1024%32))]}
  else if mask 0xffffffe0 == 0x92800000 then return dst s d (.num (2^64-1))
  else if mask 0xffe0fc00 == 0x9ac02000 then
    let shift := (← number s m)%64
    if let some v := number s n then return dst s d (.num ((v <<< shift)%2^64))
    return dst s d (.shifted (← octets s n) shift)
  else if mask 0xffe0fc00 == 0x9ac02400 then
    let .shifted xs shift ← regs s n | none
    guard (shift == (← number s m)%64)
    return dst s d (.low xs (64-shift))
  else if mask 0xffe0fc00 == 0x0a200000 then
    let v ← number s m
    guard (p.hp ≤ 32 && v%radix == radix - 2^p.hp)
    return dst s d (.low (← octets s n) p.hp)
  else none

def result (p : Params) (words : Array Nat) (sha2 : Bool := false) (segmented : Bool := false) : Option (V × V) := do
  let narrow := sha2 && p.n == 16
  let param := if sha2 && !narrow then (if segmented then 20 else 22) else 21
  let tr := if narrow then 24 else if sha2 then 25 else 26
  let lr := if narrow then 25 else if sha2 then 26 else 28
  let start : CState := {}
  let start := dst (dst start (if segmented then (if narrow then 20 else 21) else 19) (.ptr 0)) param .params
  let inputs := if sha2 then [(11,p.a),(9,p.k),(10,7)] else [(25,p.a),(24,p.k),(9,7)]
  let start := ([(2,p.m),(8,p.hp)] ++ inputs).foldl (fun s (r,v) => dst s r (.num v)) start
  let mut s := start
  for _ in [:128] do
    if s.ip == words.size then break
    let w ← words[s.ip]?
    s ← exec p s w segmented
  guard (s.ip == words.size && (← number s 23) == p.mdBytes)
  let changed := [1,8,9,10,11,12,13,14,23,tr,lr]
  guard ((List.range 32).all (fun r => changed.contains r || regs s r == regs start r))
  let t ← regs s tr
  let l ← regs s lr
  guard (s.saved == (if sha2 && (!narrow || segmented) then [(t,.num (3*2^32))] else []))
  guard (s.vectorLoads == (if segmented && narrow then [0x3dc007e0,0xad4193e5] else []))
  if narrow then guard ((← number s 9) == 0)
  return (t,l)

def expected (p : Params) :=
  (V.low ((List.range p.treeBytes).map (p.mdBytes+·)) (p.h-p.h/p.d),
   V.low ((List.range p.leafBytes).map (p.mdBytes+p.treeBytes+·)) (p.h/p.d))

/-- Give the normalized native low-bit projection its actual unsigned meaning. -/
def eval (dg : Bytes) : V → Nat
  | .low xs bits => toInt (xs.map (fun j => dg[j]!)) % 2^bits
  | _ => 0

private theorem rangeBytes (dg : Bytes) (a n : Nat) (ok : a+n ≤ dg.length) :
    ((List.range n).map (a+·)).map (fun j => dg[j]!) = (dg.drop a).take n := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [getElem!_pos _ _ (by simp at hi; omega)]

theorem interpretation (p : Params) (dg : Bytes)
    (h : p.mdBytes+p.treeBytes+p.leafBytes ≤ dg.length) :
    eval dg (expected p).1 = digestTree p dg ∧ eval dg (expected p).2 = digestLeaf p dg := by
  simp only [expected, eval, digestTree, digestLeaf]
  rw [rangeBytes dg _ _ (by omega),rangeBytes dg _ _ h]
  exact ⟨rfl,rfl⟩
end Spec.ArmSignCoordinates
