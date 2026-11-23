import Spec
import Lean.Data.Json

/-! Run the executable specification on the complete ACVP groups for one set. -/
open Lean Spec

private def required [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept (j.getObjValAs? α key)

private def digit (c : Char) : IO Nat := do
  if c.isDigit then return c.toNat - '0'.toNat
  let c := c.toLower
  if 'a' ≤ c && c ≤ 'f' then return c.toNat - 'a'.toNat + 10
  throw (IO.userError s!"invalid hexadecimal character {c}")

private def unhex (text : String) : IO Bytes := do
  let rec decode : List Char → Bytes → IO Bytes
    | [], acc => pure acc.reverse
    | [_], _ => throw (IO.userError "odd hexadecimal length")
    | a :: b :: rest, acc => do
      let byte := BitVec.ofNat 8 (16 * (← digit a) + (← digit b))
      decode rest (byte :: acc)
  decode text.toList []

private def field (j : Json) (key : String) : IO Bytes := do
  unhex (← required j key)

private def sets : List (String × Params) := [
  ("128s", sha2_128s), ("128f", sha2_128f), ("192s", sha2_192s),
  ("192f", sha2_192f), ("256s", sha2_256s), ("256f", sha2_256f),
  ("shake-128s", shake_128s), ("shake-128f", shake_128f), ("shake-192s", shake_192s),
  ("shake-192f", shake_192f), ("shake-256s", shake_256s), ("shake-256f", shake_256f)]

private def runGroup (p : Params) (op : String) (internal det : Bool) (t : Json) : IO Bool := do
  if op == "keyGen" then
    let (sk, pk) := slhKeygenInternal p (← field t "skSeed") (← field t "skPrf") (← field t "pkSeed")
    return sk == (← field t "sk") && pk == (← field t "pk")
  let msg ← field t "message"
  let ctx ← if internal then pure [] else field t "context"
  let sig ← field t "signature"
  if op == "sigVer" then
    let pk ← field t "pk"
    let expect : Bool ← required t "testPassed"
    return (if internal then slhVerifyInternal p msg sig pk else slhVerify p msg sig ctx pk) == expect
  let sk ← field t "sk"
  let rnd ← if det then pure (block p sk 2) else field t "additionalRandomness"
  return (if internal then some (slhSignInternal p msg sk rnd) else slhSign p msg ctx sk rnd) == some sig

private def check (v : Json) (p : Params) (name op : String) : IO Unit := do
  let groups : Array Json ← required v op
  let (ng, nt) := if op == "keyGen" then (1, 10) else if op == "sigGen" then (4, 7) else (2, 14)
  unless groups.size == ng do throw (IO.userError s!"{name} {op} requires {ng} groups")
  let mut ids : List Nat := []
  let mut modes : List (Bool × Bool) := []
  for g in groups do
    let set : String ← required g "parameterSet"
    unless set == name do throw (IO.userError s!"expected {name}, found {set}")
    let iface : String ← if op == "keyGen" then pure "internal" else required g "signatureInterface"
    unless iface == "internal" || iface == "external" do throw (IO.userError s!"unknown signatureInterface {iface}")
    let det : Bool ← if op == "sigGen" then required g "deterministic" else pure false
    let internal := iface == "internal"
    if modes.contains (internal, det) then throw (IO.userError s!"duplicate {op} group")
    modes := (internal, det) :: modes
    let cases : Array Json ← required g "tests"
    unless cases.size == nt do throw (IO.userError s!"{name} {op} group requires {nt} cases")
    for t in cases do
      let id : Nat ← required t "tcId"
      if ids.contains id then throw (IO.userError s!"duplicate {op} tcId {id}")
      ids := id :: ids
      unless ← runGroup p op internal det t do throw (IO.userError s!"{name} {op} tcId {id} FAILED")
  IO.println s!"{name} {op}: {ids.length} cases passed"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let set := args.headD "128s"
  let some p := sets.lookup set | throw (IO.userError s!"unknown parameter set {set}")
  let mode := args.getD 1 "all"
  unless mode == "ver" || mode == "all" do throw (IO.userError s!"unknown mode {mode}")
  let suffix := if set.startsWith "shake-" then set else "sha2-" ++ set
  let path := args.getD 2 s!"../vectors/slh-dsa-{suffix}.json"
  let v ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let name := "SLH-DSA-" ++ (suffix.dropEnd 1).toString.toUpper ++ (suffix.takeEnd 1).toString
  let abc : Bytes := [0x61, 0x62, 0x63]
  unless sha256 abc == (← unhex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") &&
      sha512 abc == (← unhex "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f") &&
      shake256 [] 32 == (← unhex "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f") do
    throw (IO.userError "hash self-test failed")
  let sizes := [("128s", 7856), ("128f", 17088), ("192s", 16224), ("192f", 35664), ("256s", 29792), ("256f", 49856)]
  unless sizes.lookup (set.takeEnd 4).toString == some p.sigBytes && p.m == p.mdBytes + p.treeBytes + p.leafBytes
      && p.len1 == 2*p.n && p.len2 == 3 && p.h == p.d*p.hp do
    throw (IO.userError "Table 2 sizes failed")
  check v p name "sigVer"
  if mode == "all" then
    check v p name "keyGen"
    check v p name "sigGen"
  return 0
