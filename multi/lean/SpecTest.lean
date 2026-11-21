import Spec
import Lean.Data.Json

/-! Runs the Lean specification against the NIST ACVP vectors. -/

open Lean Spec

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def unhex (s : String) : Bytes :=
  let rec go : List Char → Bytes
    | hi :: lo :: rest => BitVec.ofNat 8 (16 * hexVal hi + hexVal lo) :: go rest
    | _ => []
  go s.toList

def field (j : Json) (key : String) : Bytes :=
  unhex ((j.getObjValAs? String key).toOption.getD "")

def arr (j : Json) (key : String) : Array Json :=
  (j.getObjValAs? (Array Json) key).toOption.getD #[]

def main (args : List String) : IO UInt32 := do
  let set := args.headD "128s"
  let some p := [("128s", sha2_128s), ("128f", sha2_128f), ("192s", sha2_192s), ("192f", sha2_192f),
      ("256s", sha2_256s), ("256f", sha2_256f)].lookup set
    | throw (IO.userError s!"unknown parameter set {set}")
  let path := args.getD 2 s!"../vectors/slh-dsa-sha2-{set}.json"
  let .ok v := Json.parse (← IO.FS.readFile path) | throw (IO.userError "bad json")
  let mut bad := 0
  let mut total := 0
  let mode := args.getD 1 "all"
  -- A SHA-256 sanity check: SHA-256("abc").
  let abc := sha256 [0x61#8, 0x62#8, 0x63#8]
  unless abc == unhex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
    IO.println "sha256(abc) FAILED"; bad := bad + 1
  -- SHA-512("abc") (FIPS 180-4 example).
  unless sha512 [0x61#8, 0x62#8, 0x63#8] == unhex "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" do
    IO.println "sha512(abc) FAILED"; bad := bad + 1
  -- Table 2: signature and digest sizes follow from the other parameters.
  let sizes := [("128s", 7856), ("128f", 17088), ("192s", 16224), ("192f", 35664), ("256s", 29792), ("256f", 49856)]
  unless sizes.lookup set == some p.sigBytes && p.m == p.mdBytes + p.treeBytes + p.leafBytes
      && p.len1 == 2 * p.n && p.len2 == 3 && p.h == p.d * p.hp do
    IO.println "Table 2 sizes FAILED"; bad := bad + 1
  for g in arr v "sigVer" do
    let internal := (g.getObjValAs? String "signatureInterface").toOption == some "internal"
    for t in arr g "tests" do
      let expect := (t.getObjValAs? Bool "testPassed").toOption.getD false
      let got :=
        if internal then slhVerifyInternal p (field t "message") (field t "signature") (field t "pk")
        else slhVerify p (field t "message") (field t "signature") (field t "context") (field t "pk")
      total := total + 1
      unless got == expect do
        IO.println s!"sigVer {t.getObjVal? "tcId" |>.toOption} FAILED"; bad := bad + 1
  IO.println s!"{set} sigVer done: {total} cases, {bad} failures"
  (← IO.getStdout).flush
  if mode == "ver" then return (if bad == 0 then 0 else 1)
  for g in arr v "keyGen" do
    for t in (arr g "tests").extract 0 2 do
      let (sk, pk) := slhKeygenInternal p (field t "skSeed") (field t "skPrf") (field t "pkSeed")
      total := total + 1
      unless sk == field t "sk" && pk == field t "pk" do
        IO.println s!"keyGen {t.getObjVal? "tcId" |>.toOption} FAILED"; bad := bad + 1
  IO.println s!"{set} keyGen done: {total} cases, {bad} failures"
  (← IO.getStdout).flush
  for g in arr v "sigGen" do
    let internal := (g.getObjValAs? String "signatureInterface").toOption == some "internal"
    let det := (g.getObjValAs? Bool "deterministic").toOption.getD false
    for t in (arr g "tests").extract 0 1 do
      let sk := field t "sk"
      let rnd := if det then block p sk 2 else field t "additionalRandomness"
      let sig :=
        if internal then some (slhSignInternal p (field t "message") sk rnd)
        else slhSign p (field t "message") (field t "context") sk rnd
      total := total + 1
      unless sig == some (field t "signature") do
        IO.println s!"sigGen {t.getObjVal? "tcId" |>.toOption} FAILED"; bad := bad + 1
  IO.println s!"{set} all done: {total} cases, {bad} failures"
  return if bad == 0 then 0 else 1
