import Ct.Funs

/-!
# Checker against silent omissions

Every leaking operation of the instrumented program must go through a primitive of
`Ct/Model.lean`. A name of the generated text that is *not* shadowed there resolves to the
Aeneas operation, which is then either a type error or (for `Result`-valued operations) silently
lifted into `Leak` without events. This file inspects the elaborated definitions of `Ct/Funs.lean`
and fails the build unless every constant they mention is

1. another definition of `Ct/Funs.lean` (a matcher among them may only have one alternative,
   so it destructures a tuple and cannot branch);
2. one of the instrumented primitives or plumbing constants of `Ct/Leak.lean`/`Ct/Model.lean`
   or of the build's `Ct/ModelBuild.lean` (`modelConsts`);
3. a type former, a proof (theorem), or a constructor/projection of a structure of
   `Slhdsa/Types.lean` (pure data, cannot branch or index); or
4. on the whitelist `nonLeaking` of non-leaking operations below.

In particular `ite`, `dite`, `cond`, recursors and `casesOn`, `Decidable.rec`, Aeneas's
`Result`-level `bind` and `loop`, and every un-shadowed indexing, copying or division primitive
are rejected, because they are not on the whitelist.

The whitelist is part of the trusted leakage model.

This file is a copy of the single-set tree's `lean/Ct/Check.lean` (the checker itself is unchanged).
The whitelist differs from the single-set tree's by five entries, marked `[six-set]` below: the 64-bit
counterparts of the 32-bit wrapping addition and rotation that the single-set tree already lists
(SHA-512 works on 64-bit words exactly as SHA-256 does on 32-bit words), the constant
`u64::MAX`, and the 128-bit literal and cast target that SHA-512's padding needs for its 128-bit
length field. None of them branches, indexes or divides; each is a total pure function of its
operands, like the 32-bit operations already accepted.
-/

open Lean Meta Elab Command

namespace Ct.Check

/-- Instrumented primitives and plumbing (`Ct/Leak.lean`, `Ct/Model.lean`). -/
def modelConsts : List Name := [
  -- monad plumbing; `cond` emits the branch event, `prim` the events of a primitive
  ``Ct.Leak, ``Ct.Leak.bind, ``Ct.Leak.pure, ``Ct.Leak.cond, ``Ct.Leak.loop, ``Ct.Leak.prim,
  -- `matchOpt` emits the branch event of a `match` on an `Option` (`Ct/Do.lean`)
  ``Ct.Leak.matchOpt,
  ``Ct.Leak.lift, ``Ct.Leak.instMonad, ``Ct.Leak.instMonadLiftResult, ``Ct.Leak.instCCPO,
  -- the names of the generated text that are redefined
  ``slhdsa_leak.Result, ``slhdsa_leak.ok, ``slhdsa_leak.lift, ``slhdsa_leak.loop,
  ``slhdsa_leak.Array.index_usize, ``slhdsa_leak.Array.update,
  ``slhdsa_leak.Array.index_mut_usize, ``slhdsa_leak.Slice.index_usize,
  ``slhdsa_leak.Slice.update, ``slhdsa_leak.Slice.index_mut_usize,
  ``slhdsa_leak.core.slice.index.SliceIndexRangeUsizeSlice,
  ``slhdsa_leak.core.slice.index.SliceIndexUsizeSlice,
  ``slhdsa_leak.core.ops.index.IndexSlice, ``slhdsa_leak.core.ops.index.IndexMutSlice,
  ``slhdsa_leak.core.array.Array.index, ``slhdsa_leak.core.array.Array.index_mut,
  ``slhdsa_leak.core.slice.index.Slice.index, ``slhdsa_leak.alloc.vec.Vec.index,
  ``slhdsa_leak.core.slice.Slice.copy_from_slice, ``slhdsa_leak.alloc.vec.Vec.extend_from_slice,
  ``slhdsa_leak.alloc.vec.Vec.push,
  ``slhdsa_leak.instHDivUScalarLeak, ``slhdsa_leak.instHModUScalarLeak,
  ``slhdsa_leak.core.array.equality.PartialEqArray.eq,
  ``slhdsa_leak.core.clone.Clone, ``slhdsa_leak.core.clone.Clone.mk,
  ``slhdsa_leak.core.marker.Copy, ``slhdsa_leak.core.marker.Copy.mk
] ++ Ct.Build.modelConsts   -- the build's own instrumented primitives (`Ct/ModelBuild.lean`)

/-- Operations of Lean and Aeneas that the instrumented code may use without emitting events.
Keep this short; every entry is an assumption of the leakage model. -/
def nonLeaking : List Name := [
  -- Automatic lift of a `Result` computation into `Leak` (emits nothing).
  ``liftM, ``MonadLiftT.monadLift, ``instMonadLiftTOfMonadLift, ``instMonadLiftT,
  -- Checked arithmetic and shifts (`Result`-valued: they may fail on overflow, and the failure
  -- is kept). Operand values do not leak. Division and remainder are *not* here: `HDiv.hDiv`
  -- and `HMod.hMod` are only accepted with the leaking instances of `Ct/Model.lean`.
  ``HAdd.hAdd, ``Aeneas.Std.instHAddUScalarResult,
  ``HSub.hSub, ``Aeneas.Std.instHSubUScalarResult,
  ``HMul.hMul, ``Aeneas.Std.instHMulUScalarResult,
  ``HShiftLeft.hShiftLeft, ``Aeneas.Std.instHShiftLeftUScalarResult,
  ``Aeneas.Std.instHShiftLeftUScalarIScalarResult,
  ``HShiftRight.hShiftRight, ``Aeneas.Std.instHShiftRightUScalarResult,
  ``Aeneas.Std.instHShiftRightUScalarIScalarResult,
  ``HDiv.hDiv, ``HMod.hMod,
  -- Bitwise operations, wrapping arithmetic, rotations, casts (total, pure).
  ``HXor.hXor, ``Aeneas.Std.instHXorUScalar, ``HAnd.hAnd, ``Aeneas.Std.instHAndUScalar,
  ``HOr.hOr, ``Aeneas.Std.instHOrUScalar, ``Complement.complement,
  ``Aeneas.Std.instComplementUScalar,
  ``Aeneas.Std.core.num.U32.wrapping_add, ``Aeneas.Std.U32.wrapping_sub,
  ``Aeneas.Std.core.num.U32.rotate_right, ``Aeneas.Std.UScalar.cast,
  -- [six-set] The same two operations on 64-bit words (SHA-512's message schedule and rounds):
  -- `wrapping_add` is addition modulo 2^64 and `rotate_right` a rotation by a constant amount,
  -- total and pure, the 64-bit counterparts of the 32-bit entries above. As for those, the
  -- operand values are not recorded (the model has no operand events for `+` or rotations).
  ``Aeneas.Std.core.num.U64.wrapping_add, ``Aeneas.Std.core.num.U64.rotate_right,
  -- Comparisons producing a `Prop`/`Bool` (the branch on them is instrumented by `Leak.cond`).
  ``Aeneas.Std.instLTUScalar, ``Aeneas.Std.UScalar.decLt, ``Aeneas.Std.instLEUScalar,
  ``Aeneas.Std.UScalarDecidableLE, ``Aeneas.Std.instDecidableEqUScalar_1, ``bne,
  ``Aeneas.Std.instBEqUScalar_1, ``instDecidableEqBool,
  -- Turning such a comparison into a `Bool` value (`diff == 0` returned, not branched on): a
  -- flag-setting comparison. Only the decidability instances listed above can reach it, so it
  -- cannot stand for a comparison of arrays, which is the instrumented `PartialEqArray.eq`.
  ``Decidable.decide,
  -- Literals.
  ``OfNat.ofNat, ``instOfNatNat, ``instOfNat, ``Aeneas.Std.U8.ofNat, ``Aeneas.Std.U32.ofNat,
  ``Aeneas.Std.U64.ofNat, ``Aeneas.Std.Usize.ofNat, ``Aeneas.Std.I32.ofInt,
  ``Aeneas.Std.UScalarTy.U8, ``Aeneas.Std.UScalarTy.U32, ``Aeneas.Std.UScalarTy.U64,
  ``Aeneas.Std.UScalarTy.Usize, ``Aeneas.Std.IScalarTy.I32,
  -- [six-set] Literals and type tags of this translation: `u64::MAX` (a constant, shifted by the
  -- public tree height in `digest_tree`), the `u128` literal `8#u128` and the `u128` type tag
  -- of `UScalar.cast .U128` (SHA-512's padding computes the 128-bit bit length of the message,
  -- a public length, as `(len as u128) * 8`). Constants and type tags compute nothing.
  ``Aeneas.Std.core.num.U64.MAX, ``Aeneas.Std.U128.ofNat, ``Aeneas.Std.UScalarTy.U128,
  -- Data constructors (tuples, loop results, options, booleans, lists, ranges).
  ``Prod.mk, ``Aeneas.Std.ControlFlow.cont, ``Aeneas.Std.ControlFlow.done, ``Option.some,
  ``Option.none, ``Bool.true, ``Bool.false, ``List.cons, ``List.nil,
  ``Aeneas.Std.core.ops.range.Range.mk,
  -- Tuple destructuring in `let (a, b) ← e` (no branching: one constructor).
  ``Aeneas.Std.uncurry,
  -- Arrays of statically known length (the length is part of the type), views of arrays and
  -- vectors as slices, lengths, the empty vector. None of them accesses an element.
  ``Aeneas.Std.Array.repeat, ``Aeneas.Std.Array.make, ``Aeneas.Std.Array.to_slice,
  ``Aeneas.Std.Array.to_slice_mut, ``Aeneas.Std.Slice.len, ``Aeneas.Std.alloc.vec.Vec.len,
  ``Aeneas.Std.alloc.vec.Vec.deref, ``Aeneas.Std.alloc.vec.Vec.new,
  -- Trait dictionaries for machine scalars, passed to `copy_from_slice`,
  -- `extend_from_slice` and array `==` (their methods are the identity / scalar `!=`).
  ``Aeneas.Std.core.clone.CloneU8, ``Aeneas.Std.core.clone.CloneU32,
  ``Aeneas.Std.core.marker.CopyU8, ``Aeneas.Std.core.cmp.PartialEqU8,
  -- `partial_fixpoint` plumbing for the two recursive functions (the functional itself is
  -- checked: it is the body of the `.mutual` definition).
  ``Lean.Order.fix, ``Lean.Order.instCCPOPi
]

/-- Constants of a structure of `Slhdsa.Types`: its constructor and projections. -/
def isTypesStructData (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => false
  | some idx =>
    env.header.moduleNames[idx.toNat]! == `Slhdsa.Types &&
    (match env.find? c with
     | some (.ctorInfo _) => true
     | _ => (env.getProjectionFnInfo? c).isSome)

/-- Is `c` a type former (its type is `… → Sort _`) or a proof? -/
def isTypeOrProof (c : Name) : MetaM Bool := do
  let info ← getConstInfo c
  if info matches .thmInfo _ then return true
  forallTelescopeReducing info.type fun _ b => do
    let b ← whnf b
    if b.isSort then return true
    -- a constant whose type is a proposition is a proof
    return (← isProp info.type)

/-- Check the given definitions; `own c` says whether `c` is itself one of the instrumented
definitions (then it is checked on its own). Returns the offences (definition, constant). -/
def checkDecls (decls : Array Name) (own : Name → Bool) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let model : NameSet := modelConsts.foldl (·.insert ·) {}
  let white : NameSet := nonLeaking.foldl (·.insert ·) {}
  let mut bad : Array (Name × Name) := #[]
  for d in decls do
    let some info := env.find? d | continue
    let .defnInfo dv := info | continue
    -- `_unsafe_rec` is the compiler's implementation of a `partial_fixpoint`; it is not part
    -- of the logical definition.
    if dv.safety != .safe || d.components.getLast! == `_unsafe_rec then continue
    if let some mi ← getMatcherInfo? d then
      if mi.numAlts != 1 then bad := bad.push (d, `«matcher with several alternatives»)
      continue
    for c in dv.value.getUsedConstants do
      if own c then
        if let some mi ← getMatcherInfo? c then
          if mi.numAlts != 1 then bad := bad.push (d, c)
        continue
      if model.contains c || white.contains c then continue
      if isTypesStructData env c then continue
      if ← isTypeOrProof c then continue
      bad := bad.push (d, c)
  return bad

/-- All definitions of module `Ct.Funs`. -/
def funsDecls : MetaM (Array Name) := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `Ct.Funs | throwError "Ct.Funs not imported"
  return env.header.moduleData[modIdx.toNat]!.constNames

/-- Run the check on all definitions of module `Ct.Funs`. -/
def check : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `Ct.Funs | throwError "Ct.Funs not imported"
  checkDecls (← funsDecls) fun c => env.getModuleIdxFor? c == some modIdx

elab "#ct_check" : command => do
  let bad ← liftTermElabM check
  let n ← liftTermElabM do
    let ds ← funsDecls
    let env ← getEnv
    return (ds.filter fun d => match env.find? d with
      | some (.defnInfo dv) => dv.safety == .safe
      | _ => false).size
  if bad.isEmpty then
    logInfo m!"ct_check: all {n} definitions of Ct.Funs (including auxiliary matchers and \
      fixpoint functionals) use only instrumented primitives and whitelisted non-leaking \
      operations"
  else
    let offenders := bad.foldl (fun (s : NameSet) p => s.insert p.2) {}
    let msg := offenders.toList.map fun c =>
      let users := (bad.filter (·.2 == c)).map (·.1)
      m!"{c}  (in {users.size} definitions, e.g. {users[0]!})"
    throwError m!"ct_check: {offenders.size} constants outside the leakage model:\n" ++
      MessageData.joinSep msg "\n"

#ct_check

/-- Test of the checker itself: `#ct_expect_reject d c` succeeds iff checking the definition `d`
reports the constant `c`. -/
elab "#ct_expect_reject " d:ident c:ident : command => do
  let bad ← liftTermElabM do
    let d ← realizeGlobalConstNoOverloadWithInfo d
    checkDecls #[d] (fun _ => false)
  let c := c.getId
  unless bad.any (·.2 == c) do
    throwError m!"ct_expect_reject: {c} was not reported (reported: {bad.map (·.2)})"

/-- `#ct_resolves x` (inside `namespace slhdsa_leak`, with the opens of `Ct/Funs.lean`) checks
that the identifier `x` of the generated text resolves to `slhdsa_leak.x` and nothing else. -/
elab "#ct_resolves " x:ident : command => do
  let cs ← liftTermElabM (resolveGlobalConst x)
  let expected := `slhdsa_leak ++ x.getId
  unless cs == [expected] do
    throwError m!"ct_resolves: {x} resolves to {cs}, expected {expected}"

end Ct.Check
