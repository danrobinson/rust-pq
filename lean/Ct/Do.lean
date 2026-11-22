import Ct.Leak

/-!
# `do` notation for the leakage monad

Aeneas elaborates the `do` blocks of the generated code with its own elaborator
(`Aeneas/Do/Elab.lean`), which only fires for blocks of type `Result _`. This file provides the
same elaborator for blocks of type `Ct.Leak _`, so that the unchanged text of `Slhdsa/Funs.lean`
elaborates to the same term shape with

* `Aeneas.Std.bind` replaced by `Ct.Leak.bind`, and
* `ite c t e` (the elaboration of a `do`-level `if`) replaced by `Ct.Leak.cond c t e`, which emits
  the outcome of the test.

Tuple patterns (`let (a, b) ← e`) are elaborated exactly as Aeneas does (`Aeneas.Std.uncurry`);
we reuse Aeneas's pattern code. Only the `do` elements that occur in the generated code are
supported: `let x ← e`, `let pat ← e`, `let x := e`, `let pat := e`, non-dependent
`if … then … else …` chains, nested `do`, and a final term. Anything else (in particular `match`
and `if h : c`) is rejected, so that no un-instrumented branching can be produced here.

Adapted from Aeneas's `Do/Elab.lean` (Apache-2.0).
-/

open Lean Elab Parser Term Meta
open Aeneas.Do

namespace Ct.Do

/-- Build `Leak α`. -/
def mkLeakType (α : Expr) : ElabM Expr := do
  return mkApp (mkConst ``Ct.Leak [← getDecLevel α]) α

/-- Build `Leak.bind e k`. -/
def mkLeakBind (e k : Expr) : ElabM Expr :=
  mkAppOptM ``Ct.Leak.bind #[none, none, some e, some k]

/-- Build `Leak.cond c thn els`. -/
def mkLeakCond (c thn els : Expr) : MetaM Expr :=
  mkAppOptM ``Ct.Leak.cond #[none, some c, none, some thn, some els]

mutual

partial def elabDoElem (elem : Aeneas.Do.DoElem) (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  match elem with
  | `(doElem| let $x:ident $[: $ty?]? ← $rhs) => elabDoLetArrowId x ty? rhs rest
  | `(doElem| let $pat:term ← $rhs)  => elabDoLetArrowPat pat rhs rest
  | `(doElem| let $x:ident $[: $ty?]? := $rhs) => elabDoLetId x ty? rhs rest
  | `(doElem| let $pat:term := $rhs)  => elabDoLetPat pat rhs rest
  | `(doElem| if $cond:doIfCond then $thenSeq:doSeq
              $[else if $econds:doIfCond then $eseqs:doSeq]*
              else $elseSeq:doSeq) =>
    let branches : Array (TSyntax ``doIfCond × TSyntax ``doSeq) :=
      #[(cond, thenSeq)] ++ econds.zip eseqs
    elabDoIfChain branches elseSeq rest
  | `(doElem| $expr:term)            => elabDoExpr expr rest
  | `(doElem| do $seq:doSeq) =>
    let innerElems ← getDoElems seq
    elabDoSeqCore (innerElems ++ rest)
  | _ =>
    throwError "Ct.Do: unsupported `do` element (kind: {elem.raw.getKind}){indentD elem}"

partial def elabMonadicAsDoElem
    (elabAtType : Expr → ElabM Expr) (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  match rest with
  | [] =>
    let ctx ← read
    let expectedType ← mkLeakType ctx.expectedAlpha
    let result ← elabAtType expectedType
    synthesizeSyntheticMVarsNoPostponing
    pure result
  | _ =>
    let unitType ← mkConstWithFreshMVarLevels ``Unit
    ElabM.withLocalDeclD `_ unitType fun fvar => do
      let restExpr ← elabDoSeqCore rest
      let body ← mkLambdaFVars #[fvar] restExpr
      let expectedType ← mkLeakType unitType
      let e ← elabAtType expectedType
      mkLeakBind e body

partial def elabDoExpr (term : Term) (rest : List Aeneas.Do.DoElem) : ElabM Expr :=
  elabMonadicAsDoElem (fun ty => elabTermEnsuringType term ty) rest

partial def elabDoLetArrowId (x : Ident) (ty? : Option Term) (rhs : Aeneas.Do.DoElem)
    (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  let nm := x.getId
  let ty ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let expectedType ← mkLeakType ty
  let e ← withReader (fun ctx => { ctx with expectedAlpha := ty }) do
    match rhs with
    | `(doElem| do $seq:doSeq) =>
      let elems ← getDoElems seq
      elabDoSeqCore elems
    | `(doElem| $expr:term) =>
      elabTermEnsuringType expr expectedType
    | _ => do
      let e ← elabDoElem rhs []
      let eType ← instantiateMVars (← inferType e)
      if let some α := eType.getAppArgs[0]? then
        discard <| isDefEq ty α
      pure e
  let ty ← instantiateMVars ty
  ElabM.withLocalDeclD nm ty fun fvar => do
    Term.addLocalVarInfo x fvar
    let restExpr ← elabDoSeqCore rest
    let body ← mkLambdaFVars #[fvar] restExpr
    mkLeakBind e body

partial def elabDoLetArrowPat (pat : Term) (rhs : Aeneas.Do.DoElem) (rest : List Aeneas.Do.DoElem) :
    ElabM Expr := do
  let α ← mkFreshTypeMVar
  let expectedType ← mkLeakType α
  let e ← withReader (fun ctx => { ctx with expectedAlpha := α }) do
    match rhs with
    | `(doElem| do $seq:doSeq) =>
      let elems ← getDoElems seq
      elabDoSeqCore elems
    | `(doElem| $expr:term) =>
      elabTermEnsuringType expr expectedType
    | _ => do
      let e ← elabDoElem rhs []
      let eType ← instantiateMVars (← inferType e)
      if let some a := eType.getAppArgs[0]? then
        discard <| isDefEq α a
      pure e
  let α ← instantiateMVars α
  let shape ← analyzePat pat α
  let k ← mkPatContinuation shape α fun _ => elabDoSeqCore rest
  synthesizeSyntheticMVarsNoPostponing
  mkLeakBind e k

partial def elabDoLetId (x : Ident) (ty? : Option Term) (rhs : Term)
    (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  let nm := x.getId
  let α ← match ty? with
    | some ty => elabType ty
    | none    => mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  ElabM.withLetDecl nm α val fun fvar => do
    Term.addLocalVarInfo x fvar
    let restExpr ← elabDoSeqCore rest
    mkLetFVars #[fvar] restExpr

partial def elabDoLetPat (pat : Term) (rhs : Term)
    (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  let α ← mkFreshTypeMVar
  let val ← elabTermEnsuringType rhs α
  let α ← instantiateMVars α
  let shape ← analyzePat pat α
  let k ← mkPatContinuation shape α fun _ => elabDoSeqCore rest
  synthesizeSyntheticMVarsNoPostponing
  return (mkApp k val).headBeta

/-- An `if/else if/…/else` chain becomes nested `Leak.cond`s. -/
partial def elabDoIfChain (branches : Array (TSyntax ``doIfCond × TSyntax ``doSeq))
    (elseSeq : TSyntax ``doSeq) (rest : List Aeneas.Do.DoElem) : ElabM Expr := do
  let elabAtType (ty : Expr) : ElabM Expr := do
    let some α := ty.getAppArgs[0]?
      | throwError "Ct.Do.elabDoIfChain: expected monadic type, got{indentExpr ty}"
    withReader (fun ctx => { ctx with expectedAlpha := α }) do
      let mut result ← elabDoSeqCore (← getDoElems elseSeq)
      for (c, s) in branches.toList.reverse do
        match c with
        | `(doIfCond| $cond:term) =>
          let thenExpr ← elabDoSeqCore (← getDoElems s)
          let propExpr ← elabIfCondition cond
          result ← mkLeakCond propExpr thenExpr result
        | _ => throwError "Ct.Do: unsupported `if` condition (only `if c then …`){indentD c}"
      return result
  elabMonadicAsDoElem elabAtType rest

partial def elabDoSeqCore : List Aeneas.Do.DoElem → ElabM Expr
  | [] => throwError "Ct.Do: unexpected empty `do` block"
  | elem :: rest => elabDoElem elem rest

end

/-- Run the elaborator against an expected type `Leak α`. -/
def execute (x : ElabM Expr) (α : Expr) : TermElabM Expr :=
  (x.run { expectedAlpha := α }).run pure

/-- `do` blocks of type `Ct.Leak _` (after `whnf`, so also `slhdsa_leak.Result _`). -/
@[term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType? | throwUnsupportedSyntax
  let ty ← instantiateMVars =<< whnf expectedType
  let some α := (match_expr ty with
    | Ct.Leak α => some α
    | _ => none) | throwUnsupportedSyntax
  let `(do $doSeq) := stx | throwUnsupportedSyntax
  let result ← execute (getDoElems doSeq >>= elabDoSeqCore) α
  let result ← Term.ensureHasType expectedType? result
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

end Ct.Do
