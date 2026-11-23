import Ideal.Direct.RomCoreGhost
import Ideal.Direct.S1Prog

/-!
# The joint handler of the coupling (`status/DIRECT.md` §13.1, §13.4 steps 1–2, §14)

The joint handler `J k` of the table of §13.1, on `σJ = DS × (Tc × GS) × (log × flag)`:

* the **D step is taken as is** (`defH k`), then two fresh 256-bit values `h, h'` are drawn;
* the R state is updated **deterministically** from the D step (`updH`, `updP`): an honest
  query `t` caches `O(t) := ansOf t v` (`v` the label of its final node, read by the D step) and
  draws the undrawn ghosts as `splice t h v` (head of `h`, tail of `v`: the hidden part of the
  label) and the inner label `X` (`h`, `h'` when the D value is not fresh); a forger cell is
  classified as by the simulator (`T` cached / `relQ` / `innQ` / fresh) and its R value is the D
  answer `v`;
* the **flag** is raised when the step is not of the tabulated form: an R value that R would
  draw fresh is not fresh on the D side, or an R value that R holds already disagrees with the
  D answer.  The flag is the coupling's `bad`; it is never lowered;
* every query is appended to a **log** (for S1: `s1_trace_S` applies to it).

Proved here: `hm` of `Couple.coupling_le` (**`jm_marg`**: the D-marginal of a step of `J k` is
the step of `defH k`, exactly in distribution), and the **assembly**
`deferCoreGhostSufH_of_parts`: `DeferCoreGhostSufH` follows from
* `DomJ` (step 3 of §13.4: `J k` is dominated by `romGE k` through the R projection until the
  flag), and
* `BadJS` (step 4: the flag, with `¬ Gs.Bad` of the filled D state, has probability at most
  `epsHalf + qs/2^128`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-! ## Nodes, answers, splices -/

/-- The node of a nonempty block list (`walkL` reads it: last block, reversed prefix). -/
def ndOf (bs : List Blk) : MD.Nd Blk := (bs.getLastD default, bs.dropLast.reverse)

/-- The oracle answer of an honest query from the label of its final node. -/
def ansOf : (t : (hashSpec Cr).Domain) → St → (hashSpec Cr).Range t
  | .inl (.thash _ _ _), v => out16 v
  | .inl (.hmsg _ _ _ _), v => dig30 v
  | .inr _, v => out16 v

/-- The head of `h` (the first `ansLen t` bytes) and the tail of `v`. -/
def splice (t : (hashSpec Cr).Domain) (h v : St) : St :=
  Vector.ofFn fun i : Fin 32 => if i.val < ansLen t then h[i] else v[i]

/-- The D-side label table. -/
abbrev LT : Type := ((Empty ⊕ MD.Nd Blk) →ₒ St).QueryCache

/-- The label of a node, `0` if undrawn. -/
def lab (L : LT) (n : MD.Nd Blk) : St := (L (.inr n)).getD 0

/-- The inner node of a two-stage query. -/
def innNd : (hashSpec Cr).Domain → Option (MD.Nd Blk)
  | .inl (.thash _ _ _) => none
  | .inl (.hmsg R ps pr M) => some (ndOf (iblocksH R ps pr M))
  | .inr ⟨k, o, M⟩ => some (ndOf (ikey k :: iblocks o M))

/-- The final node of an honest query, read off the label table (the outer walk of a two-stage
query depends on the inner label). -/
def finNd (L : LT) : (hashSpec Cr).Domain → MD.Nd Blk
  | .inl (.thash ps a xs) => ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2)
  | .inl (.hmsg R ps pr M) => ndOf (oblocksH R ps (lab L (ndOf (iblocksH R ps pr M))))
  | .inr ⟨k, o, M⟩ => ndOf [okey k, oblock (lab L (ndOf (ikey k :: iblocks o M)))]

/-- The R-side honest query of a tagged index (`romGP`'s argument of `honG`), if honest. -/
def honT (k : Bytes 16) : (QT Dsk).Domain → Option (hashSpec Cr).Domain
  | .inl _ => none
  | .inr (.inl (.inl _)) => none
  | .inr (.inl (.inr d)) => some (.inl (PublicHashQuery.thash d.1 (Cr.adrsToKey d.2.1) [k]))
  | .inr (.inr (.inl q)) => some (.inl q)
  | .inr (.inr (.inr t)) => some (.inr ⟨t.1, t.2.1, t.2.2⟩)

/-! ## The joint state and the updates -/

/-- The joint state: the D state, the R state, the query log and the flag. -/
abbrev σJ : Type := DS × (Tc × GS) × (List (QT Dsk).Domain × Bool)

/-- The ghost-label table of the R side. -/
abbrev GLT : Type := ((Empty ⊕ KG) →ₒ St).QueryCache

/-- Draw a ghost if undrawn. -/
def gset (G : GLT) (c : KG) (g : St) : GLT :=
  match G (.inr c) with
  | some _ => G
  | none => G.cacheQuery (.inr c) g

open Classical in
/-- **The R update of an honest query `t`** from the D label tables before (`L`) and after
(`L'`) the step: the new R state and whether the step is off the table (the flag). -/
noncomputable def updH (t : (hashSpec Cr).Domain) (L L' : LT) (r : Tc × GS) (h h' : St) :
    (Tc × GS) × Bool :=
  let n := finNd L' t
  let v := lab L' n
  let fv : Prop := L (.inr n) = none ∧ innNd t ≠ some n
  let X : St := match innNd t with | some m => lab L' m | none => 0
  let fX : Prop := match innNd t with | some m => L (.inr m) = none | none => False
  let C := r.2.1
  let G := r.2.2
  let flag : Prop := match C (.inl t) with
    | none => ¬ fv
    | some y => y ≠ ansOf t v
  let C' : PubG.QueryCache := match C (.inl t) with
    | none => C.cacheQuery (.inl t) (ansOf t v)
    | some _ => C
  let G' := gset (gset G (t, false) (if fv then splice t h v else h)) (t, true)
    (if fX then X else h')
  ((r.1, (C', G')), decide flag)

open Classical in
/-- **The R update of a forger cell `q` tagged `pk`** from the D answer `v` (fresh on the D side
iff `fv`). -/
noncomputable def updP (pk : PublicKeyCore Cr) (q : St × Blk) (v : St) (fv : Prop)
    (r : Tc × GS) (h : St) : (Tc × GS) × Bool :=
  let T := r.1
  let C := r.2.1
  let G := r.2.2
  match T q with
  | some v' => (r, decide (v' ≠ v))
  | none =>
    match relQ pk T q with
    | some t =>
      let fl : Prop := (match C (.inl t) with
          | none => ¬ fv
          | some y => y ≠ ansOf t v) ∨
        (match G (.inr (t, false)) with
          | none => ¬ fv
          | some g => overlay t (ansOf t v) g ≠ v)
      let C' : PubG.QueryCache := match C (.inl t) with
        | none => C.cacheQuery (.inl t) (ansOf t v)
        | some _ => C
      ((T.cacheQuery q v, (C', gset G (t, false) (splice t h v))), decide fl)
    | none =>
      match innQ pk T q with
      | some t =>
        let fl : Prop := match G (.inr (t, true)) with
          | none => ¬ fv
          | some g => g ≠ v
        ((T.cacheQuery q v, (C, gset G (t, true) v)), decide fl)
      | none => ((T.cacheQuery q v, (C, G)), decide (¬ fv))

/-- The update of the R state and the flag after a D step. -/
noncomputable def upd (k : Bytes 16) (t : (QT Dsk).Domain) (d : DS) (a : (QT Dsk).Range t)
    (d' : DS) (r : Tc × GS) (h h' : St) : (Tc × GS) × Bool :=
  match t, a with
  | .inl _, _ => (r, false)
  | .inr (.inl (.inl pq)), v => updP pq.1 pq.2 v (Gs.merge d.1 pq.2 = none) r h
  | t, _ =>
    match honT k t with
    | some u => updH u d.1.2 d'.1.2 r h h'
    | none => (r, false)

/-- **The joint handler.** -/
noncomputable def J (k : Bytes 16) : QueryImpl (QT Dsk) (StateT σJ ProbComp) := fun t =>
  StateT.mk fun s => do
    let z ← (defH k t).run s.1
    let h ← ($ᵗ St : ProbComp St)
    let h' ← ($ᵗ St : ProbComp St)
    let w := upd k t s.1 z.1 z.2 s.2.1 h h'
    pure (z.1, (z.2, w.1, (s.2.2.1 ++ [t], s.2.2.2 || w.2)))

/-- The D projection. -/
def πD (s : σJ) : DS := s.1

/-- The R projection. -/
def πR (s : σJ) : Tc × GS := s.2.1

/-- The flag. -/
def badJ (s : σJ) : Prop := s.2.2.2 = true

/-- The initial joint state. -/
def sJ0 : σJ := (((∅, ∅), []), ((∅ : Tc), ((∅, ∅) : GS)), ([], false))

/-! ## Step 2: the D-marginal -/

theorem J_run (k : Bytes 16) (t : (QT Dsk).Domain) (s : σJ) :
    (J k t).run s = (defH k t).run s.1 >>= fun z => ($ᵗ St : ProbComp St) >>= fun h =>
      ($ᵗ St : ProbComp St) >>= fun h' =>
        pure (z.1, (z.2, (upd k t s.1 z.1 z.2 s.2.1 h h').1,
          (s.2.2.1 ++ [t], s.2.2.2 || (upd k t s.1 z.1 z.2 s.2.1 h h').2))) := rfl

/-- **The D-marginal of a step of `J k` is the step of `defH k`** (`hm` of `coupling_le`). -/
theorem jm_marg (k : Bytes 16) (t : (QT Dsk).Domain) (s : σJ) :
    (fun z => (z.1, πD z.2)) <$> (J k t).run s =ᵈ (defH k t).run (πD s) := by
  rw [J_run]
  simp only [map_bind, map_pure, πD]
  have e : ((defH k t).run s.1 >>= fun z => ($ᵗ St : ProbComp St) >>= fun h =>
      ($ᵗ St : ProbComp St) >>= fun h' => (pure (z.1, z.2) : ProbComp _)) =ᵈ
      ((defH k t).run s.1 >>= fun z => (pure z : ProbComp _)) := by
    refine EvalDistEq.bind_congr_of_support _ fun z _ => ?_
    refine (EvalDistEq.bind_const _ _).trans ?_
    exact EvalDistEq.bind_const _ _
  rw [bind_pure] at e
  exact e

theorem J_preserves_bad (k : Bytes 16) : QueryImpl.PreservesInv (J k) badJ := by
  intro t s hs z hz
  rw [J_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w, -, h, -, h', -, rfl⟩ := hz
  simp only [badJ] at hs ⊢
  simp [hs]

theorem J_preserves_true (k : Bytes 16) : QueryImpl.PreservesInv (J k) (fun _ => True) :=
  fun _ _ _ _ _ => trivial

/-! ## The two remaining statements and the assembly -/

/-- **Step 3 of §13.4 (domination)**: off the flag, a step of `J k` read through the R
projection is dominated by the step of the eager ghost game `romGE k`. -/
def DomJ : Prop :=
  ∀ k : Bytes 16, QueryImpl.DominatedUntilBad (J k) (romGE k) πR (fun _ => True) badJ

/-- **Step 4 of §13.4 (the bad bound), SUF.** -/
def BadJS : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (J k) (PprfST oR ($ᵗ (Bytes 16)) S)).run sJ0
       let st ← RelabelState.endFill (πD z.2)}[badJ z.2 ∧ ¬ Gs.Bad st] ≤
      epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **Step 4 of §13.4 (the bad bound), EUF.** -/
def BadJE : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (J k) (PprfET oR ($ᵗ (Bytes 16)) S)).run sJ0
       let st ← RelabelState.endFill (πD z.2)}[badJ z.2 ∧ ¬ Gs.Bad st] ≤
      epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- The coupling at one secret seed, for any tagged program. -/
theorem couple_k (hd : DomJ) (k : Bytes 16) (P : OracleComp (QT Dsk) Bool) :
    Pr{let z ← (simulateQ (defH k) P).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      Pr{let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] +
        Pr{let z ← (simulateQ (J k) P).run sJ0
           let st ← RelabelState.endFill (πD z.2)}[badJ z.2 ∧ ¬ Gs.Bad st] :=
  coupling_le (J k) (defH k) (romGE k) πD πR (fun _ => True) badJ (J_preserves_true k)
    (J_preserves_bad k) (fun t s _ => jm_marg k t s) (hd k) P sJ0 trivial
    RelabelState.endFill (fun st => ¬ Gs.Bad st)

theorem couple_all (hd : DomJ) (P : OracleComp (QT Dsk) Bool) :
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (defH k) P).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
         let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] +
        Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
           let z ← (simulateQ (J k) P).run sJ0
           let st ← RelabelState.endFill (πD z.2)}[badJ z.2 ∧ ¬ Gs.Bad st] := by
  have h := prEvent_bind_le_add_of_forall_le ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
    (fun k => (simulateQ (defH k) P).run ((∅, ∅), []) >>= fun z =>
      (fun st => (z, st)) <$> RelabelState.endFill z.2)
    (fun k => (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS)))
    (fun k => (simulateQ (J k) P).run sJ0 >>= fun z =>
      (fun st => (z, st)) <$> RelabelState.endFill (πD z.2))
    (fun p => p.1.1 = true ∧ ¬ Gs.Bad p.2) (fun z => z.1 = true)
    (fun p => badJ p.1.2 ∧ ¬ Gs.Bad p.2) (fun k => by
      have := couple_k hd k P
      simpa only [prEvent_norm] using this)
  simpa only [prEvent_norm, bind_assoc] using h

/-- **The assembly (SUF)**: domination and the bad bound give `DeferCoreGhostSufH`. -/
theorem deferCoreGhostSufH_of_parts (hd : DomJ) (hb : BadJS) : DeferCoreGhostSufH := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (couple_all hd _).trans ?_
  rw [add_assoc]
  gcongr
  exact hb S oR qf qs ℓ hqf hqs hlong hout

/-- **The assembly (EUF).** -/
theorem deferCoreGhostEufH_of_parts (hd : DomJ) (hb : BadJE) : DeferCoreGhostEufH := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (couple_all hd _).trans ?_
  rw [add_assoc]
  gcongr
  exact hb S oR qf qs ℓ hqf hqs hlong hout

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.jm_marg
#print axioms Ideal.Direct.Rom.deferCoreGhostSufH_of_parts
#print axioms Ideal.Direct.Rom.deferCoreGhostEufH_of_parts
