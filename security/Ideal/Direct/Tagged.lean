import Ideal.Direct.Entry

/-!
# The tagged program and the tagged lazy table (D1 of `status/DIRECT.md`)

Every compression query of the entry program `progS` (`Direct/Entry.lean`) is given a tag saying
who issues it: `F` (a compression query of the forger, i.e. a port query), `H` (the honest
computation: key generation, the signing oracle, the two compression calls of each `PRF`-game
query), `V` (the final check: verification of the forgery).

* `Tag`, `hT` (tagged compression oracle), `untagI`, `tagWith τ`; `untag_tagWith`.
* `fullH k`: the interpretation of the port program (`chainP`, then `prfOI k`) as one handler;
  `fullT k τ`: the same with every compression query tagged (port queries `F`, `PRF`-game
  queries `H`, hash chains `τ`).
* Phase split of the open SUF/EUF programs: `bRestWOpenP_split`, `bRestOpenP_split` (key
  generation and forger run, then the check).
* `progTS`, `progTE`: the tagged programs (hash chains of the first phase tagged `H`, of the check
  `V`); **`untag_progTS : simulateQ untagI (progTS …) = progS …`**, `untag_progTE`.
* `progTS_F`, `progTE_F`: at most `qf` queries are tagged `F`.
* `tagRom`: the lazy table with a first-reader tag map; **`tagRom_proj`**: its run projects to the
  run of `romImpl` on the untagged program (`untag_eq`), so every probability about the entry
  program can be computed over the tagged table.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Ideal.Direct

open Ideal.Realize.Prf Reduction Reduction.Open
open Ideal.Realize (PortForgerProg isPortQ isSignQ isLongQ)
open Ideal.Realize.Msg (harnP)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Tags -/

/-- Who issues a compression query. -/
inductive Tag
  | F
  | H
  | V
deriving DecidableEq, Repr

/-- The tagged compression oracle. -/
abbrev hT : OracleSpec (Tag × (St × Blk)) := (Tag × (St × Blk)) →ₒ St

/-- The interface of tagged programs. -/
abbrev TSpec := unifSpec + hT

/-- Forget the tags. -/
def untagI : QueryImpl TSpec (OracleComp (unifSpec + hS St Blk))
  | .inl n => (unifSpec + hS St Blk).query (.inl n)
  | .inr tq => (unifSpec + hS St Blk).query (.inr tq.2)

/-- Tag every compression query with `τ`. -/
def tagWith (τ : Tag) : QueryImpl (unifSpec + hS St Blk) (OracleComp TSpec)
  | .inl n => TSpec.query (.inl n)
  | .inr q => TSpec.query (.inr (τ, q))

theorem untag_tagWith (τ : Tag) {α : Type} (X : OracleComp (unifSpec + hS St Blk) α) :
    simulateQ untagI (simulateQ (tagWith τ) X) = X := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [simulateQ_bind, simulateQ_spec_query, ih]
      simp [tagWith, untagI]
    · simp only [simulateQ_bind, simulateQ_spec_query, ih]
      simp [tagWith, untagI]

/-- A tagged query with tag `τ`. -/
def isTag (τ : Tag) : ℕ ⊕ (Tag × (St × Blk)) → Bool
  | .inr tq => decide (tq.1 = τ)
  | _ => false

theorem qb_false {ι α : Type} {spec : OracleSpec ι} (X : OracleComp spec α) :
    IsQueryBoundP X (fun _ => False) 0 := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun u => by simp [ih u]⟩

theorem tagWith_count (τ σ : Tag) {α : Type} (X : OracleComp (unifSpec + hS St Blk) α)
    (h : σ ≠ τ) : IsQueryBoundP (simulateQ (tagWith τ) X) (fun i => isTag σ i = true) 0 := by
  refine IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (qb_false X)
    (fun t ht => ht.elim) (fun t _ => ?_)
  rcases t with n | q
  · dsimp only [tagWith]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isTag] at h
  · dsimp only [tagWith]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h' => by simp [isTag, Ne.symm h] at h'

theorem tagWith_count_le (τ : Tag) {α : Type} (X : OracleComp (unifSpec + hS St Blk) α) (n : ℕ)
    (hX : IsQueryBoundP X (fun i => i.isRight = true) n) :
    IsQueryBoundP (simulateQ (tagWith τ) X) (fun i => isTag τ i = true) n := by
  refine IsQueryBoundP.simulateQ_of_step hX (fun t _ => ?_) (fun t ht => ?_)
  · rcases t with m | q
    · dsimp only [tagWith]
      exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · dsimp only [tagWith]
      exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with m | q
    · dsimp only [tagWith]
      exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [isTag] at h
    · simp at ht

/-! ## The full handler of the port program -/

/-- The port program's interpretation (`chainP`, then the `PRF` oracle by `prfOI k`). -/
noncomputable def fullH (k : Bytes 16) :
    QueryImpl (QSpec Ideal.Realize.Msg.Rd Dsk) (OracleComp (unifSpec + hS St Blk)) := fun t =>
  simulateQ (prfOI k) (chainP t)

/-- The tag of a port-program query: port `F`, `PRF` game `H`, otherwise (hash chains) `τ`. -/
def qTag (τ : Tag) : (QSpec Ideal.Realize.Msg.Rd Dsk).Domain → Tag
  | .inr (.inl (.inl _)) => .F
  | .inr (.inl (.inr _)) => .H
  | _ => τ

/-- The tagged interpretation. -/
noncomputable def fullT (k : Bytes 16) (τ : Tag) :
    QueryImpl (QSpec Ideal.Realize.Msg.Rd Dsk) (OracleComp TSpec) := fun t =>
  simulateQ (tagWith (qTag τ t)) (fullH k t)

theorem untag_fullT (k : Bytes 16) (τ : Tag) {α : Type}
    (X : OracleComp (QSpec Ideal.Realize.Msg.Rd Dsk) α) :
    simulateQ untagI (simulateQ (fullT k τ) X) = simulateQ (fullH k) X := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) X
  exact untag_tagWith _ _

theorem prfOI_chainP (k : Bytes 16) {α : Type} (X : OracleComp (QSpec Ideal.Realize.Msg.Rd Dsk) α) :
    simulateQ (prfOI k) (simulateQ chainP X) = simulateQ (fullH k) X := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k' ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih, fullH]

/-! ## The phase split of the open programs -/

section Split

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)

/-- SUF, first phase: `SK.prf`, key generation, the forger run; returns the root and the run. -/
noncomputable def runWP (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) :
    OracleComp (QSpec prims (D₀ prims))
      (prims.Y × ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims)) :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (QSpec prims (D₀ prims)) prims.SkPrf) >>= fun skPrf =>
    simulateQ embQ (openKeygenP prims pkSeed) >>= fun root =>
      (fun z => (root, z)) <$> (simulateQ (harnP (portQ (prims := prims) (D := D₀ prims))
        (sigSignOracle (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run []

/-- SUF, second phase: the final check. -/
noncomputable def chkWP (wO : OpenCheck vp prims) (pkSeed : prims.PkSeed)
    (rz : prims.Y × ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims)) :
    OracleComp (QSpec prims (D₀ prims)) Bool :=
  simulateQ embQ (simulateQ (hashEmb prims (D₀ prims)) (wO ⟨pkSeed, rz.1⟩ rz.2.1 rz.2.2))

theorem bRestWOpenP_split (wO : OpenCheck vp prims) (mainP : PortForgerProg vp prims)
    (pkSeed : prims.PkSeed) :
    bRestWOpenP optRand wO mainP pkSeed = runWP optRand mainP pkSeed >>= chkWP wO pkSeed := by
  simp only [bRestWOpenP, runWP, chkWP, bind_assoc, bind_map_left]

/-- EUF, first phase. -/
noncomputable def runEP (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) :
    OracleComp (QSpec prims (D₀ prims))
      (prims.Y × ((List Byte × GeneralScheme.SignatureCore vp prims.core) × List (List Byte))) :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (QSpec prims (D₀ prims)) prims.SkPrf) >>= fun skPrf =>
    simulateQ embQ (openKeygenP prims pkSeed) >>= fun root =>
      (fun z => (root, z)) <$> (simulateQ (harnP (portQ (prims := prims) (D := D₀ prims))
        (harnessSignOracle (vp := vp) (prims := prims)
          (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run []

/-- EUF, second phase: verification and freshness. -/
noncomputable def chkEP (pkSeed : prims.PkSeed)
    (rz : prims.Y × ((List Byte × GeneralScheme.SignatureCore vp prims.core) × List (List Byte))) :
    OracleComp (QSpec prims (D₀ prims)) Bool :=
  simulateQ embQ (simulateQ (hashEmb prims (D₀ prims))
    (GeneralScheme.verifyInternalM vp prims.core rz.2.1.1 rz.2.1.2 ⟨pkSeed, rz.1⟩ :
      OracleComp (publicHashSpec prims.core) Bool)) >>= fun v =>
    pure (decide (rz.2.1.1 ∉ rz.2.2) && v)

theorem bRestOpenP_split (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) :
    bRestOpenP optRand mainP pkSeed = runEP optRand mainP pkSeed >>= chkEP pkSeed := by
  simp only [bRestOpenP, runEP, chkEP, bind_assoc, bind_map_left]

end Split

/-! ## The tagged programs -/

section Programs

open Ideal.Realize.Msg (Rd optRand₀ mainC)

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

/-- The domain restriction of the realisers. -/
noncomputable abbrev Rs := restrictP (prims := Rd) (skRestrict Link.vp Rd)

/-- **The tagged SUF program**: key generation, signing and `PRF` calls tagged `H`, the forger's
compression queries `F`, the final check `V`. -/
noncomputable def progTS : OracleComp TSpec Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp TSpec _)
  let pkSeed ← simulateQ (fullT k .H) (simulateQ Rs
    (liftM pkSeedDist : OracleComp (QSpec Rd (D₀ Rd)) Rd.PkSeed))
  let rz ← simulateQ (fullT k .H) (simulateQ Rs (runWP (optRand₀ oR) (mainC S) pkSeed))
  simulateQ (fullT k .V) (simulateQ Rs (chkWP sufCheckOpen pkSeed rz))

/-- **The tagged EUF program.** -/
noncomputable def progTE : OracleComp TSpec Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp TSpec _)
  let pkSeed ← simulateQ (fullT k .H) (simulateQ Rs
    (liftM pkSeedDist : OracleComp (QSpec Rd (D₀ Rd)) Rd.PkSeed))
  let rz ← simulateQ (fullT k .H) (simulateQ Rs (runEP (optRand₀ oR) (mainC S) pkSeed))
  simulateQ (fullT k .V) (simulateQ Rs (chkEP pkSeed rz))

theorem untagI_liftM {α : Type} (ob : ProbComp α) :
    simulateQ untagI (liftM ob : OracleComp TSpec α) =
      (liftM ob : OracleComp (unifSpec + hS St Blk) α) := by
  induction ob using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, ih]
    congr 1

theorem untag_split (k : Bytes 16) {α β γ : Type} (A : OracleComp (QSpec Rd Dsk) α)
    (B : α → OracleComp (QSpec Rd Dsk) β) (C : α → β → OracleComp (QSpec Rd Dsk) γ) :
    (simulateQ untagI (simulateQ (fullT k .H) A) >>= fun x =>
      simulateQ untagI (simulateQ (fullT k .H) (B x)) >>= fun y =>
        simulateQ untagI (simulateQ (fullT k .V) (C x y))) =
      simulateQ (fullH k) (A >>= fun x => B x >>= C x) := by
  rw [simulateQ_bind, untag_fullT]
  refine bind_congr fun x => ?_
  rw [simulateQ_bind, untag_fullT]
  refine bind_congr fun y => ?_
  rw [untag_fullT]

theorem PprfS_split :
    (simulateQ Rs (liftM pkSeedDist : OracleComp (QSpec Rd (D₀ Rd)) Rd.PkSeed) >>= fun pkSeed =>
      simulateQ Rs (runWP (optRand₀ oR) (mainC S) pkSeed) >>= fun rz =>
        simulateQ Rs (chkWP sufCheckOpen pkSeed rz)) = PprfS S oR pkSeedDist := by
  unfold PprfS bPrfWCOpenP bPrfWOpenP
  rw [simulateQ_bind]
  refine bind_congr fun pkSeed => ?_
  rw [bRestWOpenP_split, simulateQ_bind]

theorem PprfE_split :
    (simulateQ Rs (liftM pkSeedDist : OracleComp (QSpec Rd (D₀ Rd)) Rd.PkSeed) >>= fun pkSeed =>
      simulateQ Rs (runEP (optRand₀ oR) (mainC S) pkSeed) >>= fun rz =>
        simulateQ Rs (chkEP pkSeed rz)) = PprfE S oR pkSeedDist := by
  unfold PprfE bPrfCOpenP bPrfOpenP
  rw [simulateQ_bind]
  refine bind_congr fun pkSeed => ?_
  rw [bRestOpenP_split, simulateQ_bind]

/-- **Untagging the tagged SUF program gives the entry program.** -/
theorem untag_progTS : simulateQ untagI (progTS S oR pkSeedDist) = progS S oR pkSeedDist := by
  unfold progTS progS progOf
  simp only [simulateQ_bind, untagI_liftM]
  refine bind_congr fun k => ?_
  refine (untag_split k _ _ _).trans ?_
  refine (congrArg (simulateQ (fullH k)) (PprfS_split S oR pkSeedDist)).trans ?_
  exact (prfOI_chainP k _).symm

/-- **Untagging the tagged EUF program gives the entry program.** -/
theorem untag_progTE : simulateQ untagI (progTE S oR pkSeedDist) = progE S oR pkSeedDist := by
  unfold progTE progE progOf
  simp only [simulateQ_bind, untagI_liftM]
  refine bind_congr fun k => ?_
  refine (untag_split k _ _ _).trans ?_
  refine (congrArg (simulateQ (fullH k)) (PprfE_split S oR pkSeedDist)).trans ?_
  exact (prfOI_chainP k _).symm

/-! ## The forger's queries -/

section Count

theorem fullT_step_F (k : Bytes 16) (τ : Tag) (hτ : τ ≠ .F) (t : (QSpec Rd Dsk).Domain) :
    IsQueryBoundP (fullT k τ t) (fun i => isTag .F i = true)
      (if (qPort : (QSpec Rd Dsk).Domain → Prop) t then 1 else 0) := by
  rcases t with n | (q | d) | (h | m)
  · simpa [fullT, qTag, qPort, liftQ] using tagWith_count τ .F _ (Ne.symm hτ)
  · simp only [qPort, liftQ, ite_true]
    refine tagWith_count_le .F _ 1 ?_
    simp only [fullH, chainP]
    rw [simulateQ_spec_query]
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · simpa [fullT, qTag, qPort, liftQ] using tagWith_count .H .F _ (by decide)
  · simpa [fullT, qTag, qPort, liftQ] using tagWith_count τ .F _ (Ne.symm hτ)
  · simpa [fullT, qTag, qPort, liftQ] using tagWith_count τ .F _ (Ne.symm hτ)

/-- Transfer of a port bound through the tagged interpretation, with a continuation. -/
theorem fullT_bind_F (k : Bytes 16) (τ : Tag) (hτ : τ ≠ .F) {α β γ : Type}
    (X : OracleComp (QSpec Rd Dsk) α) (g : α → OracleComp (QSpec Rd Dsk) β)
    (f : α → OracleComp TSpec γ)
    (hf : ∀ x m, IsQueryBoundP (g x) qPort m → IsQueryBoundP (f x) (fun i => isTag .F i = true) m)
    (n : ℕ) (h : IsQueryBoundP (X >>= g) qPort n) :
    IsQueryBoundP (simulateQ (fullT k τ) X >>= f) (fun i => isTag .F i = true) n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure x => simpa using hf x n (by simpa using h)
  | query_bind t k' ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    refine (isQueryBoundP_bind (fullT_step_F k τ hτ t) fun u _ => ih u _ (h.2 u)).mono ?_
    by_cases hp : (qPort : (QSpec Rd Dsk).Domain → Prop) t
    · have := h.1.resolve_left (not_not.2 hp)
      simp only [hp, ite_true]; omega
    · simp [hp]

theorem fullT_F (k : Bytes 16) (τ : Tag) (hτ : τ ≠ .F) {α : Type}
    (X : OracleComp (QSpec Rd Dsk) α) (n : ℕ) (h : IsQueryBoundP X qPort n) :
    IsQueryBoundP (simulateQ (fullT k τ) X) (fun i => isTag .F i = true) n := by
  have := fullT_bind_F k τ hτ X pure pure (fun _ m _ => by simp) n (by simpa using h)
  simpa using this

theorem liftM_tag_count {α : Type} (ob : ProbComp α) (σ : Tag) :
    IsQueryBoundP (liftM ob : OracleComp TSpec α) (fun i => isTag σ i = true) 0 :=
  liftM_zeroG ob _ fun n => by simp [isTag]

variable {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **The tagged SUF program makes at most `qf` queries tagged `F`.** -/
theorem progTS_F : IsQueryBoundP (progTS S oR pkSeedDist) (fun i => isTag .F i = true) qf := by
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  have hP := bPrfWCOpenP_port (optRand₀ oR) pkSeedDist hF
  have hP' := hP
  rw [show bPrfWCOpenP (optRand₀ oR) pkSeedDist sufCheckOpen (mainC S) = PprfS S oR pkSeedDist
    from rfl, ← PprfS_split] at hP'
  unfold progTS
  refine (isQueryBoundP_bind (m := qf) (liftM_tag_count _ .F) fun k _ => ?_).mono (by simp)
  refine fullT_bind_F k .H (by decide) _ _ _ (fun pkSeed m hm => ?_) qf hP'
  exact fullT_bind_F k .H (by decide) _ _ _ (fun rz m' hm' => fullT_F k .V (by decide) _ m' hm')
    m hm

/-- **The tagged EUF program makes at most `qf` queries tagged `F`.** -/
theorem progTE_F : IsQueryBoundP (progTE S oR pkSeedDist) (fun i => isTag .F i = true) qf := by
  have hF := Ideal.Realize.Msg.mainC_bounds S hqf hqs hlong hout
  have hP := bPrfCOpenP_port (optRand₀ oR) pkSeedDist hF
  have hP' := hP
  rw [show bPrfCOpenP (optRand₀ oR) pkSeedDist (mainC S) = PprfE S oR pkSeedDist
    from rfl, ← PprfE_split] at hP'
  unfold progTE
  refine (isQueryBoundP_bind (m := qf) (liftM_tag_count _ .F) fun k _ => ?_).mono (by simp)
  refine fullT_bind_F k .H (by decide) _ _ _ (fun pkSeed m hm => ?_) qf hP'
  exact fullT_bind_F k .H (by decide) _ _ _ (fun rz m' hm' => fullT_F k .V (by decide) _ m' hm')
    m hm

end Count

end Programs

/-! ## The tagged lazy table -/

section TagRom

/-- State of the tagged lazy table: the cache, and the tag of the first reader of each cell. -/
abbrev TCache := (hS St Blk).QueryCache × (St × Blk → Option Tag)

/-- **The tagged lazy table**: a cached cell is answered from the cache; a fresh cell is sampled,
cached, and its first reader's tag recorded. -/
noncomputable def tagRom : QueryImpl TSpec (StateT TCache ProbComp)
  | .inl n => StateT.mk fun s => (fun u => (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr tq => StateT.mk fun s =>
      match s.1 tq.2 with
      | some u => pure (u, s)
      | none => ($ᵗ St : ProbComp St) >>= fun u =>
          pure (u, (s.1.cacheQuery tq.2 u, Function.update s.2 tq.2 (some tq.1)))

/-- Generic state projection: if every step of `h₂` projects to the step of `h₁`, so does every
run. -/
theorem run_proj {ι σ₁ σ₂ α : Type} {spec : OracleSpec ι}
    (h₁ : QueryImpl spec (StateT σ₁ ProbComp)) (h₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₂ → σ₁)
    (hstep : ∀ t s, (fun z => (z.1, proj z.2)) <$> (h₂ t).run s = (h₁ t).run (proj s))
    (X : OracleComp spec α) (s : σ₂) :
    (fun z => (z.1, proj z.2)) <$> (simulateQ h₂ X).run s = (simulateQ h₁ X).run (proj s) := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, ← hstep, bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 z.2

theorem tagRom_step (t : TSpec.Domain) (s : TCache) :
    (fun z => (z.1, z.2.1)) <$> (tagRom t).run s =
      (simulateQ (hS St Blk).romImpl (untagI t)).run s.1 := by
  rcases t with n | ⟨τ, q⟩
  · simp only [tagRom, untagI, StateT.run_mk, Functor.map_map]
    rw [simulateQ_spec_query]
    exact (roSim.run_apply_inl _ n s.1).symm
  · simp only [tagRom, untagI, StateT.run_mk]
    rw [simulateQ_spec_query, OracleSpec.romImpl_apply_inr, randomOracle.run_eq]
    cases h : s.1 q with
    | some u => simp
    | none => simp

/-- **The tagged table projects to the lazy table of the untagged program.** -/
theorem untag_eq {α : Type} (X : OracleComp TSpec α) (s : TCache) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ tagRom X).run s =
      (simulateQ (hS St Blk).romImpl (simulateQ untagI X)).run s.1 := by
  rw [run_proj (fun t => simulateQ (hS St Blk).romImpl (untagI t)) tagRom Prod.fst tagRom_step]
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-- The entry program's success probability over the tagged table. -/
theorem prT_lazy_eq_tag (X : OracleComp TSpec Bool) :
    HP.prT ((simulateQ (hS St Blk).romImpl (simulateQ untagI X)).run' ∅) =
      HP.prT ((simulateQ tagRom X).run' (∅, fun _ => none)) := by
  have h := congrArg (fun m => Prod.fst <$> m) (untag_eq X (∅, fun _ => none))
  simp only [Functor.map_map] at h
  simp only [StateT.run'_eq]
  exact congrArg HP.prT h.symm

end TagRom

/-- **Entry point over the tagged table (SUF).** -/
theorem sufI_le_tag (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    sufI S (optRandU oR) pkSeedDist ≤
      HP.prT ((simulateQ tagRom (progTS S oR pkSeedDist)).run' (∅, fun _ => none)) := by
  refine (sufI_le_lazy S oR pkSeedDist).trans (le_of_eq ?_)
  rw [← prT_lazy_eq_tag, untag_progTS]

/-- **Entry point over the tagged table (EUF).** -/
theorem eufI_le_tag (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    eufI S (optRandU oR) pkSeedDist ≤
      HP.prT ((simulateQ tagRom (progTE S oR pkSeedDist)).run' (∅, fun _ => none)) := by
  refine (eufI_le_lazy S oR pkSeedDist).trans (le_of_eq ?_)
  rw [← prT_lazy_eq_tag, untag_progTE]

end Ideal.Direct

#print axioms Ideal.Direct.untag_progTS
#print axioms Ideal.Direct.untag_progTE
#print axioms Ideal.Direct.progTS_F
#print axioms Ideal.Direct.progTE_F
#print axioms Ideal.Direct.untag_eq
#print axioms Ideal.Direct.sufI_le_tag
#print axioms Ideal.Direct.eufI_le_tag
