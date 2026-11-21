import Ideal.Games.TcrIdeal

/-!
# Multi-block SM-TCR in the ideal-compression model: shared definitions

The joint cache of the ideal game is read as a partial function on cells (`look`); a block list
`(B₁, [B₂, …, B_k])` is evaluated in a cache by `chainVal` (private-row cell `B₁`, then public
cells `(c₁, B₂)`, …).  `MInv` is the invariant that phase two of the multi-block game needs of
the cache after phase one; `build` is the cache that a symbolic state (targets answered by the
private row table alone, hidden intermediate chaining values drawn separately) stands for.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

/-- A cell of the joint cache: a public cell `(c, B)` or a private-row cell `B`. -/
abbrev Cell (St Blk : Type) := (St × Blk) ⊕ Blk

/-- The joint cache as a partial function on cells. -/
def look (c : Cache St Blk) : Cell St Blk → Option St
  | .inl q => c (.inl q)
  | .inr B => c (.inr B)

/-- The joint cache of a partial function on cells. -/
def ofLook (κ : Cell St Blk → Option St) : Cache St Blk :=
  QueryCache.ofFn fun t => match t with
    | .inl q => κ (.inl q)
    | .inr B => κ (.inr B)

@[simp] theorem look_ofLook (κ : Cell St Blk → Option St) : look (ofLook κ) = κ := by
  funext x; cases x <;> rfl

@[simp] theorem ofLook_look (c : Cache St Blk) : ofLook (look c) = c := by
  apply QueryCache.equivFn.injective
  funext x; cases x <;> rfl

theorem look_inl (c : Cache St Blk) (q : St × Blk) : look c (.inl q) = c (.inl q) := rfl

theorem look_inr (c : Cache St Blk) (B : Blk) : look c (.inr B) = c (.inr B) := rfl

theorem look_empty : look (∅ : Cache St Blk) = fun _ => none := by
  funext x; cases x <;> rfl

section Dec

variable [DecidableEq St] [DecidableEq Blk]

theorem look_cacheQuery_inl (c : Cache St Blk) (q : St × Blk) (u : St) :
    look (c.cacheQuery (.inl q) u) = Function.update (look c) (.inl q) (some u) := by
  funext x
  by_cases h : x = .inl q
  · subst h
    rw [Function.update_self]
    exact QueryCache.cacheQuery_self c (.inl q) u
  · rw [Function.update_of_ne h]
    cases x with
    | inl q' => exact QueryCache.cacheQuery_of_ne (t := .inl q) c u h
    | inr B => exact QueryCache.cacheQuery_of_ne (t := .inl q) c u h

theorem look_cacheQuery_inr (c : Cache St Blk) (B : Blk) (u : St) :
    look (c.cacheQuery (.inr B) u) = Function.update (look c) (.inr B) (some u) := by
  funext x
  by_cases h : x = .inr B
  · subst h
    rw [Function.update_self]
    exact QueryCache.cacheQuery_self c (.inr B) u
  · rw [Function.update_of_ne h]
    cases x with
    | inl q' => exact QueryCache.cacheQuery_of_ne (t := .inr B) c u h
    | inr B' => exact QueryCache.cacheQuery_of_ne (t := .inr B) c u h

theorem ofLook_update_inl (κ : Cell St Blk → Option St) (q : St × Blk) (u : St) :
    ofLook (Function.update κ (.inl q) (some u)) = (ofLook κ).cacheQuery (.inl q) u := by
  rw [← ofLook_look ((ofLook κ).cacheQuery (.inl q) u), look_cacheQuery_inl, look_ofLook]

theorem ofLook_update_inr (κ : Cell St Blk → Option St) (B : Blk) (u : St) :
    ofLook (Function.update κ (.inr B) (some u)) = (ofLook κ).cacheQuery (.inr B) u := by
  rw [← ofLook_look ((ofLook κ).cacheQuery (.inr B) u), look_cacheQuery_inr, look_ofLook]

end Dec

/-! ## Chains in a cache -/

/-- Continue a chain from the chaining value `c` through the public cells of the blocks. -/
def walk (κ : Cell St Blk → Option St) : St → List Blk → Option St
  | c, [] => some c
  | c, b :: bs => (κ (.inl (c, b))).bind fun c' => walk κ c' bs

/-- The value of the block list `X` in the cache: the private-row cell of the first block, then
the public cells. -/
def chainVal (κ : Cell St Blk → Option St) (X : Blk × List Blk) : Option St :=
  (κ (.inr X.1)).bind fun c => walk κ c X.2

/-- Distinct cached cells have distinct values. -/
def CInj (κ : Cell St Blk → Option St) : Prop :=
  ∀ x y v, κ x = some v → κ y = some v → x = y

/-- Extension of caches. -/
def CLe (κ κ' : Cell St Blk → Option St) : Prop := ∀ x v, κ x = some v → κ' x = some v

/-- The cache has at most `N` cells. -/
def CFin (κ : Cell St Blk → Option St) (N : ℕ) : Prop :=
  ∃ l : List (Cell St Blk), l.length ≤ N ∧ ∀ x, (κ x).isSome → x ∈ l

/-- **The invariant after phase one.**  The cache is injective, no cached value is `IV`, target
tweaks determine their message, and every target's block list is complete in the cache and is
the only complete block list with `L` continuation blocks whose first block carries the target's
tweak. -/
structure MInv (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak) (L : ℕ)
    (qs : List (Tweak × M)) (κ : Cell St Blk → Option St) : Prop where
  inj : CInj κ
  noIV : ∀ x, κ x ≠ some F.IV
  twfun : ∀ t m m', (t, m) ∈ qs → (t, m') ∈ qs → m = m'
  tgt : ∀ t m, (t, m) ∈ qs → (chainVal κ (F.tch t m)).isSome ∧
    ∀ X : Blk × List Blk, X.2.length = L → btw X.1 = t → (chainVal κ X).isSome → X = F.tch t m

/-! ## The symbolic state of phase one -/

/-- The public cells of a chain with chaining values `vals` and continuation blocks `bs`, with
their values. -/
def pubCells : List St → List Blk → List (Cell St Blk × St)
  | c :: c' :: t, b :: bs => (.inl (c, b), c') :: pubCells (c' :: t) bs
  | _, _ => []

/-- The cells of the block list `X` with chaining values `vals`, with their values. -/
def chainCells (X : Blk × List Blk) : List St → List (Cell St Blk × St)
  | [] => []
  | c :: t => (.inr X.1, c) :: pubCells (c :: t) X.2

/-- Write a list of cells into a cache, in order. -/
def writeAll [DecidableEq St] [DecidableEq Blk] (es : List (Cell St Blk × St))
    (κ : Cell St Blk → Option St) : Cell St Blk → Option St :=
  es.foldl (fun κ e => Function.update κ e.1 (some e.2)) κ

/-- The single-block family: the attacked member keeps only its first block. -/
@[reducible] def THFam.single (F : THFam St Blk PkSeed Tweak M Y ι) :
    THFam St Blk PkSeed Tweak M Y ι :=
  { F with tch := fun t m => ((F.tch t m).1, []) }

/-- The chaining values of a target in the symbolic state: the hidden values `h`, then the value
of the target's private-row cell. -/
def tgtVals (F : THFam St Blk PkSeed Tweak M Y ι) (κ : Cell St Blk → Option St)
    (tm : Tweak × M) (h : List St) : List St :=
  match κ (.inr (F.tch tm.1 tm.2).1) with
  | some v => h ++ [v]
  | none => []

/-- The cells of all targets in the symbolic state. -/
def entries (F : THFam St Blk PkSeed Tweak M Y ι) (κ : Cell St Blk → Option St)
    (qs : List (Tweak × M)) (hs : List (List St)) : List (Cell St Blk × St) :=
  (List.zip qs hs).flatMap fun p => chainCells (F.tch p.1.1 p.1.2) (tgtVals F κ p.1 p.2)

/-- The cache a symbolic state stands for: the chain of each target, through its hidden values
and ending in the value of its private-row cell, is written over the symbolic cache. -/
def build [DecidableEq St] [DecidableEq Blk] (F : THFam St Blk PkSeed Tweak M Y ι)
    (κ : Cell St Blk → Option St) (qs : List (Tweak × M)) (hs : List (List St)) :
    Cell St Blk → Option St :=
  writeAll (entries F κ qs hs) κ

/-- The hidden values are pairwise distinct and no cached public cell lies in a hidden row. -/
def Nice (κ : Cell St Blk → Option St) (hs : List (List St)) : Prop :=
  hs.flatten.Nodup ∧ ∀ h ∈ hs.flatten, ∀ b, κ (.inl (h, b)) = none

/-- The hidden values are pairwise distinct, different from `IV` and from every cached value, and
no cached public cell lies in a hidden row. -/
def FillNice (IV : St) (κ : Cell St Blk → Option St) (hs : List (List St)) : Prop :=
  hs.flatten.Nodup ∧
    ∀ h ∈ hs.flatten, h ≠ IV ∧ (∀ x, κ x ≠ some h) ∧ ∀ b, κ (.inl (h, b)) = none

theorem FillNice.nice {IV : St} {κ : Cell St Blk → Option St} {hs : List (List St)}
    (h : FillNice IV κ hs) : Nice κ hs :=
  ⟨h.1, fun x hx => (h.2 x hx).2.2⟩

/-- The deterministic invariant of the symbolic phase one: the invariant of the single-block
game, pairwise distinct target tweaks, and one list of `L` hidden values per target. -/
structure SInv [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak) (L : ℕ)
    (s : SM_DT_TCR_State Tweak M) (c : Cache St Blk) (hs : List (List St)) : Prop where
  tcr : TcrInv F.single btw s c
  nodup : (s.1.map Prod.fst).Nodup
  len : hs.length = s.1.length
  lenL : ∀ h ∈ hs, h.length = L

/-! ## Drawing the hidden values -/

/-- `n` independent uniform chaining values. -/
noncomputable def drawV [SampleableType St] : ℕ → ProbComp (List St)
  | 0 => pure []
  | n + 1 => do
      let h ← $ᵗ St
      let t ← drawV n
      pure (h :: t)

/-- `n` independent lists of `L` uniform chaining values. -/
noncomputable def drawN [SampleableType St] (L : ℕ) : ℕ → ProbComp (List (List St))
  | 0 => pure []
  | n + 1 => do
      let hs ← drawN L n
      let h ← drawV L
      pure (hs ++ [h])

end Ideal
