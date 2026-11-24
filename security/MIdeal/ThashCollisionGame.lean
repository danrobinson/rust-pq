import MIdeal.ThashCollision

namespace MIdeal.Sha512
open Ideal Ideal.HP Ideal.Itsr Ideal.Prf MLink SLHDSA OracleComp OracleSpec ENNReal
variable (S : Sha2Set)

abbrev SHAReader := OracleComp (unifSpec + hS Chain512 Block512)

def readPath (c : Chain512) : List Block512 → SHAReader Chain512
  | [] => pure c
  | b::bs => liftM ((unifSpec + hS Chain512 Block512).query (.inr (c,b))) >>= fun st => readPath st bs

def updateLog (g : CF Chain512 Block512) (c : Chain512) : List Block512 → List Cell → List Cell
  | [], l => l
  | b::bs, l => updateLog g (g (c,b)) bs (logU id (c,b) l)

theorem updateLog_contains (g : CF Chain512 Block512) (c : Chain512) (bs : List Block512) (l : List Cell) :
    ∀ t, t ∈ l ∨ t ∈ mdCells g c bs → t ∈ updateLog g c bs l := by
  induction bs generalizing c l with
  | nil => simp [updateLog, mdCells]
  | cons b bs ih =>
    intro t ht
    apply ih
    rcases ht with ht|ht
    · exact Or.inl (subset_logU id _ _ _ ht)
    · rcases List.mem_cons.mp ht with rfl|h
      · exact Or.inl (mem_logU id _ _)
      · exact Or.inr h

theorem readPath_run (g : CF Chain512 Block512) (c : Chain512) (bs : List Block512) (l : List Cell) :
    (simulateQ (stImpl (spec := hS Chain512 Block512) g (logU id)) (readPath c bs)).run l =
      pure (mdFold g c bs, updateLog g c bs l) := by
  induction bs generalizing c l with
  | nil => simp [readPath, updateLog, mdFold]
  | cons b bs ih =>
    rw [readPath, run_stImpl_inr_bind, ih]; rfl

theorem readPath_bound (c : Chain512) (bs : List Block512) :
    IsQueryBoundP (readPath c bs) (fun i => i.isRight = true) bs.length := by
  induction bs generalizing c with
  | nil => simp [readPath]
  | cons b bs ih =>
    rw [readPath, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr (by simp), fun st => by simpa using ih st⟩

abbrev HashInput (arity : ℕ) := S.Node × Bytes 22 × {xs : List S.Node // xs.length = arity}

def inputPath {arity} (x : HashInput S arity) := path S x.1 x.2.1 x.2.2.val

theorem inputPath_length {arity} (x : HashInput S arity) :
    (inputPath S x).length = (38 + S.vp.params.n * arity)/128 + 2 := by
  simp [inputPath, path, thashBlocks_length, x.2.2.property]

def validatePair {arity} (x y : HashInput S arity) : SHAReader Bool := do
  let h ← readPath initial (inputPath S x)
  let h' ← readPath initial (inputPath S y)
  return decide (x ≠ y ∧ trunc S h = trunc S h')

def checkPair (arity : ℕ) (A : SHAReader (HashInput S arity × HashInput S arity)) : SHAReader Bool := do
  let (x,y) ← A
  validatePair S x y

theorem checkPair_bound (arity q : ℕ) (A : SHAReader (HashInput S arity × HashInput S arity))
    (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    IsQueryBoundP (checkPair S arity A) (fun i => i.isRight = true)
      (q + 2*((38+S.vp.params.n*arity)/128+2)) := by
  unfold checkPair
  apply isQueryBoundP_bind hq
  rintro ⟨x,y⟩ _
  unfold validatePair
  rw [two_mul, ← inputPath_length S x, show (inputPath S x).length = (inputPath S y).length from
    (inputPath_length S x).trans (inputPath_length S y).symm]
  apply isQueryBoundP_bind ((readPath_bound _ _).mono (le_of_eq ((inputPath_length S x).trans (inputPath_length S y).symm)))
  intro h _
  exact (isQueryBoundP_bind (m := 0) (readPath_bound _ _) (fun _ _ => by simp)).mono (by omega)

def value {arity} (g : CompressionTables) (x : HashInput S arity) : S.Node :=
  (tablePrimitives g S.vp.params).Thash x.1 x.2.1 x.2.2.val

theorem value_eq {arity} (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (hm : arity ≠ 1)
    (x : HashInput S arity) : value S g x = trunc S (mdFold g.2 initial (inputPath S x)) :=
  thash_wide S g hw _ _ _ (by rw [x.2.2.property]; exact hm)

def pairLog {arity} (g : CF Chain512 Block512) (x y : HashInput S arity) (l : List Cell) :=
  updateLog g initial (inputPath S y) (updateLog g initial (inputPath S x) l)

theorem validatePair_run {arity} (g : CompressionTables) (hw : S.vp.params.n ≠ 16)
    (hm : arity ≠ 1) (x y : HashInput S arity) (l : List Cell) :
    (simulateQ (stImpl (spec := hS Chain512 Block512) g.2 (logU id)) (validatePair S x y)).run l =
      pure (decide (x ≠ y ∧ value S g x = value S g y), pairLog S g.2 x y l) := by
  simp only [validatePair, simulateQ_bind, StateT.run_bind, readPath_run, pure_bind,
    simulateQ_pure, StateT.run_pure, value_eq S g hw hm, pairLog]

theorem pairLog_bad {arity} (g : CompressionTables) (hw : S.vp.params.n ≠ 16)
    (hm : arity ≠ 1) (x y : HashInput S arity) (l : List Cell) (hd : x ≠ y)
    (he : value S g x = value S g y) :
    badV (trunc S initial) ((pairLog S g.2 x y l).map fun t => trunc S (g.2 t)) = true := by
  refine thash_collision S g hw x.1 y.1 x.2.1 y.2.1 x.2.2.val y.2.2.val
    (by simpa [x.2.2.property] using hm) (by simpa [y.2.2.property] using hm) _ ?_ ?_ he ?_
  · intro t ht
    exact updateLog_contains _ _ _ _ _ (Or.inl (updateLog_contains _ _ _ _ _ (Or.inr ht)))
  · intro t ht
    exact updateLog_contains _ _ _ _ _ (Or.inr ht)
  · intro h
    apply hd
    exact Prod.ext (Prod.mk.inj h).1 (Prod.ext (Prod.mk.inj (Prod.mk.inj h).2).1
      (Subtype.ext (Prod.mk.inj (Prod.mk.inj h).2).2))

/-- Collision resistance of the actual fixed-arity SHA-512 tweakable hash against
an adaptive classical compression reader. Both candidate hashes are charged. -/
theorem collision_bound (g256 : CF St Blk) (hw : S.vp.params.n ≠ 16) (arity q : ℕ) (hm : arity ≠ 1)
    (A : SHAReader (HashInput S arity × HashInput S arity))
    (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g =>
      simulateQ (ansImpl (spec := hS Chain512 Block512) g) A >>= fun p =>
        pure (decide (p.1 ≠ p.2 ∧ value S (g256,g) p.1 = value S (g256,g) p.2))) ≤
      (((q + 2*((38+S.vp.params.n*arity)/128+2))^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  apply le_trans _ (badPrefix_bound S (spec := hS Chain512 Block512) id (fun g t => g t)
    (fun _ _ _ h => h) (checkPair S arity A) _ (checkPair_bound S arity q A hq))
  apply prT_bind_mono
  intro g _
  rw [← fst_map_run_stImpl (spec := hS Chain512 Block512) g (logU id) A []]
  simp only [checkPair, simulateQ_bind, StateT.run_bind, bind_assoc, bind_map_left]
  apply prT_bind_mono
  rintro ⟨⟨x,y⟩,l⟩ _
  rw [validatePair_run S (g256,g) hw hm, pure_bind]
  by_cases h : x ≠ y ∧ value S (g256,g) x = value S (g256,g) y
  · rw [pairLog_bad S (g256,g) hw hm x y l h.1 h.2]
    simp [h, prT_pure]
  · simp [h, prT_pure]

end MIdeal.Sha512
