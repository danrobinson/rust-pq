import MIdeal.CellCollision
import MIdeal.SkPrf

namespace MIdeal.SingletonHash
open Ideal Ideal.HP MLink SLHDSA SLHDSA.Concrete OracleComp OracleSpec ENNReal
open SkPrf
variable (S : Sha2Set)

abbrev Reader := CellCollision.Reader (St × Blk) St
abbrev Candidate := S.Node × Bytes 22 × S.Node × S.Node

def value (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (x : S.Node) : S.Node :=
  (tablePrimitives g S.vp.params).Thash pk a [x]

theorem value_eq (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (x : S.Node) :
    value S g pk a x = output S (g.1 (g.1 (IV128,seedBlock S pk),singletonBlock S a x)) := by
  apply Eq.trans _ (singleton_shape S g.1 pk a x)
  change sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk a [x] = _
  simp only [sha2ThashMixed, sha2ThashG, List.length_cons, List.length_nil, ite_true]

theorem block_injective (a : Bytes 22) : Function.Injective (singletonBlock S a) := by
  intro x y h
  have e := congrArg Vector.toList h
  change _ ++ tailL _ = _ ++ tailL _ at e
  exact Vector.toList_inj.mp (List.append_cancel_left (List.append_cancel_right e))

def selectCells (A : Reader (Candidate S)) : Reader ((St × Blk) × (St × Blk)) := do
  let (pk,a,x,y) ← A
  let c ← (unifSpec + hS St Blk).query (.inr (IV128,seedBlock S pk))
  return ((c,singletonBlock S a x),(c,singletonBlock S a y))

theorem select_bound (A : Reader (Candidate S)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    IsQueryBoundP (selectCells S A) (fun i => i.isRight = true) (q+1) := by
  apply isQueryBoundP_bind hq
  rintro ⟨pk,a,x,y⟩ _
  simp [isQueryBoundP_query_bind_iff]

private theorem answer (g : CF St Blk) (t : St × Blk) :
    ansImpl (spec := hS St Blk) g (.inr t) = pure (g t) := rfl

theorem bound (g512 : CF Chain512 Block512) (A : Reader (Candidate S)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => i.isRight = true) q) :
    prT ($ᵗ (CF St Blk) >>= fun g => simulateQ (ansImpl (spec := hS St Blk) g) A >>= fun p =>
      pure (decide (p.2.2.1 ≠ p.2.2.2 ∧ value S (g,g512) p.1 p.2.1 p.2.2.1 = value S (g,g512) p.1 p.2.1 p.2.2.2))) ≤
      (((q+3)^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  have h := CellCollision.bound (output S) (output S IV128) (balanced S) (selectCells S A) _ (select_bound S A q hq)
  refine le_trans ?_ (h.trans (le_of_eq ?_))
  · apply prT_bind_mono
    intro g _
    simp only [selectCells, simulateQ_bind, bind_assoc]
    apply prT_bind_mono
    rintro ⟨pk,a,x,y⟩ _
    simp only [simulateQ_spec_query, simulateQ_pure, answer, pure_bind, value_eq]
    have equiv (c : St) : ((c,singletonBlock S a x) ≠ (c,singletonBlock S a y)) ↔ x ≠ y := by
      constructor
      · intro h e; exact h (by rw [e])
      · intro h e; exact h (block_injective S a (congrArg Prod.snd e))
    simp only [equiv]
    exact le_rfl
  · rw [card_bytes, Nat.cast_pow, pow_mul]
    norm_num

/-- The SHA-256 reader for F uses the public seed and terminal compression calls. -/
def readF (pk : S.Node) (a : Bytes 22) (x : S.Node) : Reader S.Node := do
  let c ← (unifSpec + hS St Blk).query (.inr (IV128,seedBlock S pk))
  let v ← (unifSpec + hS St Blk).query (.inr (c,singletonBlock S a x))
  return output S v

theorem readF_eval (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (x : S.Node) :
    simulateQ (ansImpl (spec := hS St Blk) g.1) (readF S pk a x) = pure (value S g pk a x) := by
  simp only [readF, simulateQ_bind, simulateQ_spec_query, answer, pure_bind, simulateQ_pure, value_eq]

theorem readF_bound (pk : S.Node) (a : Bytes 22) (x : S.Node) :
    IsQueryBoundP (readF S pk a x) (fun i => i.isRight = true) 2 := by
  simp [readF, isQueryBoundP_query_bind_iff]

def oneNode (xs : {l : List S.Node // l.length = 1}) : S.Node := xs.val[0]'(by rw [xs.property]; decide)

theorem oneNode_eq (xs : {l : List S.Node // l.length = 1}) : xs.val = [oneNode S xs] := by
  obtain ⟨l,h⟩ := xs
  obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp h
  rfl

/-- For the four wider sets, all other collection arities use only the fixed SHA-512 table. -/
def readCollection (d : CF Chain512 Block512) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) : Reader S.Node :=
  if h : xs.length = 1 then readF S pk a (oneNode S ⟨xs,h⟩)
  else pure (byteArrayPrefixOrZero (sha512G (lift512 d) (sha2Prefix512Key pk a ++ concatBytes xs)) S.vp.params.n)

theorem collection_eval (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :
    simulateQ (ansImpl (spec := hS St Blk) g.1) (readCollection S g.2 pk a xs) =
      pure ((tablePrimitives g S.vp.params).Thash pk a xs) := by
  by_cases h : xs.length = 1
  · rw [readCollection, dif_pos h, readF_eval]
    exact congrArg (fun l => pure ((tablePrimitives g S.vp.params).Thash pk a l)) (oneNode_eq S ⟨xs,h⟩).symm
  · rw [readCollection, dif_neg h, simulateQ_pure]
    change _ = pure (sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk a xs)
    simp only [sha2ThashMixed, ite_eq_right h, ite_eq_right hw]

theorem collection_bound (d : CF Chain512 Block512) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :
    IsQueryBoundP (readCollection S d pk a xs) (fun i => i.isRight = true) 2 := by
  unfold readCollection
  split
  · apply readF_bound
  · simp
end MIdeal.SingletonHash
