import Integration.SlhDsaCompressionCost

namespace Reduction.Compression.ClassCollision
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive
open MIdeal.Sha512

abbrev Cell := Chain512 × Block512

variable (S : Sha2Set)

/-- Scan equal-length SHA-512 paths in parallel and return the first distinct
compression inputs whose outputs agree on the public digest prefix. -/
def scan (g : CF Chain512 Block512) (c d : Chain512) :
    List Block512 → List Block512 → Option (Cell × Cell)
  | b :: bs, e :: es =>
    let u := (c,b)
    let v := (d,e)
    if u ≠ v ∧ trunc S (g u) = trunc S (g v) then some (u,v)
    else scan g (g u) (g v) bs es
  | _, _ => none

theorem scan_sound (g : CF Chain512 Block512) (c d : Chain512) (bs es : List Block512)
    (u v : Cell) (h : scan S g c d bs es = some (u,v)) :
    u ≠ v ∧ trunc S (g u) = trunc S (g v) := by
  induction bs generalizing c d es with
  | nil => simp [scan] at h
  | cons b bs ih =>
    cases es with
    | nil => simp [scan] at h
    | cons e es =>
      simp only [scan] at h
      split at h
      · rename_i hit
        cases h
        exact hit
      · exact ih _ _ _ h

private theorem scan_none (g : CF Chain512 Block512) (c d : Chain512) (bs es : List Block512)
    (len : bs.length = es.length) (ne : bs ≠ []) (h : scan S g c d bs es = none)
    (eq : trunc S (mdFold g c bs) = trunc S (mdFold g d es)) : c = d ∧ bs = es := by
  induction bs generalizing c d es with
  | nil => contradiction
  | cons b bs ih =>
    cases es with
    | nil => simp at len
    | cons e es =>
      simp only [scan] at h
      split at h
      · contradiction
      · rename_i miss
        simp only [List.length_cons, Nat.succ.injEq] at len
        change trunc S (mdFold g (g (c,b)) bs) = trunc S (mdFold g (g (d,e)) es) at eq
        have next : trunc S (g (c,b)) = trunc S (g (d,e)) ∧ bs = es := by
          by_cases empty : bs = []
          · subst bs
            have he : es = [] := List.length_eq_zero_iff.mp len.symm
            subst es
            exact ⟨eq,rfl⟩
          · obtain ⟨hg,he⟩ := ih _ _ _ len empty h eq
            exact ⟨congrArg (trunc S) hg,he⟩
        have cell : (c,b) = (d,e) := by
          by_contra diff
          exact miss ⟨diff,next.1⟩
        exact ⟨congrArg Prod.fst cell,congrArg₂ List.cons (congrArg Prod.snd cell) next.2⟩

def extract (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (xs ys : List S.Node) :=
  let c := g.2 (initial, seedBlock S pk)
  scan S g.2 c c (thashBlocks S a xs) (thashBlocks S a ys)

/-- Every valid class-TCR collision of fixed nonsingleton arity yields an actual
pair of distinct SHA-512 cells with colliding prefixes, for each fixed table. -/
theorem extract_collision (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (pk : S.Node)
    (a : Bytes 22) (xs ys : List S.Node) (arity : xs.length = ys.length)
    (hn : xs.length ≠ 1) (diff : xs ≠ ys)
    (win : (tablePrimitives g S.vp.params).Thash pk a xs =
      (tablePrimitives g S.vp.params).Thash pk a ys) :
    ∃ u v, extract S g pk a xs ys = some (u,v) ∧ u ≠ v ∧ trunc S (g.2 u) = trunc S (g.2 v) := by
  unfold extract
  cases h : scan S g.2 _ _ (thashBlocks S a xs) (thashBlocks S a ys) with
  | some pair =>
    obtain ⟨u,v⟩ := pair
    exact ⟨u,v,rfl,scan_sound S g.2 _ _ _ _ _ _ h⟩
  | none =>
    rw [thash_wide S g hw _ _ _ hn, thash_wide S g hw _ _ _ (arity ▸ hn)] at win
    have len : (thashBlocks S a xs).length = (thashBlocks S a ys).length := by
      simp only [thashBlocks_length, arity]
    have ne : thashBlocks S a xs ≠ [] := by
      intro he
      have z := thashBlocks_length S a xs
      rw [he] at z
      simp at z
    exact (diff (thashBlocks_injective S (scan_none S g.2 _ _ _ _ len ne h win).2).2).elim

private theorem read_cost (u : Cell) :
    EvalCost (fun H => (pure ((tablesOf H).2 u) : ProbComp Chain512)) 1 :=
  EvalCost.eval (X := Input) (Y := Output) (.inr u) (fun y => (arrayVectorEquivFin UInt64 8).symm y.2)

private theorem scan_cost (c d : Chain512) (bs es : List Block512) :
    EvalCost (fun H => (pure (scan S (tablesOf H).2 c d bs es) : ProbComp (Option (Cell × Cell))))
      (2 * bs.length) := by
  induction bs generalizing c d es with
  | nil => exact EvalCost.const (pure none)
  | cons b bs ih =>
    cases es with
    | nil => exact (EvalCost.const (pure none)).mono (Nat.zero_le _)
    | cons e es =>
      let step := fun (c' d' : Chain512) (H : Input → Output) =>
        (pure (if (c,b) ≠ (d,e) ∧ trunc S c' = trunc S d' then some ((c,b),(d,e))
          else scan S (tablesOf H).2 c' d' bs es) : ProbComp (Option (Cell × Cell)))
      have inner (c' d' : Chain512) : EvalCost (step c' d') (2 * bs.length) := by
        unfold step
        split
        · exact (EvalCost.const _).mono (Nat.zero_le _)
        · exact ih c' d' es
      have cost := EvalCost.bind (read_cost (c,b)) (fun c' =>
        EvalCost.bind (read_cost (d,e)) (inner c'))
      rw [show 2 * (b :: bs).length = 1 + (1 + 2 * bs.length) by simp; omega]
      simpa only [step, pure_bind, scan] using cost

/-- The extractor uses the forger's same quantum port. It reads the seed cell once
and reads at most two cells per remaining block, including padding. -/
theorem extract_cost (pk : S.Node) (a : Bytes 22) (xs ys : List S.Node) :
    EvalCost (fun H => (pure (extract S (tablesOf H) pk a xs ys) : ProbComp (Option (Cell × Cell))))
      (1 + 2 * ((38 + S.vp.params.n * xs.length) / 128 + 1)) := by
  have cost := EvalCost.bind (read_cost (initial, seedBlock S pk)) (fun c =>
    scan_cost S c c (thashBlocks S a xs) (thashBlocks S a ys))
  simpa only [extract, pure_bind, thashBlocks_length] using cost

structure Attempt (arity : ℕ) where
  seed : S.Node
  address : Bytes 22
  left : {xs : List S.Node // xs.length = arity}
  right : {xs : List S.Node // xs.length = arity}

variable {arity : ℕ} {E : Type} [Fintype E] [DecidableEq E]
variable (A : (Input → Output) → Closed (WS Input Output E) (Attempt S arity))

def Attempt.wins (g : CompressionTables) (a : Attempt S arity) : Prop :=
  a.left.val ≠ a.right.val ∧
    (tablePrimitives g S.vp.params).Thash a.seed a.address a.left.val =
      (tablePrimitives g S.vp.params).Thash a.seed a.address a.right.val

def collision (g : CompressionTables) : Option (Cell × Cell) → Prop
  | some (u,v) => u ≠ v ∧ trunc S (g.2 u) = trunc S (g.2 v)
  | none => False

def machine (H : Input → Output) : Closed (WS Input Output E) (Option (Cell × Cell)) :=
  (fun a => extract S (tablesOf H) a.seed a.address a.left.val a.right.val) <$> A H

theorem machine_cost (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    PUE (spec := unifSpec) cnt0 (machine S A)
      (q + (1 + 2 * ((38 + S.vp.params.n * arity) / 128 + 1))) := by
  unfold machine
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply PUE.bind hq
  intro a
  let B := fun (x : Option (Cell × Cell)) (_ : Input → Output) =>
    (pure x : Closed (WS Input Output E) (Option (Cell × Cell)))
  have h := PUE.liftU_bind (extract_cost S a.seed a.address a.left.val a.right.val)
    (B := B) (q := 0) (fun x => PUE.pure x 0)
  simpa only [B, liftU_pure, pure_bind, Nat.zero_add, a.left.property] using h

/-- For an arbitrary quantum machine producing two fixed-arity candidates, its
hash-collision success is bounded by the extracted compression-collision success.
This inequality holds pointwise, even on a nonrandom compression table. -/
theorem collision_reduction (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (hn : arity ≠ 1)
    (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) :
    @qWeight _ _ _ (Attempt.wins S g) (Classical.decPred _) (A (oracle g)) ρ ≤
      @qWeight _ _ _ (collision S g) (Classical.decPred _) (machine S A (oracle g)) ρ := by
  classical
  unfold machine
  rw [qWeight_map, tablesOf_oracle]
  apply qWeight_mono
  intro a ha
  obtain ⟨u,v,hit,ok⟩ := extract_collision S g hw a.seed a.address a.left.val a.right.val
    (a.left.property.trans a.right.property.symm) (by simpa only [a.left.property] using hn) ha.1 ha.2
  rw [hit]
  exact ok

section Game
attribute [local irreducible] arityTargets
open TweakableHash
variable (seeds : ProbComp S.Node)
local notation "P" g => thashArityProblemT S.vp (randPrims (functions S g)) seeds arity

/-- The two candidates and their common seed and tweak in the actual class game.
An out-of-bounds target index becomes two identical candidates. -/
noncomputable def candidates (g : CompressionTables) (B : QSM_DT_TCR_Adversary (WS Input Output E) (P g)) :
    Closed (WS Input Output E) (Attempt S arity) := do
  let pk ← liftU seeds
  let r ← liftU ((simulateQ (SM_DT_TCR_oracles (P g) pk) B.choose).run ([], []))
  let jm ← B.forge r.1 pk
  match r.2.1[jm.1]? with
  | none => pure ⟨pk, default, jm.2, jm.2⟩
  | some tm => pure ⟨pk, tm.1, jm.2, tm.2⟩

theorem candidates_success (g : CompressionTables) (B : QSM_DT_TCR_Adversary (WS Input Output E) (P g)) :
    qSM_DT_TCR_Advantage B =
      @qWeight _ _ _ (Attempt.wins S g) (Classical.decPred _) (candidates S seeds g B) B.ρ₀ := by
  classical
  let win := fun a : Attempt S arity => decide (a.wins S g)
  have eq : qSM_DT_TCR_Experiment B = win <$> candidates S seeds g B := by
    unfold qSM_DT_TCR_Experiment candidates
    simp only [map_bind]
    congr 1
    funext pk
    congr 1
    funext r
    congr 1
    funext jm
    split
    · rename_i ht
      simp [ht, win, Attempt.wins]
    · rename_i tm ht
      rw [ht, map_pure]
      apply congrArg pure
      unfold win
      apply decide_eq_decide.mpr
      simp only [Attempt.wins, ne_eq, Subtype.ext_iff]
      rfl
  unfold qSM_DT_TCR_Advantage
  rw [eq, qWeight_map]
  simp [win]

set_option maxHeartbeats 1400000 in
/-- Reduction of the uniform shared-compression class game to SHA-512 prefix
collision finding. The query premise accounts for candidate generation, including
the game oracles in phase one; the displayed additive term covers extraction. -/
theorem class_reduction (hw : S.vp.params.n ≠ 16) (hn : arity ≠ 1)
    (B : (g : CompressionTables) → QSM_DT_TCR_Adversary (WS Input Output E) (P g))
    (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) (same : ∀ g, (B g).ρ₀ = ρ)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q)
    (realize : ∀ g, A (oracle g) = candidates (arity := arity) (E := E) S seeds g (B g)) :
    ∃ M : (Input → Output) → Closed (WS Input Output E) (Option (Cell × Cell)),
      PUE (X := Input) (Y := Output) (E := E) (spec := unifSpec) cnt0 M (q + (1 + 2 * ((38 + S.vp.params.n * arity) / 128 + 1))) ∧
      (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (B g)) ≤
        ∑ g : CompressionTables, unifW _ g *
          @qWeight _ _ _ (collision S g) (Classical.decPred _) (M (oracle g)) ρ := by
  refine ⟨machine S A, machine_cost S A q hq, ?_⟩
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  rw [candidates_success (arity := arity) (E := E) S seeds g (B g), same, ← realize]
  exact collision_reduction S A g hw hn ρ

end Game

end Reduction.Compression.ClassCollision
#print axioms Reduction.Compression.ClassCollision.extract_collision

#print axioms Reduction.Compression.ClassCollision.extract_cost
#print axioms Reduction.Compression.ClassCollision.collision_reduction
#print axioms Reduction.Compression.ClassCollision.machine_cost
#print axioms Reduction.Compression.ClassCollision.candidates_success
#print axioms Reduction.Compression.ClassCollision.class_reduction
