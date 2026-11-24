import MIdeal.ThashCollisionGame
import MIdeal.SkPrf

namespace MIdeal.Sha512
open Ideal Ideal.Itsr Ideal.HP MLink SLHDSA SLHDSA.Concrete OracleComp OracleSpec
variable (S : Sha2Set)

/-- A reader for all collection arities on a wide set, conditional on the
independent SHA-256 table. A singleton uses that table alone. -/
def readThash (g256 : CF St Blk) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) : SHAReader S.Node :=
  if xs.length = 1 then pure (sha2ThashG (liftC g256) S.vp.params pk a xs)
  else trunc S <$> readPath initial (path S pk a xs)

theorem readPath_eval (g : CF Chain512 Block512) (c : Chain512) (bs : List Block512) :
    simulateQ (ansImpl (spec := hS Chain512 Block512) g) (readPath c bs) = pure (mdFold g c bs) := by
  rw [← fst_map_run_stImpl (spec := hS Chain512 Block512) g (logU id) _ [], readPath_run]
  simp

theorem readThash_eval (g : CompressionTables) (hw : S.vp.params.n ≠ 16)
    (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :
    simulateQ (ansImpl (spec := hS Chain512 Block512) g.2) (readThash S g.1 pk a xs) =
      pure ((tablePrimitives g S.vp.params).Thash pk a xs) := by
  by_cases h : xs.length = 1
  · rw [readThash, ite_eq_left h, simulateQ_pure]
    change pure (sha2ThashG _ _ _ _ _) = pure (sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk a xs)
    simp only [sha2ThashG, sha2ThashMixed, ite_eq_left h]
  · rw [readThash, ite_eq_right h, thash_wide S g hw _ _ _ h, simulateQ_map, readPath_eval]
    rfl

def thashCost (arity : ℕ) := if arity = 1 then 0 else (38+S.vp.params.n*arity)/128+2

theorem readThash_bound (g256 : CF St Blk) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :
    IsQueryBoundP (readThash S g256 pk a xs) (fun i => i.isRight = true) (thashCost S xs.length) := by
  unfold readThash thashCost
  split
  · simp
  · exact ((isQueryBoundP_map_iff _ _ _).mpr (readPath_bound initial (path S pk a xs))).mono
      (by simp [path, thashBlocks_length])

end MIdeal.Sha512
