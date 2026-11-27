import Parallel.MaximalSession

namespace slhdsa.MaximalWorker
open ParallelCached ParallelCached.Tickets

/-- Reindex a validated physical plan after an unstable sort. The metadata
arrays and the reducer's destinations are independent of ticket numbers. -/
def PhasePlan.reorder {f x l} (plan : PhasePlan f x l) (sorted : Jobs)
    (order : sorted.Perm plan.jobs) : PhasePlan f x l where
  jobs := sorted
  reducer := plan.reducer
  unique := by
    have same := (order.flatMap_right id).map Prod.fst
    simp only [List.flatMap_id] at same
    exact same.nodup_iff.mpr plan.unique
  forestCover := by
    have same := ((order.flatMap_right id).map Prod.fst).append_right plan.reducer
    simp only [List.flatMap_id] at same
    exact (same.filterMap (region (x+l) f)).trans plan.forestCover
  chunkCover := by
    have same := ((order.flatMap_right id).map Prod.fst).filterMap (region 0 x)
    simp only [List.flatMap_id] at same
    exact same.trans plan.chunkCover
  leafCover := by
    have same := ((order.flatMap_right id).map Prod.fst).filterMap (region x l)
    simp only [List.flatMap_id] at same
    exact same.trans plan.leafCover

/-- The sort carries the complete work item. Its payload may contain input-
dependent tree indices; its destination list can include multiple SIMD lanes. -/
def PhasePlan.ofSorted {f x l J} (plan : PhasePlan f x l)
    (before after : List J) (fields : J → List (Nat × Unit))
    (source : before.map fields = plan.jobs) (order : after.Perm before) :
    PhasePlan f x l :=
  plan.reorder (after.map fields) (source ▸ order.map fields)

end slhdsa.MaximalWorker

namespace slhdsa.WorkerSetup
/-- Static dispatch fields which determine the ordered physical publications.
Cryptographic indices and subtree heights affect values, not ownership. -/
inductive Destination where
  | xmss (slot : Nat)
  | leaf (layer : Nat)
  | low (tree height : Nat)
  | direct (slot : Nat)
  | split (slot : Nat)
  | batchLow (first active height : Nat)
  | batchDirect (first active height : Nat)
  | batchSplit (active chunk base chunks : Nat)
deriving DecidableEq, Inhabited

def Destination.slots (x l f stride : Nat) (job : Destination) : List Nat :=
  let forest := x+l
  match job with
  | .xmss s => [s]
  | .leaf j => [x+j]
  | .low t h => (List.range (h+1)).map (fun j => forest+t*stride+j)
  | .direct s => [forest+s]
  | .split s => [forest+f+s]
  | .batchLow first active h =>
    (List.range (h+1)).flatMap fun j =>
      (List.range active).map fun lane => forest+(first+lane)*stride+j
  | .batchDirect first active h =>
    (List.range active).map fun lane => forest+(first+lane)*stride+1+h
  | .batchSplit active chunk base chunks =>
    (List.range active).map fun lane => forest+f+base+lane*chunks+chunk

end slhdsa.WorkerSetup
