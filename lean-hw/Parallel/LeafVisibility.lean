import Parallel.LeafTable
import Parallel.TicketProjection
import Parallel.SigningPublication
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLeafTable
open ParallelSigning Publication

/-- The full ticket queue can interleave leaf tickets with any other work.
Every leaf is visible before reduction and remains visible after READY. -/
theorem visible_leaves {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (tree : U64) (leaf : U32) (count : Nat) (size : count≤p.d.val)
    (bound : leaf.val<2^p.hp.val) {jobs issued : Nat} {done : List Nat}
    (trace : Trace jobs issued [] done) (exhausted : jobs < issued) (fields : Nat → List Nat)
    (cover : ((List.range jobs).flatMap fields).Perm (List.range count)) :
    leaves (nodeFor host p) p sk seed tree leaf count (done.flatMap fields) ⦃ slots =>
      ParallelRootWalk.PublishedLeaves (Shake.params p) (bytes sk.val) (bytes seed.val) tree.val leaf.val count slots ∧
      ∀ j<count, ∃ ticket, j ∈ fields ticket ∧
        Before done.reverse (fun i k => k ∈ fields i) (.slot ticket j) .reduce ∧
        ∀ w, Before done.reverse (fun i k => k ∈ fields i) (.slot ticket j) (.readRoots w) ⦄ := by
  have subtrace := projected_trace trace exhausted fields cover
  apply WP.spec_mono (leaves_spec _ p hp (node_law host p hp) sk seed tree leaf count (count+1)
    _ size bound subtrace (by omega))
  intro slots values
  refine ⟨values,?_⟩
  intro j hj
  obtain ⟨t,range,write⟩ := List.mem_flatMap.mp (cover.mem_iff.mpr (List.mem_range.mpr hj))
  have all := (trace.joined exhausted).exactly_once
  have complete : done.length=jobs := by
    have perm : done.Perm (List.range jobs) :=
      (List.perm_ext_iff_of_nodup all.1 List.nodup_range).mpr (fun k => (all.2 k).trans List.mem_range.symm)
    simpa using perm.length_eq
  have edge := ready_sees_cells trace complete (fun i k => k ∈ fields i) (List.mem_range.mp range) write
  exact ⟨t,write,(edge 0).1,fun w => (edge w).2⟩

end slhdsa.ParallelLeafTable
