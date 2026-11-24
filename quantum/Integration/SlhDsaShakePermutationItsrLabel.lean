import Integration.SlhDsaShakePermutationExtensions
import Integration.SlhDsaShakePermutationRelabelUpdate
import Integration.SlhDsaShakePermutationCompletion
import Integration.SlhDsaShakeSingleTarget

/-! Recorded terminal digest collisions for bounded overwrite paths. The
failure event includes an ambiguous graph, so it is monotone even when a
mask insertion makes several previously unreachable paths reachable. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support
abbrev Heads := Capacity → Option Rate

def key (S : Sha2Set) (pre y : Rate) : ShakeSingle.Decoded S :=
  DigestTransport.coveringDigest S.vp
    (ShakeXof.head (output_sizes S).2 (Completion.bytes (rateXor pre y)))

def Seen (S : Sha2Set) (π : Permutation) (L : ℕ) (k k' : Db) (h : Heads)
    (z : Capacity) (d : ShakeSingle.Decoded S) : Prop :=
  ∃ (path : Relabel.Path L) (pre y : Rate), Relabel.visit π k k' path = some (pre,z) ∧
    h z = some y ∧ key S pre y = d

def Good (S : Sha2Set) (π : Permutation) (L : ℕ) (k k' : Db) (h : Heads) : Prop :=
  Graph.Good (layout π) k k' ∧ ∀ z w d, Seen S π L k k' h z d → Seen S π L k k' h w d → z = w

theorem seen_mono {S π L k k' K K' h H z d} (hk : Graph.Extends k K)
    (hk' : Graph.Extends k' K') (hh : Graph.Extends h H) (s : Seen S π L k k' h z d) :
    Seen S π L K K' H z d := by
  obtain ⟨p,r,y,hr,hy,hd⟩ := s
  exact ⟨p,r,y,Relabel.run_extends π k k' K K' hk hk' _ hr,hh _ _ hy,hd⟩

theorem good_of_extension {S π L k k' K K' h H} (hk : Graph.Extends k K)
    (hk' : Graph.Extends k' K') (hh : Graph.Extends h H) (g : Good S π L K K' H) :
    Good S π L k k' h :=
  ⟨Graph.good_of_extension _ hk hk' g.1,fun z w d s t =>
    g.2 z w d (seen_mono hk hk' hh s) (seen_mono hk hk' hh t)⟩

theorem good_empty (S π L) : Good S π L (fun _ => none) (fun _ => none) (fun _ => none) :=
  ⟨Graph.good_empty _,fun _ _ _ ⟨_,_,_,_,h,_⟩ => by contradiction⟩

private theorem extends_insert {α β : Type} [DecidableEq α] {f : α → Option β} {x}
    (hx : f x = none) (y) : Graph.Extends f (Function.update f x (some y)) := by
  intro r v hv
  have hn : r ≠ x := by rintro rfl; rw [hx] at hv; contradiction
  exact (Function.update_of_ne hn ..).trans hv

private theorem seen_back {S : Sha2Set} {π : Permutation} {L : ℕ} {k k' K K' : Db} {h : Heads} {z : Capacity} {d : ShakeSingle.Decoded S} (hk : Graph.Extends k K)
    (hk' : Graph.Extends k' K') (tails : ∀ l, z ∈ Graph.support h →
      Graph.Tail (layout π) K K' l z → Graph.Tail (layout π) k k' l z)
    (s : Seen S π L K K' h z d) : Seen S π L k k' h z d := by
  obtain ⟨p,r,y,hr,hy,hd⟩ := s
  have held : z ∈ Graph.support h := (Graph.mem_support h z).mpr (Option.isSome_iff_exists.mpr ⟨y,hy⟩)
  have reached : Graph.Tail (layout π) K K' (List.ofFn p.2) z :=
    (Relabel.run_tail π K K').mp ⟨r,hr⟩
  obtain ⟨pre,hpre⟩ := (Relabel.run_tail π k k').mpr (tails _ held reached)
  have eq := Option.some.inj ((Relabel.run_extends π k k' K K' hk hk' _ hpre).symm.trans hr)
  exact ⟨p,pre,y,hpre,hy,(congrArg (fun a : Rate × Capacity => key S a.1 y) eq).trans hd⟩

theorem good_left {S π L k k' h x y} (g : Good S π L k k' h) (empty : k x = none)
    (cert : LeftCert π k k' x y) : Good S π L (Function.update k x (some y)) k' h := by
  have back := @seen_back S π L k k' (Function.update k x (some y)) k' h
  exact ⟨cert.1,fun z w d s t => g.2 z w d
    (back (extends_insert empty y) (fun _ _ => id) (fun _ _ u => cert.2 u) s)
    (back (extends_insert empty y) (fun _ _ => id) (fun _ _ u => cert.2 u) t)⟩

theorem good_right {S : Sha2Set} {π : Permutation} {L : ℕ} {k k' : Db} {h : Heads} {x : Rate} {y : Capacity} (g : Good S π L k k' h) (empty : k' x = none)
    (cert : RightCert π k k' (Graph.support h) x y) : Good S π L k (Function.update k' x (some y)) h := by
  obtain ⟨gc,mark,disj,tail⟩ := cert
  have back (z d) : Seen S π L k (Function.update k' x (some y)) h z d → Seen S π L k k' h z d :=
    @seen_back S π L k k' k (Function.update k' x (some y)) h z d (fun _ _ => id) (extends_insert empty y) (fun _ held u =>
      (tail u).resolve_right (fun eq => (disj z eq).2 held))
  exact ⟨gc,fun z w d s t => g.2 z w d (back z d s) (back w d t)⟩

end Reduction.ShakePermutation.ItsrLabel
