import Integration.SlhDsaShakePermutationItsrBanks
import Integration.SlhDsaShakePermutationSkFormat

/-! On a good capacity graph, every recorded terminal head belongs to one
overwrite path. Thus an arbitrary fixed partial assignment of one target
digest per path costs just one digest guess per fresh head. -/
namespace Reduction.ShakePermutation.ItsrLabel.Target
open Classical Tails MLink SLHDSA
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

abbrev Goal (S : Sha2Set) := List Rate → Option S.Node
def digest (S : Sha2Set) (pre y : Rate) : S.Node :=
  ShakeXof.head (output_sizes S).1 (Completion.bytes (rateXor pre y))

def Good (S : Sha2Set) (π : Permutation) (L : ℕ) (goal : Goal S) (k k' : Db) (h : Heads) : Prop :=
  Graph.Good (layout π) k k' ∧ ∀ (p : Relabel.Path L) pre z y,
    Relabel.visit π k k' p = some (pre,z) → h z = some y →
    goal (List.ofFn p.2) ≠ some (digest S pre y)

noncomputable def label (S : Sha2Set) (π : Permutation) (L : ℕ) (goal : Goal S) (D : Bank) : Bool :=
  decide (Good S π L goal (masks D false) (masks D true) (held D))

theorem good_of_extension {S π L goal k k' K K' h H} (hk : Graph.Extends k K)
    (hk' : Graph.Extends k' K') (hh : Graph.Extends h H) (g : Good S π L goal K K' H) :
    Good S π L goal k k' h :=
  ⟨Graph.good_of_extension _ hk hk' g.1,fun p r z y hr hy =>
    g.2 p r z y (Relabel.run_extends π k k' K K' hk hk' _ hr) (hh z y hy)⟩

private theorem ext_insert {α β : Type} [DecidableEq α] {f : α → Option β} {x}
    (hx : f x = none) (y) : Graph.Extends f (Function.update f x (some y)) := by
  intro r v hv
  have hn : r ≠ x := by rintro rfl; rw [hx] at hv; contradiction
  exact (Function.update_of_ne hn ..).trans hv

set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support

private theorem preserve {S : Sha2Set} {π : Permutation} {L : ℕ} {goal : Goal S} {k k' K K' : Db} {h : Heads}
    (g : Good S π L goal k k' h) (gc : Graph.Good (layout π) K K')
    (hk : Graph.Extends k K) (hk' : Graph.Extends k' K') (back : ∀ {p z}, z ∈ Graph.support h →
      Graph.Tail (layout π) K K' p z → Graph.Tail (layout π) k k' p z) :
    Good S π L goal K K' h := by
  refine ⟨gc,fun p r z y hr hy => ?_⟩
  have hz : z ∈ Graph.support h := (Graph.mem_support h z).mpr (Option.isSome_iff_exists.mpr ⟨y,hy⟩)
  have tail : Graph.Tail (layout π) K K' (List.ofFn p.2) z := (Relabel.run_tail π K K').mp ⟨r,hr⟩
  obtain ⟨u,hu⟩ := (Relabel.run_tail π k k').mpr (back hz tail)
  have eq := congrArg Prod.fst (Option.some.inj ((Relabel.run_extends π k k' K K' hk hk' _ hu).symm.trans hr))
  change u = r at eq
  exact g.2 p r z y (eq ▸ hu) hy

theorem good_left {S π L goal k k' h x y} (g : Good S π L goal k k' h) (empty : k x = none)
    (cert : LeftCert π k k' x y) : Good S π L goal (Function.update k x (some y)) k' h :=
  preserve g cert.1 (ext_insert empty y) (fun _ _ => id) (fun _ u => cert.2 u)

theorem good_right {S : Sha2Set} {π L} {goal : Goal S} {k k' : Db} {h : Heads} {x y}
    (g : Good S π L goal k k' h) (empty : k' x = none)
    (cert : RightCert π k k' (Graph.support h) x y) : Good S π L goal k (Function.update k' x (some y)) h := by
  obtain ⟨gc,mark,m,tail⟩ := cert
  exact preserve g gc (fun _ _ => id) (ext_insert empty y) (fun held u =>
    (tail u).resolve_right (fun eq => (m _ eq).2 held))

noncomputable def aim (S : Sha2Set) (π : Permutation) (L : ℕ) (goal : Goal S) (k k' : Db) (z : Capacity) : Rate × S.Node :=
  match Relabel.chosen π k k' L z with
  | none => (0,default)
  | some (path,r) => (r,(goal (List.ofFn path.2)).getD default)

theorem good_head {S π L goal k k' h x y} (g : Good S π L goal k k' h)
    (miss : digest S (aim S π L goal k k' x).1 y ≠ (aim S π L goal k k' x).2) :
    Good S π L goal k k' (Function.update h x (some y)) := by
  refine ⟨g.1,fun p r z v hr hv hit => ?_⟩
  by_cases eq : z = x
  · subst z
    rw [Function.update_self] at hv
    cases Option.some.inj hv
    apply miss
    simp only [aim,Relabel.chosen_of_visit π k k' g.1 hr,hit,Option.getD_some]
  · exact g.2 p r z v hr ((Function.update_of_ne eq ..).symm.trans hv) hit

end Reduction.ShakePermutation.ItsrLabel.Target
