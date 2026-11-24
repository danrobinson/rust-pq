import Integration.SlhDsaCompressionHmac256Outer
import Ideal.Games.Itsr

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive
abbrev InputCell := St × Blk
private abbrev Record := InputCell × St

private def path (g : CF St Blk) (c : St) : List Blk → List Record
  | [] => []
  | b :: bs => let v := g (c,b); ((c,b),v) :: path g v bs

private theorem path_eq (g : CF St Blk) (c : St) (bs : List Blk) :
    path g c bs = (Itsr.mdCells g c bs).map (fun x => (x,g x)) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [path, Itsr.mdCells, ih]

/-- Either an input mapping back to the random starting state or two distinct
compression inputs with identical output. -/
abbrev Evidence := InputCell ⊕ (InputCell × InputCell)

def validEvidence (g : CompressionTables) (i : St) : Evidence → Prop
  | .inl x => g.1 x = i
  | .inr (x,y) => x ≠ y ∧ g.1 x = g.1 y

private def inspect (i : St) (rs : List Record) : Option Evidence :=
  match rs.find? (fun r => decide (r.2 = i)) with
  | some r => some (.inl r.1)
  | none => ((rs.product rs).find? (fun p => decide (p.1.1 ≠ p.2.1 ∧ p.1.2 = p.2.2))).map
      (fun p => .inr (p.1.1,p.2.1))


def extractInner (g : CompressionTables) (i : St) (x y : (Bytes 16) × List Byte) :=
  inspect i (path g.1 i (Ideal.iblocks x.1 x.2) ++ path g.1 i (Ideal.iblocks y.1 y.2))

theorem extract_inner_hit (g : CompressionTables) (i : St) (x y : (Bytes 16) × List Byte)
    (ne : x ≠ y) (same : innerDigest g i x = innerDigest g i y) :
    ∃ w, extractInner g i x y = some w ∧ validEvidence g i w := by
  let bs := Ideal.iblocks x.1 x.2
  let cs := Ideal.iblocks y.1 y.2
  let cells := Itsr.mdCells g.1 i bs ++ Itsr.mdCells g.1 i cs
  let rs := cells.map fun u => (u,g.1 u)
  have mem (r : Record) (hr : r ∈ rs) : g.1 r.1 = r.2 := by
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hr
    rw [← hu]
  have entry (u : InputCell) (hu : u ∈ cells) : (u,g.1 u) ∈ rs := List.mem_map.mpr ⟨u,hu,rfl⟩
  change ∃ w, inspect i _ = some w ∧ _
  rw [path_eq, path_eq, ← List.map_append]
  change ∃ w, inspect i rs = some w ∧ _
  unfold inspect
  cases h : rs.find? (fun r => decide (r.2 = i)) with
  | some r =>
    have eq := List.find?_some h
    exact ⟨_,rfl,(mem r (List.mem_of_find?_eq_some h)).trans (of_decide_eq_true eq)⟩
  | none =>
    cases e : (rs.product rs).find? (fun p => decide (p.1.1 ≠ p.2.1 ∧ p.1.2 = p.2.2)) with
    | some p =>
      have hp := List.mem_product.mp (List.mem_of_find?_eq_some e)
      have good : decide (p.1.1 ≠ p.2.1 ∧ p.1.2 = p.2.2) = true := List.find?_some (p := fun z : Record × Record => decide (z.1.1 ≠ z.2.1 ∧ z.1.2 = z.2.2)) e
      have hit := of_decide_eq_true good
      exact ⟨_,rfl, hit.1,(mem _ hp.1).trans (hit.2.trans (mem _ hp.2).symm)⟩
    | none =>
      exfalso
      apply ne
      have inj (u) (hu : u ∈ cells) (v) (hv : v ∈ cells) (eq : g.1 u = g.1 v) : u = v := by
        by_contra hne
        have hh := List.find?_eq_none.mp e ((u,g.1 u),(v,g.1 v))
          (List.mem_product.mpr ⟨entry u hu,entry v hv⟩)
        simp [hne,eq] at hh
      have fresh (u) (hu : u ∈ cells) : g.1 u ≠ i := by
        intro hv
        have hh := List.find?_eq_none.mp h (u,g.1 u) (entry u hu)
        simp [hv] at hh
      have eq := Itsr.md_inj g.1 i cells inj fresh bs cs
        (fun _ hu => List.mem_append_left _ hu) (fun _ hu => List.mem_append_right _ hu) same
      exact Prod.ext (Ideal.iblocks_injective eq).1 (Ideal.iblocks_injective eq).2

private theorem path_cost (i : St) (bs : List Blk) :
    EvalCost (fun H => (pure (path (tablesOf H).1 i bs) : ProbComp _)) bs.length := by
  induction bs generalizing i with
  | nil => exact EvalCost.const (X := Input) (Y := Output) (pure [])
  | cons b bs ih =>
    have one := EvalCost.eval (X := Input) (Y := Output) (.inl (i,b))
      Prod.fst
    have cost := EvalCost.bind one (fun v => (ih v).map (fun rs => ((i,b),v) :: rs))
    simp only [pure_bind,map_pure,Nat.add_comm 1] at cost
    kexact cost

theorem extract_inner_cost (i : St) (x y : (Bytes 16) × List Byte) :
    EvalCost (fun H => (pure (extractInner (tablesOf H) i x y) : ProbComp _))
      ((x.2.length + 24)/64 + 1 +
        ((y.2.length + 24)/64 + 1)) := by
  have cost := EvalCost.bind (path_cost i (Ideal.iblocks x.1 x.2)) (fun xs =>
    (path_cost i (Ideal.iblocks y.1 y.2)).map (fun ys => inspect i (xs ++ ys)))
  simpa only [extractInner, Ideal.iblocks_length, pure_bind, map_pure] using cost

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.extract_inner_hit
#print axioms Reduction.Compression.Hmac256.extract_inner_cost
