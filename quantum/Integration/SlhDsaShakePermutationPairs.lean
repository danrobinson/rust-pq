import Integration.SlhDsaShakePermutationTails

/-! Simultaneously adding a capacity mask to several pending pairs can create collisions
between two new intermediate rates. The same mask is used for both pairs. -/
namespace Reduction.ShakePermutation.Pairs
open Classical

private theorem pack {A C : Type} [DecidableEq A] [DecidableEq C] (g : Bool → C → A)
    (hg : ∀ b, Function.Injective (g b)) (s : Finset C) (n : ℕ) (hc : 4*n ≤ s.card) :
    ∃ f : Fin n → C, (∀ i, f i ∈ s) ∧
      ∀ i j, i ≠ j → ∀ b d, g b (f i) ≠ g d (f j) := by
  classical
  induction n generalizing s with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
    let fiber := fun b d => s.filter fun z => g b z = g d x
    have small (b d) : (fiber b d).card ≤ 1 :=
      Finset.card_le_one.mpr (fun u hu v hv => hg b ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm))
    let bad := Finset.univ.biUnion fun b : Bool => Finset.univ.biUnion (fiber b)
    have hb : bad.card ≤ 4 := by
      calc _ ≤ ∑ b : Bool, ∑ d : Bool, (fiber b d).card :=
              Finset.card_biUnion_le.trans (Finset.sum_le_sum fun b _ => Finset.card_biUnion_le)
           _ ≤ ∑ _b : Bool, ∑ _d : Bool, 1 :=
              Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ => small b d
           _ = 4 := by decide
    have hrem := Finset.card_le_card_sdiff_add_card (s := s) (t := bad)
    obtain ⟨f,hf,hi⟩ := ih (s \ bad) (by omega)
    have sep (i : Fin n) (b d) : g b (f i) ≠ g d x := by
      intro he
      exact (Finset.mem_sdiff.mp (hf i)).2 (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hf i)).1,he⟩⟩⟩)
    refine ⟨Fin.cons x f,fun i => Fin.cases hx (fun j => (Finset.mem_sdiff.mp (hf j)).1) i,?_⟩
    intro i j hij b d
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (hij rfl).elim
    · exact (sep _ d b).symm
    · exact sep _ b d
    · exact hi _ _ (fun h => hij (congrArg Fin.succ h)) b d

private theorem pack_prop {C A : Type} [DecidableEq C] [DecidableEq A] (g : Bool → C → A)
    (hg : ∀ b, Function.Injective (g b)) (s : Finset C) (n : ℕ) (hs : 4*n ≤ s.card)
    (P : C → Prop) (hP : ∀ c ∈ s, P c) :
    ∃ f : Fin n → C, (∀ i, P (f i)) ∧ ∀ i j, i ≠ j → ∀ b d, g b (f i) ≠ g d (f j) := by
  obtain ⟨f,hf,hi⟩ := pack g hg s n hs
  exact ⟨f,fun i => hP _ (hf i),hi⟩

private abbrev I := Fin 8 × Bool
private abbrev Labels := Rate × Rate × Capacity × (Fin 8 → Capacity) × (Fin 8 → Rate) × (I → Capacity)
private def left (w : Labels) (i : I) : Words :=
  if i.2 then join w.2.1 (Tails.xorCap (w.2.2.2.1 i.1) w.2.2.1) else join w.1 (w.2.2.2.1 i.1)
private def right (w : Labels) (i : I) : Words := join (w.2.2.2.2.1 i.1) (w.2.2.2.2.2 i)
private abbrev Witness := {w : Labels // Function.Injective (left w) ∧ Function.Injective (right w)}

def collision (π : Permutation) (r s : Rate) (delta : Capacity) (z : Capacity) : Prop :=
  rateOf (π (join r z)) = rateOf (π (join s (Tails.xorCap z delta)))
noncomputable def salts (π : Permutation) (r s : Rate) (d : Capacity) : Finset Capacity := by
  classical exact Finset.univ.filter (collision π r s d)

theorem mem_salts (π : Permutation) (r s : Rate) (d c : Capacity) : c ∈ salts π r s d ↔ collision π r s d c := by
  classical simp [salts]

def exceptional (π : Permutation) : Prop :=
  ∃ (r s : Rate) (d : Capacity), (r ≠ s ∨ d ≠ (fun _ => 0)) ∧ 32 ≤ (salts π r s d).card

private theorem values_injective (r s : Rate) (d : Capacity) (c : Capacity) (hn : r ≠ s ∨ d ≠ (fun _ => 0)) :
    join r c ≠ join s (Tails.xorCap c d) := by
  intro h
  have hr : r = s := by simpa only [rate_join] using congrArg rateOf h
  have hc : c = Tails.xorCap c d := by simpa only [cap_join] using congrArg capOf h
  apply hn.resolve_left (not_not.mpr hr)
  funext i
  have hi := congrFun hc i
  have hx := congrArg (fun v => c i ^^^ v) hi
  simpa [Tails.xorCap,← UInt64.xor_assoc] using hx.symm

set_option maxRecDepth 4000 in
private theorem graph_count :
    Nat.card (I ↪ Words) * Nat.card {π : Permutation // exceptional π} ≤ Nat.card Witness * Nat.card Permutation := by
  classical
  apply graph_union_bound (fun w : Witness => ⟨left w,w.property.1⟩) (fun w => ⟨right w,w.property.2⟩)
  rintro π ⟨r,s,d,hd,hsize⟩
  let g (b : Bool) (c : Capacity) := if b then join s (Tails.xorCap c d) else join r c
  have hg (b) : Function.Injective (g b) := by
    cases b
    · intro a b e; simpa only [g,Bool.false_eq_true,ite_false,cap_join] using congrArg capOf e
    · intro a b e
      have h : Tails.xorCap a d = Tails.xorCap b d := by simpa only [g,ite_true,cap_join] using congrArg capOf e
      funext i
      have h' := congrArg (fun v => v ^^^ d i) (congrFun h i)
      simpa only [Tails.xorCap,UInt64.xor_assoc,UInt64.xor_self,UInt64.xor_zero] using h'
  obtain ⟨cs,hm,distinct⟩ := pack_prop g hg (salts π r s d) 8 hsize (collision π r s d)
    (fun c => (mem_salts π r s d c).mp)
  let w : Labels := (r,s,d,cs,fun i => rateOf (π (join r (cs i))),fun p => capOf (π (g p.2 (cs p.1))))
  have hl : Function.Injective (left w) := by
    rintro ⟨i,b⟩ ⟨j,e⟩ h
    change g b (cs i) = g e (cs j) at h
    by_cases hi : i = j
    · subst j
      cases b <;> cases e <;> first | rfl | exact (values_injective r s d (cs i) hd h).elim | exact (values_injective r s d (cs i) hd h.symm).elim
    · exact (distinct i j hi b e h).elim
  have graph (p : I) : π (left w p) = right w p := by
    obtain ⟨i,b⟩ := p
    have h := hm i
    change rateOf (π (join r (cs i))) = rateOf (π (join s (Tails.xorCap (cs i) d))) at h
    cases b
    · exact (join_split _).symm
    · change _ = join (rateOf (π (join r (cs i)))) _
      rw [h]
      exact (join_split _).symm
  have hr : Function.Injective (right w) := by intro a b h; exact hl (π.injective ((graph a).trans (h.trans (graph b).symm)))
  exact ⟨⟨w,hl,hr⟩,DFunLike.ext _ _ graph⟩

theorem exceptional_probability :
    2^1000 * Nat.card {π : Permutation // exceptional π} ≤ Nat.card Permutation := by
  classical
  have label : Nat.card Witness ≤ Nat.card Labels := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective (Subtype.val : Witness → Labels) Subtype.val_injective
  have lanes : Fintype.card UInt64 = 2^64 := by rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
  have num : Nat.card Labels * 2^1000 ≤ Nat.card (I ↪ Words) := by
    simp only [Nat.card_eq_fintype_card,Labels,I,Fintype.card_prod,Fintype.card_embedding_eq,Fintype.card_fun,
      Fintype.card_fin,Fintype.card_bool,Rate,Capacity,Words,lanes]
    decide +kernel
  have h := Nat.mul_le_mul_right (Nat.card {π : Permutation // exceptional π}) num
  have hp : 0 < Nat.card Labels := Nat.card_pos
  rw [Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left (h.trans (graph_count.trans (Nat.mul_le_mul_right _ label))) hp

end Reduction.ShakePermutation.Pairs
#print axioms Reduction.ShakePermutation.Pairs.exceptional_probability
