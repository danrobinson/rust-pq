import Slhdsa.Proofs.Basic
import Spec.Shake256

open Aeneas Aeneas.Std Result
namespace slhdsa.Keccak

def words {n : Usize} (a : Array U64 n) : Spec.Keccak.State :=
  (a.val.map (·.bv)).toArray

private theorem words_at {n : Usize} (a : Array U64 n) {j : Nat} (h : j < n.val) :
    (words a)[j]! = (a.val[j]!).bv := by
  simp [words, getElem!_pos, h]

/-- Before iteration i, each earlier lane agrees with the corresponding
specification value. -/
private def prefixOk {n : Usize} (a : Array U64 n) (i : Nat) (f : Nat → BitVec 64) : Prop :=
  ∀ j, j < i → (a.val[j]!).bv = f j

private theorem advance {n : Usize} (a b : Array U64 n) (x : U64) (i : Nat)
    (f : Nat → BitVec 64) (hi : i < n.val)
    (post : b.val = a.val.set i x) (prev : prefixOk a i f) (hx : x.bv = f i) :
    prefixOk b (i+1) f := by
  intro j hj
  have hja : j < a.val.length := by simpa using (show j < n.val by omega)
  rw [post, getElem!_pos _ _ (by simp; omega), List.getElem_set]
  split
  · subst j; exact hx
  · rw [← getElem!_eq _ _ hja]; exact prev j (by omega)

theorem parity_spec (a : Array U64 25#usize) (c : Array U64 5#usize) (i : Usize)
    (hi : i.val ≤ 5) (inv : prefixOk c i.val (Spec.Keccak.parity (words a))) :
    shake256.round_loop0 a c i ⦃ out => prefixOk out 5 (Spec.Keccak.parity (words a)) ⦄ := by
  unfold shake256.round_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 5#usize × Usize) => 5 - p.2.val)
    (inv := fun p => p.2.val ≤ 5 ∧ prefixOk p.1 p.2.val (Spec.Keccak.parity (words a)))
  · rintro ⟨c,x⟩ ⟨hi, inv⟩
    simp only at hi inv
    simp only [shake256.round_loop0.body, step_simps]
    spec_split
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [x1_post]
      apply advance c a1 i12 x.val _ (by scalar_tac) (by rw [a1_post, Array.set_val_eq]) inv
      have atLane (j : Nat) (hj : j < 25) : (words a)[j]! = (a.val[j]'(by simpa)).bv := by
        rw [words_at _ (by simpa), getElem!_eq]
      simp only [Spec.Keccak.parity, *, atLane _ (by scalar_tac : x.val < 25),
        atLane _ (by scalar_tac : x.val+5 < 25), atLane _ (by scalar_tac : x.val+10 < 25),
        atLane _ (by scalar_tac : x.val+15 < 25), atLane _ (by scalar_tac : x.val+20 < 25)]
    · simp only [step_simps]
      have eq : x.val = 5 := by scalar_tac
      simpa [eq] using inv
  · exact ⟨hi, inv⟩

theorem delta_spec (state : Spec.Keccak.State) (c d : Array U64 5#usize) (i : Usize)
    (hc : prefixOk c 5 (Spec.Keccak.parity state)) (hi : i.val ≤ 5)
    (inv : prefixOk d i.val (Spec.Keccak.delta state)) :
    shake256.round_loop1 c d i ⦃ out => prefixOk out 5 (Spec.Keccak.delta state) ⦄ := by
  unfold shake256.round_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 5#usize × Usize) => 5 - p.2.val)
    (inv := fun p => p.2.val ≤ 5 ∧ prefixOk p.1 p.2.val (Spec.Keccak.delta state))
  · rintro ⟨d,x⟩ ⟨hi, inv⟩
    simp only at hi inv
    simp only [shake256.round_loop1.body, step_simps]
    spec_split
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i3_post]
      apply advance d a i7 x.val _ (by scalar_tac) (by rw [a_post, Array.set_val_eq]) inv
      have h (j : Nat) (hj : j < 5) : (c.val[j]'(by simpa)).bv = Spec.Keccak.parity state j := by
        rw [← getElem!_eq]; exact hc j hj
      refine i7_post1.trans ?_
      rw [i2_post, i6_post, i5_post]
      change _ ^^^ BitVec.rotateLeft _ 1 = _
      simp only [Spec.Keccak.delta, i1_post, i4_post, i_post, i3_post]
      exact congrArg₂ (fun (u v : BitVec 64) => u ^^^ v.rotateLeft 1)
        (h ((x.val+4)%5) (by omega)) (h ((x.val+1)%5) (by omega))
    · simp only [step_simps]
      have eq : x.val = 5 := by scalar_tac
      simpa [eq] using inv
  · exact ⟨hi, inv⟩

private def dest (i : Nat) := i/5 + 5 * ((2*(i%5) + 3*(i/5))%5)
private def src (i : Nat) := (i%5 + 3*(i/5))%5 + 5*(i%5)

private theorem coordinates : ∀ i : Fin 25, dest i < 25 ∧ src i < 25 ∧
    src (dest i) = i ∧ dest (src i) = i := by decide

private theorem rotation_table : ∀ i : Fin 25,
    (shake256.round.ROT.val[i.val]!).val = Spec.Keccak.rotations[i.val]! := by
  unfold shake256.round.ROT Spec.Keccak.rotations
  decide

private def rhoPrefix (a b : Array U64 25#usize) (i : Nat) : Prop :=
  ∀ j, j < i → (b.val[dest j]!).bv = Spec.Keccak.rhoPi (words a) (dest j)

theorem rhoPi_spec (a b : Array U64 25#usize) (d : Array U64 5#usize) (i : Usize)
    (hd : prefixOk d 5 (Spec.Keccak.delta (words a))) (hi : i.val ≤ 25)
    (inv : rhoPrefix a b i.val) :
    shake256.round_loop2 a d b i ⦃ out => prefixOk out 25 (Spec.Keccak.rhoPi (words a)) ⦄ := by
  unfold shake256.round_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Usize) => 25 - p.2.val)
    (inv := fun p => p.2.val ≤ 25 ∧ rhoPrefix a p.1 p.2.val)
  · rintro ⟨b,k⟩ ⟨hi, inv⟩
    simp only at hi inv
    simp only [shake256.round_loop2.body, step_simps]
    spec_split
    · have hk : k.val < 25 := by scalar_tac
      have coord := coordinates ⟨k.val,hk⟩
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      have hkdest : i11.val = dest k.val := by simp [dest, *]
      have jlt : j < 25 := by omega
      have jd := (coordinates ⟨j,jlt⟩).1
      rw [a1_post, Array.set_val_eq, hkdest, getElem!_eq _ _ (by simpa using jd), List.getElem_set]
      split
      · rename_i eq
        have jk : j = k.val := by
          have v := congrArg src eq
          have cj := (coordinates ⟨j,jlt⟩).2.2.1
          change src (dest j) = j at cj
          have ck : src (dest k.val) = k.val := coord.2.2.1
          grind
        subst j
        unfold Spec.Keccak.rhoPi
        change i5.bv = (Spec.Keccak.theta (words a) (src (dest k.val))).rotateLeft
          Spec.Keccak.rotations[src (dest k.val)]!
        have ck : src (dest k.val) = k.val := coord.2.2.1
        rw [ck]
        have dh := hd (k.val%5) (by omega)
        have rh := rotation_table ⟨k.val,hk⟩
        change (shake256.round.ROT.val[k.val]!).val = _ at rh
        rw [getElem!_eq d.val _ (by simp; omega)] at dh
        rw [getElem!_eq shake256.round.ROT.val _ (by simpa)] at rh
        rw [i5_post]
        change BitVec.rotateLeft i3.bv i4.val = _
        refine (congrArg (fun w : BitVec 64 => w.rotateLeft i4.val) i3_post1).trans ?_
        rw [i1_post, i2_post, i4_post]
        simp only [x_post, Spec.Keccak.theta, words_at a hk, dh, rh]
        rw [getElem!_eq a.val k.val (by simpa)]
      · rw [← getElem!_eq _ _ (by simpa using jd)]
        apply inv
        by_contra hj'
        have : j = k.val := by omega
        subst j
        contradiction
    · simp only [step_simps]
      intro j hj
      have coord := coordinates ⟨j,hj⟩
      have h := inv (src j) (by have hj' : src j < 25 := coord.2.1; scalar_tac)
      have h' : dest (src j) = j := coord.2.2.2
      simpa only [h'] using h
  · exact ⟨hi, inv⟩

private theorem words_get {n : Usize} (a : Array U64 n) (j : Nat) (h : j < n.val) :
    (words a)[j]! = (a.val[j]'(by simpa)).bv := by
  rw [words_at a h, getElem!_eq a.val j (by simpa)]

theorem chi_spec (b out : Array U64 25#usize) (i : Usize)
    (hi : i.val ≤ 25) (inv : prefixOk out i.val (Spec.Keccak.chi (words b))) :
    shake256.round_loop3 b out i ⦃ result => prefixOk result 25 (Spec.Keccak.chi (words b)) ⦄ := by
  unfold shake256.round_loop3
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Usize) => 25 - p.2.val)
    (inv := fun p => p.2.val ≤ 25 ∧ prefixOk p.1 p.2.val (Spec.Keccak.chi (words b)))
  · rintro ⟨out,k⟩ ⟨hi, inv⟩
    simp only at hi inv
    simp only [shake256.round_loop3.body, step_simps]
    spec_split
    · have hk : k.val < 25 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i13_post]
      apply advance out a i12 k.val _ (by scalar_tac) (by rw [a_post, Array.set_val_eq]) inv
      have row_eq : k.val - k.val % 5 = k.val / 5 * 5 := by omega
      have idx1 : (k.val%5 + 1)%5 = (k.val+1)%5 := by omega
      have idx2 : (k.val%5 + 2)%5 = (k.val+2)%5 := by omega
      simp only [Spec.Keccak.chi, *, UScalar.bv_not,
        words_get b k.val hk,
        words_get b (k.val/5*5 + (k.val+1)%5) (by simpa using (show k.val/5*5 + (k.val+1)%5 < 25 by omega)),
        words_get b (k.val/5*5 + (k.val+2)%5) (by simpa using (show k.val/5*5 + (k.val+2)%5 < 25 by omega))]
    · simp only [step_simps]
      have eq : k.val = 25 := by scalar_tac
      simpa [eq] using inv
  · exact ⟨hi, inv⟩

private theorem array_eq {n : Usize} (a : Array U64 n) (f : Nat → BitVec 64)
    (p : prefixOk a n.val f) : words a = _root_.Array.ofFn (n := n.val) (fun i => f i.val) := by
  apply _root_.Array.ext
  · simp [words]
  · intro i hi hj
    have h : i < n.val := by simpa [words] using hi
    have hp := p i h
    simpa [words, getElem!_eq a.val i (by simpa)] using hp

set_option maxHeartbeats 2000000 in
/-- One Keccak-f round, including theta, rho, pi, chi and iota. -/
@[step] theorem round_spec (a : Array U64 25#usize) (rc : U64) :
    shake256.round a rc ⦃ out => words out = Spec.Keccak.round (words a) rc.bv ⦄ := by
  unfold shake256.round
  let* ⟨c, cp⟩ ← parity_spec a _ 0#usize (by decide) (by intro j hj; simp at hj)
  let* ⟨d, dp⟩ ← delta_spec (words a) c _ 0#usize cp (by decide) (by intro j hj; simp at hj)
  let* ⟨b, bp⟩ ← rhoPi_spec a _ d 0#usize dp (by decide) (by intro j hj; simp at hj)
  let* ⟨o, op⟩ ← chi_spec b _ 0#usize (by decide) (by intro j hj; simp at hj)
  step*
  change words out = _root_.Array.ofFn (n := 25) (fun j =>
    if j.val = 0 then Spec.Keccak.chi (_root_.Array.ofFn (n := 25) (fun i => Spec.Keccak.rhoPi (words a) i.val)) j.val ^^^ rc.bv
    else Spec.Keccak.chi (_root_.Array.ofFn (n := 25) (fun i => Spec.Keccak.rhoPi (words a) i.val)) j.val)
  have hb : words b = _root_.Array.ofFn (n := 25) (fun i => Spec.Keccak.rhoPi (words a) i.val) := array_eq b _ bp
  rw [← hb]
  apply array_eq out (fun j => if j = 0 then Spec.Keccak.chi (words b) j ^^^ rc.bv else Spec.Keccak.chi (words b) j)
  intro j hj
  change j < 25 at hj
  rw [out_post, Array.set_val_eq, getElem!_eq _ _ (by simpa using hj), List.getElem_set]
  split
  · subst j
    have hv := op 0 (by decide)
    simp only [getElem!_eq o.val 0 (by simp)] at hv
    simpa [*, UScalar.bv_xor] using congrArg (fun x : BitVec 64 => x ^^^ rc.bv) hv
  · rename_i hn
    have h0 : j ≠ 0 := by intro he; subst j; exact hn rfl
    simpa [h0, getElem!_eq o.val j (by simpa)] using op j hj
#print axioms round_spec

private theorem round_constants : ∀ j : Fin 24,
    (shake256.RC.val[j.val]!).bv = Spec.Keccak.rc.toList[j.val]! := by
  unfold shake256.RC Spec.Keccak.rc
  decide

private def remaining (i : Nat) (state : Spec.Keccak.State) : Spec.Keccak.State :=
  (Spec.Keccak.rc.toList.drop i).foldl Spec.Keccak.round state

/-- Keccak-f[1600] runs the 24 rounds in the FIPS 202 order. -/
@[step] theorem permute_spec (a : Array U64 25#usize) :
    shake256.permute a ⦃ out => words out = Spec.Keccak.permute (words a) ⦄ := by
  have size : Spec.Keccak.rc.toList.length = 24 := by decide
  unfold shake256.permute shake256.permute_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array U64 25#usize × Usize) => 24 - p.2.val)
    (inv := fun p => p.2.val ≤ 24 ∧ remaining p.2.val (words p.1) = Spec.Keccak.permute (words a))
  · rintro ⟨state,k⟩ ⟨hi, inv⟩
    simp only at hi inv
    simp only [shake256.permute_loop.body, step_simps]
    spec_split
    · have hk : k.val < 24 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hc := round_constants ⟨k.val,hk⟩
      change (shake256.RC.val[k.val]!).bv = Spec.Keccak.rc.toList[k.val]! at hc
      rw [getElem!_eq _ _ (by simpa), getElem!_eq _ _ (by omega)] at hc
      unfold remaining at inv ⊢
      rw [← List.getElem_cons_drop (show k.val < Spec.Keccak.rc.toList.length by omega),
        List.foldl_cons] at inv
      simpa only [i2_post, state1_post, i1_post, hc] using inv
    · simp only [step_simps]
      have eq : k.val = 24 := by scalar_tac
      simpa [remaining, eq, List.drop_eq_nil_of_le (le_of_eq size)] using inv
  · constructor
    · change 0 ≤ 24; decide
    · simp [remaining, Spec.Keccak.permute]
#print axioms permute_spec

end slhdsa.Keccak
