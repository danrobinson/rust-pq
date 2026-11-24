import Slhdsa.Proofs.Basic
import Spec.Shake256
import Mathlib.Tactic.IntervalCases

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

theorem words_get {n : Usize} (a : Array U64 n) (j : Nat) (h : j < n.val) :
    (words a)[j]! = (a.val[j]'(by simpa)).bv := by
  rw [words_at a h, getElem!_eq a.val j (by simpa)]

private theorem read_lane {n : Usize} (a : Array U64 n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok (a.val[i.val]!) := by
  have hi : i.val < a.val.length := by simpa using h
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem chi_spec (b : Array U64 25#usize) :
    shake256.chi b ⦃ result => prefixOk result 25 (Spec.Keccak.chi (words b)) ⦄ := by
  simp (disch := decide) only [shake256.chi, read_lane, lift, bind_ok, step_simps]
  intro j hj
  interval_cases j <;> simp (disch := decide) only [Array.make_val, Spec.Keccak.chi, words_at] <;> rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem rhoPi_spec (a : Array U64 25#usize) (d : Array U64 5#usize)
    (hd : prefixOk d 5 (Spec.Keccak.delta (words a))) :
    shake256.rho_pi a d ⦃ out => prefixOk out 25 (Spec.Keccak.rhoPi (words a)) ⦄ := by
  simp (disch := decide) only [shake256.rho_pi, read_lane, lift, bind_ok, step_simps]
  intro j hj
  interval_cases j <;>
    simp (disch := decide) only [Array.make_val, Spec.Keccak.rhoPi, Spec.Keccak.theta, words_at] <;>
    change (_ ^^^ (_ : U64).bv).rotateLeft _ = _ <;>
    rw [hd _ (by decide)] <;> rfl

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
  let* ⟨b, bp⟩ ← rhoPi_spec a d dp
  let* ⟨o, op⟩ ← chi_spec b
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
