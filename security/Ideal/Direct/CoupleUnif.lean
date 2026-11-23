import Ideal.Direct.CoupleJ

/-!
# Uniform splitting of a label into the oracle answer and the hidden tail (`status/DIRECT.md` §14)

The domination step of the coupling (§13.4, step 3) rests on one distributional fact
(`splice_unif`): for independent uniform 256-bit `v`, `h`,
```
(ansOf t v, splice t h v)  ~  (y, g)   with y uniform on the oracle range, g uniform on St,
```
and `overlay t (ansOf t v) (splice t h v) = v` (`overlay_splice`).  Also `ansOf_unif`: the
oracle answer of a uniform label is uniform.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal SampleableType

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

/-- Split a byte vector of length `n + m`. -/
def splitV (n m : ℕ) (v : Bytes (n + m)) : Bytes n × Bytes m :=
  (Vector.ofFn fun i => v[i.castAdd m], Vector.ofFn fun i => v[i.natAdd n])

theorem splitV_bijective (n m : ℕ) : Function.Bijective (splitV n m) := by
  constructor
  · intro v w h
    simp only [splitV, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine Vector.ext fun i hi => ?_
    by_cases hin : i < n
    · have := congrArg (fun x : Bytes n => x[i]'hin) h1
      simpa using this
    · have hj : i - n < m := by omega
      have := congrArg (fun x : Bytes m => x[i - n]'hj) h2
      simp only [Vector.getElem_ofFn, Fin.natAdd] at this
      have e : n + (i - n) = i := by omega
      simpa [e] using this
  · intro p
    refine ⟨Vector.ofFn fun i : Fin (n + m) => if h : i.val < n then p.1[i.val] else
      p.2[i.val - n]'(by omega), ?_⟩
    simp only [splitV]
    refine Prod.ext ?_ ?_
    · exact Vector.ext fun i hi => by simp [hi]
    · exact Vector.ext fun i hi => by simp

theorem prEvent_split_fst (n m : ℕ) (Q : Bytes n → Prop) :
    Pr{let v ← ($ᵗ (Bytes (n + m)) : ProbComp _)}[Q (splitV n m v).1] =
      Pr{let a ← ($ᵗ (Bytes n) : ProbComp _)}[Q a] := by
  rw [prEvent_uniformSample_comp_of_bijective (splitV_bijective n m) (fun p => Q p.1),
    prEvent_uniformSample_fst]

theorem out16_eq (v : St) : out16 v = (splitV 16 16 v).1 :=
  Vector.ext fun i hi => by simp [out16, splitV]

theorem dig30_eq (v : St) : dig30 v = (splitV 30 2 v).1 :=
  Vector.ext fun i hi => by simp [dig30, splitV]

/-- **The oracle answer of a uniform label is uniform.** -/
theorem ansOf_unif (t : (hashSpec Cr).Domain) (Q : (hashSpec Cr).Range t → Prop) :
    Pr{let v ← ($ᵗ St : ProbComp St)}[Q (ansOf t v)] =
      Pr{let y ← ($ᵗ ((hashSpec Cr).Range t) : ProbComp _)}[Q y] := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · simp only [ansOf, out16_eq]
    rw [prEvent_split_fst 16 16 Q]
    exact prEvent_uniformSample_inst_irrel _ _ Q
  · simp only [ansOf, dig30_eq]
    rw [prEvent_split_fst 30 2 Q]
    exact prEvent_uniformSample_inst_irrel _ _ Q
  · simp only [ansOf, out16_eq]
    rw [prEvent_split_fst 16 16 Q]
    exact prEvent_uniformSample_inst_irrel _ _ Q

theorem ansLen_le (t : (hashSpec Cr).Domain) : ansLen t ≤ 30 := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩ <;> simp [ansLen]

/-- The answer only reads the head. -/
theorem ansOf_congr (t : (hashSpec Cr).Domain) {v w : St}
    (h : ∀ i (hi : i < 32), i < ansLen t → v[i] = w[i]) : ansOf t v = ansOf t w := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · show out16 v = out16 w
    exact Vector.ext fun i hi => by
      simp only [out16, Vector.getElem_ofFn]; exact h i (by omega) (by simp [ansLen]; omega)
  · show dig30 v = dig30 w
    exact Vector.ext fun i hi => by
      simp only [dig30, Vector.getElem_ofFn]; exact h i (by omega) (by simp [ansLen]; omega)
  · show out16 v = out16 w
    exact Vector.ext fun i hi => by
      simp only [out16, Vector.getElem_ofFn]; exact h i (by omega) (by simp [ansLen]; omega)

theorem ansOf_splice (t : (hashSpec Cr).Domain) (v h : St) : ansOf t (splice t v h) = ansOf t v :=
  ansOf_congr t fun i hi hl => by simp [splice, hl]

theorem ansBytes_ansOf (t : (hashSpec Cr).Domain) (v : St) :
    (ansBytes t (ansOf t v)).take (ansLen t) = v.toList.take (ansLen t) := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · show (out16 v).toList.take 16 = v.toList.take 16
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [out16]
  · show (dig30 v).toList.take 30 = v.toList.take 30
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [dig30]
  · show (out16 v).toList.take 16 = v.toList.take 16
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [out16]

/-- `overlay t (ansOf t v) g` is the head of `v` and the tail of `g`. -/
theorem overlay_ansOf (t : (hashSpec Cr).Domain) (v g : St) :
    overlay t (ansOf t v) g = splice t v g := by
  refine Vector.ext fun i hi => ?_
  simp only [overlay, splice, Vector.getElem_ofFn]
  rw [ansBytes_ansOf]
  have hl := ansLen_le t
  by_cases h : i < ansLen t
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp [h]
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [h, ↓reduceIte, List.getElem_drop, Vector.getElem_toList]
    congr 1
    simp only [List.length_take, Vector.length_toList]
    omega

theorem splice_self (t : (hashSpec Cr).Domain) (v : St) : splice t v v = v :=
  Vector.ext fun i hi => by simp [splice]

theorem splice_splice (t : (hashSpec Cr).Domain) (a b c : St) :
    splice t a (splice t b c) = splice t a c :=
  Vector.ext fun i hi => by by_cases h : i < ansLen t <;> simp [splice, h]

/-- **The coupled label is the label.** -/
theorem overlay_splice (t : (hashSpec Cr).Domain) (h v : St) :
    overlay t (ansOf t v) (splice t h v) = v := by
  rw [overlay_ansOf, splice_splice, splice_self]

theorem swap_bijective (t : (hashSpec Cr).Domain) :
    Function.Bijective (Function.uncurry fun v h : St => (splice t v h, splice t h v)) := by
  have hi : Function.Involutive (Function.uncurry fun v h : St => (splice t v h, splice t h v)) := by
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · exact Vector.ext fun i hi => by by_cases h : i < ansLen t <;> simp [splice, h]
    · exact Vector.ext fun i hi => by by_cases h : i < ansLen t <;> simp [splice, h]
  exact hi.bijective

/-- **Uniform splitting**: `(ansOf t v, splice t h v)` is a uniform pair. -/
theorem splice_unif (t : (hashSpec Cr).Domain) (Q : (hashSpec Cr).Range t × St → Prop) :
    Pr{let v ← ($ᵗ St : ProbComp St); let h ← ($ᵗ St : ProbComp St)}[
        Q (ansOf t v, splice t h v)] =
      Pr{let y ← ($ᵗ ((hashSpec Cr).Range t) : ProbComp _); let g ← ($ᵗ St : ProbComp St)}[
        Q (y, g)] := by
  let P' : St × St → Prop := fun p => Q (ansOf t p.1, p.2)
  calc Pr{let v ← ($ᵗ St : ProbComp St); let h ← ($ᵗ St : ProbComp St)}[
        Q (ansOf t v, splice t h v)]
      = Pr{let v ← ($ᵗ St : ProbComp St); let h ← ($ᵗ St : ProbComp St)}[
          P' (Function.uncurry (fun v h : St => (splice t v h, splice t h v)) (v, h))] := by
        simp only [P', Function.uncurry_apply_pair, ansOf_splice]
    _ = Pr{let z ← ($ᵗ (St × St) : ProbComp _)}[P' z] := by
        have := prEvent_uniformSample_pair_of_bijective (swap_bijective t) P'
        simpa only [Function.uncurry_apply_pair] using this
    _ = Pr{let a ← ($ᵗ St : ProbComp St); let b ← ($ᵗ St : ProbComp St)}[P' (a, b)] :=
        prEvent_uniformSample_prod P'
    _ = Pr{let b ← ($ᵗ St : ProbComp St); let a ← ($ᵗ St : ProbComp St)}[P' (a, b)] :=
        prEvent_bind_map_swap _ _ _
    _ = Pr{let g ← ($ᵗ St : ProbComp St); let y ← ($ᵗ ((hashSpec Cr).Range t) : ProbComp _)}[
          Q (y, g)] :=
        prEvent_bind_congr_of_support _ _ _ fun g _ => ansOf_unif t (fun y => Q (y, g))
    _ = _ := prEvent_bind_map_swap _ _ _

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.splice_unif
#print axioms Ideal.Direct.Rom.overlay_splice
