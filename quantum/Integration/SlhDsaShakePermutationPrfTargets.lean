import Integration.SlhDsaShakePermutationManifest

/-! Simultaneous target words for all secret keys and formatted public rows.
Keys sharing a public row share its short output, while every full word has
a separately sampled private suffix. The old images may be any fixed table. -/
namespace Reduction.ShakePermutation.PrfTargets
open Classical ENNReal
set_option linter.unusedSectionVars false
noncomputable section
variable {K J H S : Type} [Fintype K] [Fintype J] [Fintype H] [Fintype S]
variable [DecidableEq K] [DecidableEq J]
abbrev Row (K J : Type) := K × J
abbrev World (K J H S : Type) := (J → H) × (Row K J → S)

def val (w : World K J H S) (r : Row K J) := (w.1 r.2, w.2 r)

def put (w : World K J H S) (r : Row K J) (u : H × S) : World K J H S :=
  (Function.update w.1 r.2 u.1, Function.update w.2 r u.2)

def putSuffix (w : World K J H S) (r : Row K J) (s : S) : World K J H S :=
  (w.1,Function.update w.2 r s)

@[simp] theorem val_put (w : World K J H S) (r : Row K J) (u : H × S) :
    val (put w r u) r = u := by simp [val,put]

theorem val_put_other (w : World K J H S) (r t : Row K J) (u : H × S)
    (hj : t.2 ≠ r.2) : val (put w r u) t = val w t := by
  have ne : t ≠ r := fun eq => hj (congrArg Prod.snd eq)
  simp [val, put, Function.update_of_ne, hj, ne]

@[simp] theorem put_back (w : World K J H S) (r : Row K J) (u : H × S) :
    put (put w r u) r (val w r) = w := by simp [put,val,Function.update_idem]

private theorem row_count (r : Row K J) (get : World K J H S → H × S)
    (stable : ∀ w u, get (put w r u) = get w) :
    Fintype.card {w : World K J H S // val w r = get w} * Fintype.card (H × S) ≤
      Fintype.card (World K J H S) := by
  classical
  rw [← Fintype.card_prod]
  let encode (p : {w : World K J H S // val w r = get w} × (H × S)) := put p.1.val r p.2
  apply Fintype.card_le_of_injective encode
  rintro ⟨⟨w,hw⟩,a⟩ ⟨⟨v,hv⟩,b⟩ eq
  change put w r a = put v r b at eq
  have hab := congrArg (fun d => val d r) eq
  have hget := congrArg get eq
  simp only [val_put] at hab
  simp only [stable, ← hw, ← hv] at hget
  have same : w = v := by
    calc w = put (put w r a) r (val w r) := (put_back ..).symm
         _ = put (put v r b) r (val v r) := by rw [eq,hget]
         _ = v := put_back ..
  exact Prod.ext (Subtype.ext same) hab

private theorem suffix_count (r t : Row K J) (ne : r ≠ t) :
    Fintype.card {w : World K J H S // w.2 r = w.2 t} * Fintype.card S ≤
      Fintype.card (World K J H S) := by
  classical
  rw [← Fintype.card_prod]
  let encode (p : {w : World K J H S // w.2 r = w.2 t} × S) := putSuffix p.1.val r p.2
  apply Fintype.card_le_of_injective encode
  rintro ⟨⟨w,hw⟩,a⟩ ⟨⟨v,hv⟩,b⟩ eq
  change putSuffix w r a = putSuffix v r b at eq
  have first := congrArg Prod.fst eq
  have hab := congrArg (fun d : World K J H S => d.2 r) eq
  have other := congrArg (fun d : World K J H S => d.2 t) eq
  simp [putSuffix,Ne.symm ne] at hab other
  apply Prod.ext (Subtype.ext (Prod.ext first ?_)) hab
  funext x
  by_cases hx : x = r
  · simpa [hx,hw,hv] using other
  · have atx := congrArg (fun d : World K J H S => d.2 x) eq
    simpa [putSuffix,Function.update_of_ne hx] using atx

def Bad (old : Row K J → H × S) (w : World K J H S) :=
  (¬ Function.Injective (val w)) ∨ ∃ r t, val w r = old t

private abbrev Cases (K J : Type) := (K × K × J) ⊕ ((Row K J × Row K J) ⊕ (Row K J × Row K J))

private def hit (old : Row K J → H × S) : Cases K J → World K J H S → Prop
  | .inl (k,l,j), w => k ≠ l ∧ w.2 (k,j) = w.2 (l,j)
  | .inr (.inl (r,t)), w => r.2 ≠ t.2 ∧ val w r = val w t
  | .inr (.inr (r,t)), w => val w r = old t

private theorem witness (old : Row K J → H × S) (w : World K J H S) (bad : Bad old w) :
    ∃ i, hit old i w := by
  rcases bad with bad | ⟨r,t,ht⟩
  · unfold Function.Injective at bad
    push Not at bad
    obtain ⟨⟨k,j⟩,⟨l,n⟩,eq,ne⟩ := bad
    by_cases hj : j = n
    · subst n
      exact ⟨.inl (k,l,j),fun e => ne (Prod.ext e rfl),congrArg Prod.snd eq⟩
    · exact ⟨.inr (.inl ((k,j),(l,n))),hj,eq⟩
  · exact ⟨.inr (.inr (r,t)),ht⟩


private def multiplier (head : ℕ) : Cases K J → ℕ
  | .inl _ => head
  | .inr _ => 1

private theorem single_count (old : Row K J → H × S) (i : Cases K J) :
    Fintype.card {w // hit old i w} * Fintype.card (H × S) ≤
      Fintype.card (World K J H S) * multiplier (Fintype.card H) i := by
  classical
  rcases i with ⟨k,l,j⟩ | (⟨r,t⟩|⟨r,t⟩)
  · by_cases ne : k ≠ l
    · have bound := suffix_count (H:=H) (S:=S) ((k,j) : Row K J) (l,j) (fun e => ne (congrArg Prod.fst e))
      have bound' := Nat.mul_le_mul_right (Fintype.card H) bound
      simpa [hit,ne,multiplier,Fintype.card_prod,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound'
    · simp [hit,ne]
  · by_cases ne : r.2 ≠ t.2
    · have bound := row_count r (fun w : World K J H S => val w t)
        (fun w u => val_put_other w r t u ne.symm)
      simpa [hit,ne,multiplier] using bound
    · simp [hit,ne]
  · rw [show multiplier (Fintype.card H) (.inr (.inr (r,t))) = 1 from rfl,mul_one]
    convert! row_count r (fun _ : World K J H S => old t) (fun _ _ => rfl) using 2
    exact Fintype.card_congr (Equiv.refl _)

theorem bad_count (old : Row K J → H × S) :
    Fintype.card {w // Bad old w} * Fintype.card (H × S) ≤ Fintype.card (World K J H S) *
      (Fintype.card K ^ 2 * Fintype.card J * Fintype.card H +
        2 * (Fintype.card K * Fintype.card J)^2) := by
  classical
  let tag (w : {w // Bad old w}) := (witness old w.val w.property).choose
  let encode (w : {w // Bad old w}) : Σ i, {s // hit old i s} :=
    ⟨tag w, w.val,(witness old w.val w.property).choose_spec⟩
  have inj : Function.Injective encode := fun _ _ eq => Subtype.ext
    (congrArg (fun u : Σ i, {s // hit old i s} => u.2.val) eq)
  have hw := Nat.mul_le_mul_right (Fintype.card (H × S)) (Fintype.card_le_of_injective encode inj)
  rw [Fintype.card_sigma, Finset.sum_mul] at hw
  refine hw.trans ((Finset.sum_le_sum (fun i _ => single_count old i)).trans_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  simp [Fintype.sum_sum_type,multiplier,Fintype.card_prod,Row]
  ring


/-- Strict uniform failure probability below 2⁻⁵⁵, written as an exact
integer ratio. The old full words may be an arbitrary fixed family. -/
theorem benchmark_count [Nonempty H] [Nonempty S] (old : Row K J → H × S)
    (keys : Fintype.card K ≤ 2^256) (rows : Fintype.card J ≤ 2^512)
    (heads : Fintype.card H ≤ 2^256) (words : Fintype.card (H × S) = 2^1600) :
    Fintype.card {w // Bad old w} * 2^55 < Fintype.card (World K J H S) := by
  classical
  let n := Fintype.card (World K J H S)
  have pos : 0 < n := Fintype.card_pos
  have c := bad_count old
  rw [words] at c
  have lim : Fintype.card K ^ 2 * Fintype.card J * Fintype.card H +
        2 * (Fintype.card K * Fintype.card J)^2 ≤
        (2^256)^2 * 2^512 * 2^256 + 2 * (2^256 * 2^512)^2 := by gcongr
  have num : ((2^256)^2 * 2^512 * 2^256 + 2 * (2^256 * 2^512)^2) * 2^55 < (2:ℕ)^1600 := by
    decide +kernel
  have b := Nat.mul_le_mul_right (2^55) (c.trans (Nat.mul_le_mul_left n lim))
  have strict := Nat.mul_lt_mul_of_pos_left num pos
  rw [Nat.mul_assoc n] at b
  rw [Nat.mul_right_comm] at b
  exact Nat.lt_of_mul_lt_mul_right (b.trans_lt strict)

theorem benchmark_mean [Nonempty H] [Nonempty S] (old : Row K J → H × S)
    (keys : Fintype.card K ≤ 2^256) (rows : Fintype.card J ≤ 2^512)
    (heads : Fintype.card H ≤ 2^256) (words : Fintype.card (H × S) = 2^1600) :
    SetOracle.uniformMean (fun w => if Bad old w then 1 else 0) < ((2:ℝ≥0∞)^55)⁻¹ := by
  classical
  let n := Fintype.card (World K J H S)
  let b := Fintype.card {w // Bad old w}
  have prob : SetOracle.uniformMean (fun w => if Bad old w then 1 else 0) =
      (n : ℝ≥0∞)⁻¹ * b := by
    simp [SetOracle.uniformMean,unifW,n,b,Fintype.card_subtype,mul_comm]
  rw [prob]
  have lt : b * 2^55 < n := benchmark_count old keys rows heads words
  have lt' : (b:ℝ≥0∞) * (2:ℝ≥0∞)^55 < n := by exact_mod_cast lt
  have nz : (n:ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  calc
    _ = ((n:ℝ≥0∞)⁻¹ * ((b:ℝ≥0∞) * 2^55)) * ((2:ℝ≥0∞)^55)⁻¹ := by
      rw [mul_assoc,mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]
    _ < ((n:ℝ≥0∞)⁻¹ * n) * ((2:ℝ≥0∞)^55)⁻¹ := by
      gcongr <;> simp [nz]
    _ = _ := by rw [ENNReal.inv_mul_cancel nz (by simp),one_mul]

end
end Reduction.ShakePermutation.PrfTargets
#print axioms Reduction.ShakePermutation.PrfTargets.benchmark_mean
