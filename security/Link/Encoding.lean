import Link.Basic

/-!
# Integer/byte conversions and address compression: `Spec` = VCVio
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- FIPS 205 Algorithm 3. -/
theorem toByte_eq (x n : Nat) : sp (SLHDSA.toByte x n) = Spec.toByte x n := by
  simp only [sp, SLHDSA.toByte, VCVio.Algorithms.Encoding.natToBytesBE, Spec.toByte, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, pow_mul]
  apply BitVec.eq_of_toNat_eq
  simp

/-- FIPS 205 Algorithm 2. -/
theorem toInt_eq (l : List UInt8) : SLHDSA.toInt l = Spec.toInt (sp l) := by
  unfold SLHDSA.toInt Spec.toInt
  generalize 0 = acc
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, sp, List.map_cons]
    rw [ih]
    simp [sp, Nat.mul_comm]

private theorem fill_eq (l : List UInt8) (b : Nat) :
    ∀ (k inp bits total : Nat), b - bits ≤ k → inp ≤ l.length →
      b ≤ bits + 8 * (l.length - inp) →
      SLHDSA.base2bFill b (l.drop inp) total bits =
          (l.drop (Spec.base2bFill (sp l) b inp bits total).1,
            (Spec.base2bFill (sp l) b inp bits total).2.2,
            (Spec.base2bFill (sp l) b inp bits total).2.1) ∧
        (Spec.base2bFill (sp l) b inp bits total).1 ≤ l.length ∧
        (Spec.base2bFill (sp l) b inp bits total).2.1 +
            8 * (l.length - (Spec.base2bFill (sp l) b inp bits total).1) =
          bits + 8 * (l.length - inp) ∧
        b ≤ (Spec.base2bFill (sp l) b inp bits total).2.1 := by
  intro k
  induction k with
  | zero =>
    intro inp bits total hk hinp hb
    have hbb : ¬ bits < b := by omega
    have e : Spec.base2bFill (sp l) b inp bits total = (inp, bits, total) := by
      rw [Spec.base2bFill]; simp only [hbb, ↓reduceIte]
    rw [e]
    refine ⟨?_, hinp, rfl, by show b ≤ bits; omega⟩
    cases hd : l.drop inp with
    | nil => rfl
    | cons y ys => simp [SLHDSA.base2bFill]; omega
  | succ k ih =>
    intro inp bits total hk hinp hb
    by_cases hbb : bits < b
    · have hlt : inp < l.length := by omega
      rw [Spec.base2bFill]; simp only [hbb, ↓reduceIte]
      have hd : l.drop inp = l[inp] :: l.drop (inp + 1) := List.drop_eq_getElem_cons hlt
      have hx : ((sp l)[inp]!).toNat = l[inp].toNat := by
        simp [sp, hlt]
      have ht : (total <<< 8) + ((sp l)[inp]!).toNat = total * 256 + l[inp].toNat := by
        rw [hx, Nat.shiftLeft_eq]
      rw [ht, hd, SLHDSA.base2bFill]; simp only [show ¬ b ≤ bits by omega, ↓reduceIte]
      have := ih (inp + 1) (bits + 8) (total * 256 + l[inp].toNat) (by omega) (by omega) (by omega)
      refine ⟨this.1, this.2.1, ?_, this.2.2.2⟩
      rw [this.2.2.1]; omega
    · have e : Spec.base2bFill (sp l) b inp bits total = (inp, bits, total) := by
        rw [Spec.base2bFill]; simp only [hbb, ↓reduceIte]
      rw [e]
      refine ⟨?_, hinp, rfl, by show b ≤ bits; omega⟩
      cases hd : l.drop inp with
      | nil => rfl
      | cons y ys => simp [SLHDSA.base2bFill]; omega

private theorem go_eq (l : List UInt8) (b : Nat) :
    ∀ (out inp bits total : Nat), inp ≤ l.length → out * b ≤ bits + 8 * (l.length - inp) →
      SLHDSA.base2bGo b out (l.drop inp) total bits = Spec.base2bGo (sp l) b out inp bits total := by
  intro out
  induction out with
  | zero => intro inp bits total _ _; rfl
  | succ out ih =>
    intro inp bits total hinp hb
    have hb' : b ≤ bits + 8 * (l.length - inp) := by
      have : (out + 1) * b = out * b + b := by ring
      omega
    obtain ⟨h1, h2, h3, h4⟩ := fill_eq l b (b - bits) inp bits total (le_refl _) hinp hb'
    simp only [SLHDSA.base2bGo, Spec.base2bGo, h1]
    congr 1
    apply ih _ _ _ h2
    have : (out + 1) * b = out * b + b := by ring
    omega

/-- FIPS 205 Algorithm 4, on inputs long enough for the requested digits (the only case FIPS 205
defines; the two transcriptions treat a short input differently). -/
theorem base2b_eq (l : List UInt8) (b out : Nat) (h : out * b ≤ 8 * l.length) :
    SLHDSA.base2b l b out = Spec.base2b (sp l) b out := by
  have := go_eq l b out 0 0 0 (Nat.zero_le _) (by simpa using h)
  simpa [SLHDSA.base2b, Spec.base2b] using this

/-- The truncating 22-byte compression agrees at every address. -/
theorem compressSha2_eq (a : SLHDSA.Adrs) : sp a.compressSha2 = (adr a).compress := by
  simp only [Adrs.compressSha2, Adrs.toBytesBE, sp_append, toByte_eq]
  simp [Spec.Adrs.compress, Spec.Adrs.bytes, adr, Spec.toByte, List.range_succ]

/-- On the checked domain VCVio's total address key is the spec's compressed address. -/
theorem adrsKey_eq (a : SLHDSA.Adrs) (h : Dom a) :
    sp (sha2AdrsKey a).toList = (adr a).compress := by
  rw [sha2AdrsKey_eq_compressed a h.1 h.2.1 h.2.2]
  simpa using compressSha2_eq a

end Link

#print axioms Link.toByte_eq
#print axioms Link.toInt_eq
#print axioms Link.base2b_eq
#print axioms Link.compressSha2_eq
#print axioms Link.adrsKey_eq
