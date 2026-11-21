import Slhdsa.Proofs.Hw.Model
open Aeneas Aeneas.Std Result

/-! The kernel's sixteen steps are the SHA-256 compression function. -/

namespace slhdsa
open Spec.SHA256

/-! ## The functions of one round -/

theorem choose_eq (x y z : Word) : Arm.SHAchoose x y z = ch x y z := by
  ext i hi
  simp only [Arm.SHAchoose, ch, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem majority_eq (x y z : Word) : Arm.SHAmajority x y z = maj x y z := by
  ext i hi
  simp only [Arm.SHAmajority, maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- The working variables as the two vectors of the kernel: `a` to `d`, and
`e` to `h`, each lowest first. -/
def toV (s : State) : Arm.V × Arm.V :=
  (⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1⟩,
    ⟨s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩)

/-- One iteration of `SHA256hash` is one round, when `w` is `W[t] + K[t]`. -/
theorem hashStep_round (W : List Word) (s : State) (t : Nat) :
    Arm.SHA256hashStep (toV s).1 (toV s).2 (W[t]! + K[t]!) = toV (round W s t) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := s
  simp only [Arm.SHA256hashStep, toV, round, choose_eq, majority_eq, Arm.SHAhashSIGMA0,
    Arm.SHAhashSIGMA1, Arm.ROR, bsig0, bsig1]
  congr 2 <;> ac_rfl

/-- Four rounds from round `t`. -/
def rounds4 (W : List Word) (s : State) (t : Nat) : State :=
  round W (round W (round W (round W s t) (t + 1)) (t + 2)) (t + 3)

/-- `SHA256H` and `SHA256H2` are the two halves of the state after four
rounds. -/
theorem sha256h_rounds (W : List Word) (s : State) (t : Nat) :
    Arm.SHA256H (toV s).1 (toV s).2 (Arm.ADD (vOf W t) (vOf K t)) = (toV (rounds4 W s t)).1 ∧
    Arm.SHA256H2 (toV s).2 (toV s).1 (Arm.ADD (vOf W t) (vOf K t)) =
      (toV (rounds4 W s t)).2 := by
  simp only [Arm.SHA256H, Arm.SHA256H2, Arm.SHA256hash, Arm.ADD, vOf, hashStep_round, rounds4]
  simp

/-! ## The message schedule -/

/-- `SHA256SU0` then `SHA256SU1` give the next four words of the schedule. -/
theorem su_eq (W : List Word)
    (hrec : ∀ k, 16 ≤ k → k < 64 →
      W[k]! = ssig1 W[k - 2]! + W[k - 7]! + ssig0 W[k - 15]! + W[k - 16]!)
    (p : Nat) (hp : p + 19 < 64) :
    Arm.SHA256SU1 (Arm.SHA256SU0 (vOf W p) (vOf W (p + 4))) (vOf W (p + 8)) (vOf W (p + 12)) =
      vOf W (p + 16) := by
  have h0 : W[p + 16]! = ssig1 W[p + 14]! + W[p + 9]! + ssig0 W[p + 1]! + W[p]! := by
    have := hrec (p + 16) (by omega) (by omega)
    rwa [show p + 16 - 2 = p + 14 by omega, show p + 16 - 7 = p + 9 by omega,
      show p + 16 - 15 = p + 1 by omega, show p + 16 - 16 = p by omega] at this
  have h1 : W[p + 17]! = ssig1 W[p + 15]! + W[p + 10]! + ssig0 W[p + 2]! + W[p + 1]! := by
    have := hrec (p + 17) (by omega) (by omega)
    rwa [show p + 17 - 2 = p + 15 by omega, show p + 17 - 7 = p + 10 by omega,
      show p + 17 - 15 = p + 2 by omega, show p + 17 - 16 = p + 1 by omega] at this
  have h2 : W[p + 18]! = ssig1 W[p + 16]! + W[p + 11]! + ssig0 W[p + 3]! + W[p + 2]! := by
    have := hrec (p + 18) (by omega) (by omega)
    rwa [show p + 18 - 2 = p + 16 by omega, show p + 18 - 7 = p + 11 by omega,
      show p + 18 - 15 = p + 3 by omega, show p + 18 - 16 = p + 2 by omega] at this
  have h3 : W[p + 19]! = ssig1 W[p + 17]! + W[p + 12]! + ssig0 W[p + 4]! + W[p + 3]! := by
    have := hrec (p + 19) (by omega) (by omega)
    rwa [show p + 19 - 2 = p + 17 by omega, show p + 19 - 7 = p + 12 by omega,
      show p + 19 - 15 = p + 4 by omega, show p + 19 - 16 = p + 3 by omega] at this
  simp only [Arm.SHA256SU1, Arm.SHA256SU0, vOf, Nat.add_assoc, Nat.reduceAdd]
  rw [h2, h3, h0, h1]
  simp only [Arm.ROR, Arm.LSR, ssig0, ssig1]
  congr 1 <;> ac_rfl

theorem app_left (l : List Word) (x : Word) (i : Nat) (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem app_right (l : List Word) (x : Word) : (l ++ [x])[l.length]! = x := by
  simp

theorem set_self' (l : List Arm.V) (i : Nat) (x : Arm.V) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem set_ne' (l : List Arm.V) (i j : Nat) (x : Arm.V) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

theorem repeat_length (l : List Word) (n : Nat) :
    (Nat.repeat scheduleStep n l).length = l.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeat_succ, scheduleStep, ih]; omega

theorem repeat_prefix (l : List Word) (n m i : Nat) (h : i < l.length + n) (hm : n ≤ m) :
    (Nat.repeat scheduleStep m l)[i]! = (Nat.repeat scheduleStep n l)[i]! := by
  induction m with
  | zero => rw [show n = 0 by omega]
  | succ m ih =>
    by_cases hn : n = m + 1
    · rw [hn]
    · rw [← ih (by omega), repeat_succ]
      have hl := repeat_length l m
      generalize Nat.repeat scheduleStep m l = R at hl ⊢
      simp only [scheduleStep]
      exact app_left _ _ _ (by omega)

theorem schedule_lt16 (B : Spec.Bytes) (k : Nat) (hk : k < 16) :
    (schedule B)[k]! = word B (4 * k) := by
  rw [schedule, repeat_prefix _ 0 48 k (by simp [blockWords]; omega) (by omega)]
  simp [Nat.repeat, blockWords, hk]

theorem schedule_rec (B : Spec.Bytes) (k : Nat) (hk1 : 16 ≤ k) (hk2 : k < 64) :
    (schedule B)[k]! = ssig1 (schedule B)[k - 2]! + (schedule B)[k - 7]! +
      ssig0 (schedule B)[k - 15]! + (schedule B)[k - 16]! := by
  have hb : (blockWords B).length = 16 := by simp [blockWords]
  have hp : ∀ j, j < k → (schedule B)[j]! = (Nat.repeat scheduleStep (k - 16) (blockWords B))[j]! :=
    fun j hj => repeat_prefix _ _ _ _ (by omega) (by omega)
  have hk : (schedule B)[k]! = (Nat.repeat scheduleStep (k - 16 + 1) (blockWords B))[k]! :=
    repeat_prefix _ _ _ _ (by omega) (by omega)
  rw [hk, hp (k - 2) (by omega), hp (k - 7) (by omega), hp (k - 15) (by omega),
    hp (k - 16) (by omega), repeat_succ]
  have hl := repeat_length (blockWords B) (k - 16)
  generalize Nat.repeat scheduleStep (k - 16) (blockWords B) = R at hl ⊢
  have hk' : k = R.length := by omega
  subst hk'
  simp only [scheduleStep]
  exact app_right _ _

/-! ## The sixteen steps -/

theorem foldl_range4 {α} (f : α → Nat → α) (x : α) (n : Nat) :
    (List.range (n + 4)).foldl f x =
      f (f (f (f ((List.range n).foldl f x) n) (n + 1)) (n + 2)) (n + 3) := by
  simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem kfold_inv (st : List Word) (B : Spec.Bytes) (i : Nat) (hi : i ≤ 16) :
    let s := (List.range i).foldl kstep ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩
    (s.abcd, s.efgh) = toV ((List.range (4 * i)).foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!)) ∧
      s.m.length = 4 ∧
      ∀ j, i ≤ j → j < i + 4 → j < 16 → s.m[j % 4]! = vOf (schedule B) (4 * j) := by
  induction i with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro j _ hj _
    have e : ∀ k, k < 16 → (schedule B)[k]! = word B (4 * k) := schedule_lt16 B
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [vOf, beV, e]
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    intro s
    generalize hs0 : (List.range i).foldl kstep
      ⟨vOf st 0, vOf st 4, [beV B 0, beV B 16, beV B 32, beV B 48]⟩ = s0 at h1 h2 h3
    have hs : s = kstep s0 i := by
      simp only [s, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hs0]
    clear_value s
    subst hs
    generalize hr : (List.foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!) (List.range (4 * i))) = r at h1
    have hab : s0.abcd = (toV r).1 := by rw [← h1]
    have hef : s0.efgh = (toV r).2 := by rw [← h1]
    have hm0 : s0.m[i % 4]! = vOf (schedule B) (4 * i) := h3 i le_rfl (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [show 4 * (i + 1) = 4 * i + 4 by omega, foldl_range4, hr]
      obtain ⟨e1, e2⟩ := sha256h_rounds (schedule B) r (4 * i)
      simp only [kstep, hm0, hab, hef, e1, e2]
      rfl
    · simp only [kstep]
      split <;> simp [h2]
    · intro j hj1 hj2 hj3
      simp only [kstep]
      split
      · rename_i hi12
        by_cases hj : j = i + 4
        · subst hj
          rw [show (i + 4) % 4 = i % 4 by omega, set_self' _ _ _ (by omega)]
          rw [hm0, h3 (i + 1) (by omega) (by omega) (by omega),
            h3 (i + 2) (by omega) (by omega) (by omega),
            h3 (i + 3) (by omega) (by omega) (by omega)]
          rw [show 4 * (i + 1) = 4 * i + 4 by omega, show 4 * (i + 2) = 4 * i + 8 by omega,
            show 4 * (i + 3) = 4 * i + 12 by omega, show 4 * (i + 4) = 4 * i + 16 by omega]
          exact su_eq _ (schedule_rec B) _ (by omega)
        · rw [set_ne' _ _ _ _ (by omega)]
          exact h3 j (by omega) (by omega) hj3
      · exact h3 j (by omega) (by omega) hj3

/-- The sixteen steps of the kernel, with the initial working variables added
back, are the compression function of FIPS 180-4. -/
theorem kcompress_eq (st : List Word) (hst : st.length = 8) (B : Spec.Bytes) (hB : B.length = 64) :
    vwords (Arm.ADD (kcompress (vOf st 0) (vOf st 4) (beV B 0) (beV B 16) (beV B 32) (beV B 48)).abcd
        (vOf st 0)) ++
      vwords (Arm.ADD (kcompress (vOf st 0) (vOf st 4) (beV B 0) (beV B 16) (beV B 32) (beV B 48)).efgh
        (vOf st 4)) = compress st B := by
  obtain ⟨h1, -, -⟩ := kfold_inv st B 16 le_rfl
  simp only [kcompress]
  generalize (List.range 16).foldl kstep _ = s at h1
  simp only [compress]
  generalize (List.foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!) (List.range (4 * 16))) = r at h1
  obtain ⟨a, b, c, d, e, f, g, h⟩ := r
  simp only [toV, Prod.mk.injEq] at h1
  obtain ⟨ha, he⟩ := h1
  simp only [ha, he, vwords, Arm.ADD, vOf]
  simp [BitVec.add_comm]

end slhdsa
