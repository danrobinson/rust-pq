import Slhdsa.Proofs.Sha512Core
import Arm
open Aeneas Aeneas.Std Result

/-! The SHA-512 kernel of `rust/src/sha512.rs`, module `hw`, as a pure
function over the instruction model (`Arm.lean`), and the proof that its
forty steps are the SHA-512 compression function of FIPS 180-4
(`kcompress_eq`). `Compress.lean` proves `sha512::hw::compress_block` equal
to it. -/

namespace slhdsa.H512
open Spec.SHA512


/-- The two elements of a vector, lowest first. -/
def vwords2 (v : Arm.V2) : List Word := [v.e0, v.e1]

/-- The vector of the two words `l[i]`, `l[i + 1]`. -/
def vOf2 (l : List Word) (i : Nat) : Arm.V2 := ⟨l[i]!, l[i + 1]!⟩

/-- The vector of the two big-endian words at bytes `B[i]`, …, `B[i + 15]`. -/
def beV2 (B : Spec.Bytes) (i : Nat) : Arm.V2 := ⟨word B i, word B (i + 8)⟩

/-- The kernel between steps: the working variables in pairs and the eight
most recent schedule vectors, the one that step `i` consumes at `i % 8`. -/
structure KState where
  ab : Arm.V2
  cd : Arm.V2
  ef : Arm.V2
  gh : Arm.V2
  m : List Arm.V2

/-- Step `i`: rounds `2i`, `2i + 1`, and for `i < 32` the schedule words
`W[2i + 16]`, `W[2i + 17]`. -/
def kstep (s : KState) (i : Nat) : KState :=
  let wk := Arm.ADD2 s.m[i % 8]! (vOf2 K (2 * i))
  let sum := Arm.ADD2 (Arm.EXT1 wk wk) s.gh
  let t := Arm.SHA512H sum (Arm.EXT1 s.ef s.gh) (Arm.EXT1 s.cd s.ef)
  { ab := Arm.SHA512H2 t s.cd s.ab
    cd := s.ab
    ef := Arm.ADD2 s.cd t
    gh := s.ef
    m := if i < 32 then
        s.m.set (i % 8)
          (Arm.SHA512SU1 (Arm.SHA512SU0 s.m[i % 8]! s.m[(i + 1) % 8]!) s.m[(i + 7) % 8]!
            (Arm.EXT1 s.m[(i + 4) % 8]! s.m[(i + 5) % 8]!))
      else s.m }

/-- The forty steps from the working variables `ab0` … `gh0` on the block
whose schedule vectors are `ms`. -/
def kcompress (ab0 cd0 ef0 gh0 : Arm.V2) (ms : List Arm.V2) : KState :=
  (List.range 40).foldl kstep ⟨ab0, cd0, ef0, gh0, ms⟩

/-- The working variables as the kernel's four vectors. -/
def toV (s : State) : Arm.V2 × Arm.V2 × Arm.V2 × Arm.V2 :=
  let (a, b, c, d, e, f, g, h) := s
  (⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩)

theorem maj_cba (a b c : Word) : (c &&& b) ^^^ (c &&& a) ^^^ (b &&& a) = maj a b c := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

theorem maj_xab (x a b : Word) : (x &&& a) ^^^ (x &&& b) ^^^ (b &&& a) = maj x a b := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases x[i] <;> rfl

/-- ,  and the additions around them are two rounds. -/
theorem two_rounds (W : List Word) (s : State) (t : Nat) :
    let wk := Arm.ADD2 (vOf2 W t) (vOf2 K t)
    let v := toV s
    let sum := Arm.ADD2 (Arm.EXT1 wk wk) v.2.2.2
    let x := Arm.SHA512H sum (Arm.EXT1 v.2.2.1 v.2.2.2) (Arm.EXT1 v.2.1 v.2.2.1)
    (Arm.SHA512H2 x v.2.1 v.1, v.1, Arm.ADD2 v.2.1 x, v.2.2.1) = toV (round W (round W s t) (t + 1)) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := s
  have hch : ∀ x y z : Word, (x &&& y) ^^^ (~~~x &&& z) = ch x y z := fun _ _ _ => rfl
  have hs1 : ∀ x : Word, Arm.ROR64 x 14 ^^^ Arm.ROR64 x 18 ^^^ Arm.ROR64 x 41 = bsig1 x := fun _ => rfl
  have hs0 : ∀ x : Word, Arm.ROR64 x 28 ^^^ Arm.ROR64 x 34 ^^^ Arm.ROR64 x 39 = bsig0 x := fun _ => rfl
  simp only [toV, round, Arm.SHA512H, Arm.SHA512H2, Arm.ADD2, Arm.EXT1, vOf2, hch, hs0, hs1, maj_cba,
    maj_xab]
  generalize hT1 : h + bsig1 e + ch e f g + K[t]! + W[t]! = T1
  have e1 : ch e f g + bsig1 e + (W[t]! + K[t]! + h) = T1 := by rw [← hT1]; ac_rfl
  simp only [e1]
  simp only [Prod.mk.injEq, Arm.V2.mk.injEq, and_true, true_and]
  have e2 : T1 + d = d + T1 := BitVec.add_comm _ _
  have e3 : T1 + (bsig0 a + maj a b c) = maj a b c + bsig0 a + T1 := by ac_rfl
  rw [e2, e3]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> ac_rfl

/-! ## The message schedule -/

/-- `SHA512SU0`, `EXT` and `SHA512SU1` give the next two words of the schedule. -/
theorem su_eq (W : List Word)
    (hrec : ∀ k, 16 ≤ k → k < 80 →
      W[k]! = ssig1 W[k - 2]! + W[k - 7]! + ssig0 W[k - 15]! + W[k - 16]!)
    (p : Nat) (hp : p + 17 < 80) :
    Arm.SHA512SU1 (Arm.SHA512SU0 (vOf2 W p) (vOf2 W (p + 2))) (vOf2 W (p + 14))
        (Arm.EXT1 (vOf2 W (p + 8)) (vOf2 W (p + 10))) = vOf2 W (p + 16) := by
  have h0 : W[p + 16]! = ssig1 W[p + 14]! + W[p + 9]! + ssig0 W[p + 1]! + W[p]! := by
    have := hrec (p + 16) (by omega) (by omega)
    rwa [show p + 16 - 2 = p + 14 by omega, show p + 16 - 7 = p + 9 by omega,
      show p + 16 - 15 = p + 1 by omega, show p + 16 - 16 = p by omega] at this
  have h1 : W[p + 17]! = ssig1 W[p + 15]! + W[p + 10]! + ssig0 W[p + 2]! + W[p + 1]! := by
    have := hrec (p + 17) (by omega) (by omega)
    rwa [show p + 17 - 2 = p + 15 by omega, show p + 17 - 7 = p + 10 by omega,
      show p + 17 - 15 = p + 2 by omega, show p + 17 - 16 = p + 1 by omega] at this
  simp only [Arm.SHA512SU1, Arm.SHA512SU0, Arm.EXT1, vOf2, Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1]
  simp only [Arm.ROR64, Arm.LSR64, ssig0, ssig1]
  congr 1 <;> ac_rfl

theorem app_left (l : List Word) (x : Word) (i : Nat) (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem app_right (l : List Word) (x : Word) : (l ++ [x])[l.length]! = x := by
  simp

theorem set_self' (l : List Arm.V2) (i : Nat) (x : Arm.V2) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

theorem set_ne' (l : List Arm.V2) (i j : Nat) (x : Arm.V2) (h : i ≠ j) :
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
    (schedule B)[k]! = word B (8 * k) := by
  rw [schedule, repeat_prefix _ 0 64 k (by simp [blockWords]; omega) (by omega)]
  simp [Nat.repeat, blockWords, hk]

theorem schedule_rec (B : Spec.Bytes) (k : Nat) (hk1 : 16 ≤ k) (hk2 : k < 80) :
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

/-! ## The forty steps -/

theorem foldl_range2 {α} (f : α → Nat → α) (x : α) (n : Nat) :
    (List.range (n + 2)).foldl f x = f (f ((List.range n).foldl f x) n) (n + 1) := by
  simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The schedule vectors the kernel loads from a block. -/
def blockVs (B : Spec.Bytes) : List Arm.V2 :=
  [beV2 B 0, beV2 B 16, beV2 B 32, beV2 B 48, beV2 B 64, beV2 B 80, beV2 B 96, beV2 B 112]

theorem kfold_inv (st : List Word) (B : Spec.Bytes) (i : Nat) (hi : i ≤ 40) :
    let s := (List.range i).foldl kstep ⟨vOf2 st 0, vOf2 st 2, vOf2 st 4, vOf2 st 6, blockVs B⟩
    (s.ab, s.cd, s.ef, s.gh) = toV ((List.range (2 * i)).foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!)) ∧
      s.m.length = 8 ∧
      ∀ j, i ≤ j → j < i + 8 → j < 40 → s.m[j % 8]! = vOf2 (schedule B) (2 * j) := by
  induction i with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro j _ hj _
    have e : ∀ k, k < 16 → (schedule B)[k]! = word B (8 * k) := schedule_lt16 B
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [vOf2, beV2, blockVs, e]
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    intro s
    generalize hs0 : (List.range i).foldl kstep
      ⟨vOf2 st 0, vOf2 st 2, vOf2 st 4, vOf2 st 6, blockVs B⟩ = s0 at h1 h2 h3
    have hs : s = kstep s0 i := by
      simp only [s, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hs0]
    clear_value s
    subst hs
    generalize hr : (List.foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!) (List.range (2 * i))) = r at h1
    have hm0 : s0.m[i % 8]! = vOf2 (schedule B) (2 * i) := h3 i (Nat.le_refl _) (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 2 by omega, foldl_range2, hr]
      rw [← two_rounds (schedule B) r (2 * i)]
      have ha : s0.ab = (toV r).1 := congrArg Prod.fst h1
      have hc : s0.cd = (toV r).2.1 := congrArg (·.2.1) h1
      have he : s0.ef = (toV r).2.2.1 := congrArg (·.2.2.1) h1
      have hg : s0.gh = (toV r).2.2.2 := congrArg (·.2.2.2) h1
      simp only [kstep, hm0, ha, hc, he, hg]
    · simp only [kstep]
      split <;> simp [h2]
    · intro j hj1 hj2 hj3
      simp only [kstep]
      split
      · rename_i hi32
        by_cases hj : j = i + 8
        · subst hj
          rw [show (i + 8) % 8 = i % 8 by omega, set_self' _ _ _ (by omega)]
          rw [hm0, h3 (i + 1) (by omega) (by omega) (by omega),
            h3 (i + 7) (by omega) (by omega) (by omega),
            h3 (i + 4) (by omega) (by omega) (by omega),
            h3 (i + 5) (by omega) (by omega) (by omega)]
          rw [show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * (i + 7) = 2 * i + 14 by omega,
            show 2 * (i + 4) = 2 * i + 8 by omega, show 2 * (i + 5) = 2 * i + 10 by omega,
            show 2 * (i + 8) = 2 * i + 16 by omega]
          exact su_eq _ (schedule_rec B) _ (by omega)
        · rw [set_ne' _ _ _ _ (by omega)]
          exact h3 j (by omega) (by omega) hj3
      · exact h3 j (by omega) (by omega) hj3

/-- The forty steps of the kernel, with the initial working variables added
back, are the SHA-512 compression function of FIPS 180-4. -/
theorem kcompress_eq (st : List Word) (B : Spec.Bytes) :
    let s := kcompress (vOf2 st 0) (vOf2 st 2) (vOf2 st 4) (vOf2 st 6) (blockVs B)
    vwords2 (Arm.ADD2 s.ab (vOf2 st 0)) ++ vwords2 (Arm.ADD2 s.cd (vOf2 st 2)) ++
      (vwords2 (Arm.ADD2 s.ef (vOf2 st 4)) ++ vwords2 (Arm.ADD2 s.gh (vOf2 st 6))) =
      compress st B := by
  obtain ⟨h1, -, -⟩ := kfold_inv st B 40 (Nat.le_refl _)
  simp only [kcompress]
  generalize (List.range 40).foldl kstep _ = s at h1
  simp only [compress]
  generalize (List.foldl (round (schedule B))
        (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!) (List.range (2 * 40))) = r at h1
  obtain ⟨a, b, c, d, e, f, g, h⟩ := r
  simp only [toV, Prod.mk.injEq] at h1
  obtain ⟨ha, hc, he, hg⟩ := h1
  simp only [ha, hc, he, hg, vwords2, Arm.ADD2, vOf2]
  simp [BitVec.add_comm]

end slhdsa.H512
