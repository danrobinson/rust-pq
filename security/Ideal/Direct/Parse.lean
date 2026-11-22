import Ideal.Direct.Tagged
import Ideal.Realize.MsgMark
import Ideal.Inst.SkPrf128Fine

/-!
# Parse classes of a compression cell (D2 of `status/DIRECT.md`, block-level part)

A compression cell `(c, b)` of the SLH-DSA-SHA2-128s table is classified by its chaining value
and by the **tweak bytes** `btw128 b` (bytes `0..21` of the block, where the first `Thash` block
carries `ADRSc`), relative to the public midstate `cv = g (IV, sb128 PK.seed)` and to a
classifier `aty` of tweaks (which tweaks are `PRF` (secret-key) addresses, which are honest
single-block `Thash` tweaks (`F`, `H`), which are honest multi-block ones (`T_len`, `T_k`)):

* `Role`: `kprf` (`c = IV`, `b` an HMAC key block), `kseed a k` (`c = cv`, `b = blk128 a k`),
  `th1 A xs` (`c = cv`, `b` the first block of a one- or two-value `Thash` at a short tweak `A`),
  `thF A` (`c = cv`, tweak `A` long: the first block of a `T_len`/`T_k` evaluation), `other`.
* `role`: the classification (priority `kprf`, `kseed`, `th1`, `thF`); `role_*` characterisations;
  `blk_short_unique`: a short first block determines its tweak and input;
  `kprf_not_short`: an HMAC key block is never a short `Thash` block.

**Deviation from the plan (§2.3).**  The plan claims the classes are disjoint *by block shape*.
They are not, at the level of single blocks: the first block of a 35-value `T_len` input carries
data in bytes `22..63`, so it can equal the first block of a one-value `Thash` call at the same
tweak (data `x ‖ 0x80 ‖ 0^17 ‖ len64(816)` in bytes `22..63`).  What does hold, and what the
classification below uses, is that the tweak bytes decide the class: an address is either a
`PRF`, a short-`Thash` or a long-`Thash` address (address-type byte inside `ADRSc`), so the
honest structure has at most one class at every tweak.  The rooted-chain classes `ThL` (last block
of a long chain) and `HmF` (the `H_msg` outer final cell) depend on the cache (rooted chains) and
are not defined here (they belong to the collision part, D4/D6).
-/

open OracleComp OracleSpec ENNReal SLHDSA SLHDSA.Security SLHDSA.Concrete

namespace Ideal.Direct

/-- The kind of a tweak (22 tweak bytes) in the honest structure. -/
inductive AdKind
  | prf
  | short
  | long
  | none
deriving DecidableEq, Repr

/-- Parse class of a compression cell. -/
inductive Role
  | kprf
  | kseed (a : SkAd) (k : Bytes 16)
  | th1 (A : Bytes 22) (xs : List (Bytes 16))
  | thF (A : Bytes 22)
  | other

/-- A short (one- or two-value) `Thash` input. -/
def ShortIn (xs : List (Bytes 16)) : Prop := xs.length = 1 ∨ xs.length = 2

theorem short_snd {A : Bytes 22} {xs : List (Bytes 16)} (h : ShortIn xs) : (tblocks A xs).2 = [] :=
  h.elim (tblocks_snd_of_length_one A xs) (tblocks_snd_of_length_two A xs)

/-- **A short first block determines its tweak and its input.** -/
theorem blk_short_unique {A A' : Bytes 22} {xs xs' : List (Bytes 16)} (h : ShortIn xs)
    (h' : ShortIn xs') (he : (tblocks A xs).1 = (tblocks A' xs').1) : A = A' ∧ xs = xs' :=
  tblocks_injective (Prod.ext he (by rw [short_snd h, short_snd h']))

/-- **An HMAC key block is never a short `Thash` block** (padding byte `0x80`). -/
theorem kprf_not_short {A : Bytes 22} {xs : List (Bytes 16)} (h : ShortIn xs) (k : Bytes 16) :
    (tblocks A xs).1 ≠ ikey k ∧ (tblocks A xs).1 ≠ okey k := by
  have hn := tblocks_not_keyBlk A xs (by rcases h with h | h <;> omega)
  exact ⟨fun e => hn ⟨k, .inl e⟩, fun e => hn ⟨k, .inr e⟩⟩

/-- The seed block is no HMAC key block. -/
theorem kprf_not_seed (pk k : Bytes 16) : sb128 pk ≠ ikey k ∧ sb128 pk ≠ okey k := by
  have hn := sb128_not_keyBlk pk
  exact ⟨fun e => hn ⟨k, .inl e⟩, fun e => hn ⟨k, .inr e⟩⟩

/-- The tweak of a key block is its secret-key address. -/
theorem btw_blk128 (a : SkAd) (k : Bytes 16) : btw128 (blk128 a k) = sha2AdrsKey a.val :=
  btw128_tblocks _ _

section Role

variable (cv : St) (aty : Bytes 22 → AdKind)

open Classical in
/-- **The parse class of a cell** (priority `kprf`, `kseed`, `th1`, `thF`). -/
noncomputable def role (q : St × Blk) : Role :=
  if q.1 = IV128 ∧ ∃ k, q.2 = ikey k ∨ q.2 = okey k then .kprf
  else if q.1 = cv then
    if h : aty (btw128 q.2) = .prf ∧ ∃ a k, q.2 = blk128 a k then
      .kseed (Classical.choose h.2) (Classical.choose (Classical.choose_spec h.2))
    else if h : aty (btw128 q.2) = .short ∧ ∃ xs, ShortIn xs ∧ q.2 = (tblocks (btw128 q.2) xs).1 then
      .th1 (btw128 q.2) (Classical.choose h.2)
    else if aty (btw128 q.2) = .long then .thF (btw128 q.2)
    else .other
  else .other

/-- A key block at a `PRF` tweak in row `cv` is `kseed` of its address and key. -/
theorem role_blk128 (hcv : cv ≠ IV128) (a : SkAd) (k : Bytes 16)
    (ha : aty (sha2AdrsKey a.val) = .prf) : role cv aty (cv, blk128 a k) = .kseed a k := by
  have hb := btw_blk128 a k
  have hex : aty (btw128 (blk128 a k)) = .prf ∧ ∃ a' k', blk128 a k = blk128 a' k' :=
    ⟨(congrArg aty hb).trans ha, a, k, rfl⟩
  unfold role
  simp only [hcv, false_and, ite_false, ite_true]
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hs := Classical.choose_spec (Classical.choose_spec hex.2)
  obtain ⟨e1, e2⟩ := blk128_injective _ _ _ _ hs
  exact congrArg₂ Role.kseed e1.symm e2.symm

/-- The first block of a short call at a short tweak, in row `cv`, is `th1` of its tweak and
input. -/
theorem role_short (hcv : cv ≠ IV128) (A : Bytes 22) (xs : List (Bytes 16)) (hxs : ShortIn xs)
    (hA : aty A = .short) : role cv aty (cv, (tblocks A xs).1) = .th1 A xs := by
  have hb := btw128_tblocks A xs
  have hex : aty (btw128 (tblocks A xs).1) = .short ∧
      ∃ xs', ShortIn xs' ∧ (tblocks A xs).1 = (tblocks (btw128 (tblocks A xs).1) xs').1 :=
    ⟨(congrArg aty hb).trans hA, xs, hxs, congrArg (fun A' => (tblocks A' xs).1) hb.symm⟩
  have hnp : ¬ (aty (btw128 (tblocks A xs).1) = .prf ∧
      ∃ a k, (tblocks A xs).1 = blk128 a k) := by
    rintro ⟨h1, -⟩
    have h2 := ((congrArg aty hb).symm.trans h1).symm.trans hA
    exact absurd h2 (by decide)
  unfold role
  simp only [hcv, false_and, ite_false, ite_true]
  rw [dite_eq_right_of_eq_false (eq_false hnp), dite_eq_left_of_eq_true (eq_true hex)]
  have hs := Classical.choose_spec hex.2
  obtain ⟨e1, e2⟩ := blk_short_unique hs.1 hxs hs.2.symm
  exact congrArg₂ Role.th1 e1 e2

/-- A cell classified `th1 A xs` is the short block of `(A, xs)` in row `cv`. -/
theorem role_th1_iff (q : St × Blk) (A : Bytes 22) (xs : List (Bytes 16)) (hcv : cv ≠ IV128) :
    role cv aty q = .th1 A xs ↔
      q.1 = cv ∧ aty A = .short ∧ ShortIn xs ∧ q.2 = (tblocks A xs).1 := by
  constructor
  · intro h
    unfold role at h
    by_cases h1 : q.1 = IV128 ∧ ∃ k, q.2 = ikey k ∨ q.2 = okey k
    · rw [if_pos h1] at h; exact Role.noConfusion h
    rw [if_neg h1] at h
    by_cases h2 : q.1 = cv
    swap
    · rw [if_neg h2] at h; exact Role.noConfusion h
    rw [if_pos h2] at h
    by_cases h3 : aty (btw128 q.2) = .prf ∧ ∃ a k, q.2 = blk128 a k
    · rw [dif_pos h3] at h; exact Role.noConfusion h
    rw [dif_neg h3] at h
    by_cases h4 : aty (btw128 q.2) = .short ∧
        ∃ xs, ShortIn xs ∧ q.2 = (tblocks (btw128 q.2) xs).1
    · rw [dif_pos h4] at h
      injection h with e1 e2
      have hs := Classical.choose_spec h4.2
      rw [e2, e1] at hs
      exact ⟨h2, e1 ▸ h4.1, hs.1, hs.2⟩
    rw [dif_neg h4] at h
    by_cases h5 : aty (btw128 q.2) = .long
    · rw [if_pos h5] at h; exact Role.noConfusion h
    · rw [if_neg h5] at h; exact Role.noConfusion h
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨c, b⟩ := q
    simp only at h1 h4
    rw [h1, h4]
    exact role_short cv aty hcv A xs h3 h2

end Role

end Ideal.Direct

#print axioms Ideal.Direct.blk_short_unique
#print axioms Ideal.Direct.role_blk128
#print axioms Ideal.Direct.role_short
#print axioms Ideal.Direct.role_th1_iff
