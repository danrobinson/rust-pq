import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Util
import Mathlib.Data.Nat.Count
open Aeneas Aeneas.Std Result

/-! WOTS+. -/

namespace slhdsa

/-- `Vec::extend_from_slice` appends (bytes). -/
@[local step]
theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  step with List.clone_spec
  simp [*]

/-- `Vec::extend_from_slice` appends (words). -/
@[local step]
theorem extend_u32_spec (v : alloc.vec.Vec U32) (s : Slice U32)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU32 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  step with List.clone_spec
  simp [*]

theorem W_eq : params.W = 16#u32 := by with_unfolding_all rfl
theorem LEN1_eq : params.LEN1 = 32#usize := by with_unfolding_all rfl
theorem LEN2_eq : params.LEN2 = 3#usize := by with_unfolding_all rfl
theorem LEN_eq : params.LEN = 35#usize := by with_unfolding_all rfl
theorem LG_W_eq : params.LG_W = 4#u32 := by with_unfolding_all rfl

theorem wots_digits_loop_spec (msg : alloc.vec.Vec U32) (csum : U32) (i : Usize)
    (hlen : msg.length = 32) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (hi : i.val ≤ 32)
    (hinv : csum.val = ((nats msg.val).take i.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0)
    (hb : csum.val ≤ 15 * i.val) :
    wots.wots_digits_loop msg csum i ⦃ r =>
      r.val = (nats msg.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0 ∧ r.val ≤ 480 ⦄ := by
  unfold wots.wots_digits_loop
  apply loop.spec_decr_nat (measure := fun (p : U32 × Usize) => 32 - p.2.val)
    (inv := fun p => p.2.val ≤ 32 ∧
      p.1.val = ((nats msg.val).take p.2.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0 ∧
      p.1.val ≤ 15 * p.2.val)
  · rintro ⟨csum, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_digits_loop.body, W_eq, LEN1_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    spec_split
    · have hil : i.val < msg.val.length := by scalar_tac
      have hd : (msg.val[i.val]).val < 16 := hdig _ (List.getElem_mem hil)
      let* ⟨ i1, i1_post, i1_post1 ⟩ ← U32.sub_spec
      let* ⟨ i2, i2_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ i3, i3_post, i3_post1 ⟩ ← U32.sub_spec
      let* ⟨ csum1, csum1_post ⟩ ← U32.add_spec
      let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
      refine ⟨by scalar_tac, ?_, by scalar_tac, by scalar_tac⟩
      have hn : i.val < (nats msg.val).length := by simp [nats]; scalar_tac
      rw [i4_post, List.take_add_one, List.foldl_append, ← h2, List.getElem?_eq_getElem hn]
      simp [nats, Spec.w, csum1_post, i3_post, i1_post, i2_post]
    · simp only [step_simps]
      have hi32 : i.val = 32 := by scalar_tac
      have : List.take i.val (nats msg.val) = nats msg.val := by
        apply List.take_of_length_le; simp [nats]; scalar_tac
      rw [this] at h2
      exact ⟨h2, by scalar_tac⟩
  · exact ⟨hi, hinv, hb⟩

@[step]
theorem wots_digits_spec (m : Array U8 16#usize) :
    wots.wots_digits m ⦃ r =>
      nats r.val = Spec.wotsDigits (bytes m.val) ∧ r.length = 35 ∧ ∀ d ∈ r.val, d.val < 16 ⦄ := by
  unfold wots.wots_digits
  simp only [LG_W_eq, LEN1_eq, LEN2_eq]
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ msg, msg_post, msg_post1, msg_post2 ⟩ ← base_2b_spec
  let* ⟨ csum, csum_post, csum_le ⟩ ← wots_digits_loop_spec
  · simp
  let* ⟨ csum1, csum1_post, csum1_post1 ⟩ ← U32.ShiftLeft_IScalar_spec
  let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i1, i1_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ tail, tail_post, tail_post1, tail_post2 ⟩ ← base_2b_spec
  have hbytes : bytes s1.val = Spec.toByte (csum.val <<< 4) 2 := by
    simp [s1_post, Spec.toByte, List.range, List.range.loop, i1_post, i2_post]
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp [i_post1, csum1_post1, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp [csum1_post1, Nat.shiftLeft_eq]
  have hderef : tail.deref.val = tail.val := by simp [alloc.vec.Vec.deref]
  let* ⟨ r, r_post ⟩ ← extend_u32_spec
  rw [hderef] at r_post
  refine ⟨?_, ?_, ?_⟩
  · simp only [Spec.wotsDigits, r_post, nats, List.map_append]
    simp only [nats] at msg_post tail_post csum_post
    rw [msg_post, tail_post, hbytes, csum_post, msg_post, s_post]
    simp [Spec.lgw, Spec.len1, Spec.len2]
  · simp [r_post]; scalar_tac
  · intro d hd
    simp [r_post] at hd
    rcases hd with hd | hd
    · exact msg_post2 d hd
    · exact tail_post2 d hd

theorem WOTS_PRF_eq : address.WOTS_PRF = 5#u32 := by with_unfolding_all rfl
theorem WOTS_PK_eq : address.WOTS_PK = 1#u32 := by with_unfolding_all rfl

theorem adrsS_sk (adrs a sk_adrs : address.Adrs)
    (ha : a = ⟨adrs.layer, adrs.tree, address.WOTS_PRF, 0#u32, 0#u32, 0#u32⟩)
    (hs : sk_adrs = ⟨a.layer, a.tree, a.typ, adrs.keypair, a.word2, a.word3⟩) :
    adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs) := by
  subst ha; subst hs
  simp [adrsS, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear, Spec.WOTS_PRF, WOTS_PRF_eq]

theorem adrsS_pk (adrs a pk_adrs : address.Adrs)
    (ha : a = ⟨adrs.layer, adrs.tree, address.WOTS_PK, 0#u32, 0#u32, 0#u32⟩)
    (hs : pk_adrs = ⟨a.layer, a.tree, a.typ, adrs.keypair, a.word2, a.word3⟩) :
    adrsS pk_adrs = Spec.wotsPkAdrs (adrsS adrs) := by
  subst ha; subst hs
  simp [adrsS, Spec.wotsPkAdrs, Spec.Adrs.setTypeAndClear, Spec.WOTS_PK, WOTS_PK_eq]

/-! The secret values. -/

theorem forall_set_succ {α} [Inhabited α] (l : List α) (i : Nat) (x : α) (P : Nat → α → Prop)
    (hl : i < l.length) (h : ∀ j, j < i → P j l[j]!) (hx : P i x) :
    ∀ j, j < i + 1 → P j (l.set i x)[j]! := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · rw [getElem!_set_ne' _ _ _ _ (by omega)]; exact h j hj
  · subst hj; rw [getElem!_set_self' _ _ _ hl]; exact hx

theorem cast_u32_val (i : Usize) (h : i.val < 35) : (UScalar.cast .U32 i).val = i.val := by
  simp; scalar_tac

theorem wots_sks_loop0_spec (sk_seed : Array U8 16#usize) (sk_adrs : address.Adrs)
    (blocks : Array (Array U8 64#usize) 35#usize) (i : Usize) (hi : i.val ≤ 35)
    (hinv : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val)) :
    wots.wots_sks_loop0 sk_seed sk_adrs blocks i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val =
        padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val) ⦄ := by
  unfold wots.wots_sks_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ ∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
  · rintro ⟨blocks, i⟩ ⟨h1, h2⟩
    simp only [wots.wots_sks_loop0.body, LEN_eq]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i2_post, a2_post, Array.set_val_eq]
    refine forall_set_succ blocks.val i.val a1 (fun j (b : Array U8 64#usize) => bytes b.val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
      (by simp; scalar_tac) h2 ?_
    rw [a1_post, s_post, a_post, i1_post]
    simp only [adrsS, Array.val_to_slice, cast_u32_val i (by scalar_tac)]
  · exact ⟨hi, hinv⟩

theorem wots_sks_loop1_spec (st : Array (Array U32 8#usize) 35#usize)
    (sk : Array (Array U8 16#usize) 35#usize) (i : Usize) (hi : i.val ≤ 35)
    (hinv : ∀ j, j < i.val → bytes (sk.val[j]!).val = (ser (wv (st.val[j]!).val)).take 16) :
    wots.wots_sks_loop1 st sk i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val = (ser (wv (st.val[j]!).val)).take 16 ⦄ := by
  unfold wots.wots_sks_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧
      ∀ j, j < p.2.val → bytes (p.1.val[j]!).val = (ser (wv (st.val[j]!).val)).take 16)
  · rintro ⟨sk, i⟩ ⟨h1, h2⟩
    simp only [wots.wots_sks_loop1.body, LEN_eq]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i1_post, a2_post, Array.set_val_eq]
    refine forall_set_succ sk.val i.val a1
      (fun j (b : Array U8 16#usize) => bytes b.val = (ser (wv (st.val[j]!).val)).take 16)
      (by simp; scalar_tac) h2 ?_
    simp only [a1_post, a_post, getElem!_eq _ _ (show i.val < st.val.length by simp; scalar_tac)]
  · exact ⟨hi, hinv⟩

@[step]
theorem wots_sks_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (sk_adrs : address.Adrs) :
    wots.wots_sks sk pk sk_adrs ⦃ r =>
      ∀ i, i < 35 → bytes (r.val[i]!).val =
        Spec.PRF (bytes pk.pk_seed.val) (bytes sk.val) { adrsS sk_adrs with word2 := i } ⦄ := by
  unfold wots.wots_sks
  let* ⟨ blocks1, blocks1_post ⟩ ← wots_sks_loop0_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, to_slice_mut_back, s1_post, to_slice_mut_back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s2, s2_len, s2_post ⟩ ← compress_many_spec
  let* ⟨ r, r_post ⟩ ← wots_sks_loop1_spec
  rename_i j hj
  have hst : (to_slice_mut_back s2).val = s2.val := by
    rw [to_slice_mut_back_post]
    exact Array.from_slice_val _ _ (by simp [s2_len, s1_post])
  have hsl : s.length = 35 := by simp [s_post]
  have hc := s2_post j (by omega)
  have hsj : s.val[j]! = blocks1.val[j]! := by rw [s_post, Array.val_to_slice]
  rw [hsj] at hc
  have hw := compress_ok_wv _ _ _ hc
  exact thash_short_parts pk hpk _ _ _ _ _ (blocks1_post j hj) hw (by rw [r_post j hj, hst])

/-! Concatenating the chain values. -/

theorem concat_loop_spec (x : Array (Array U8 16#usize) 35#usize) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ 35) (hlen : out.length = 16 * i.val)
    (hinv : bytes out.val = (List.range i.val).flatMap (fun j => bytes (x.val[j]!).val)) :
    wots.concat_loop x out i ⦃ r =>
      bytes r.val = (List.range 35).flatMap (fun j => bytes (x.val[j]!).val) ∧
      r.length = 560 ⦄ := by
  unfold wots.concat_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap (fun j => bytes (x.val[j]!).val))
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.concat_loop.body, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    spec_split
    · let* ⟨ a, a_post ⟩ ← Array.index_usize_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ out1, out1_post ⟩ ← extend_u8_spec
      let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
      refine ⟨by scalar_tac, by simp [out1_post, s_post]; scalar_tac, ?_, by scalar_tac⟩
      rw [i1_post, List.range_succ, List.flatMap_append, ← h3, out1_post]
      simp [s_post, a_post, List.getElem?_eq_getElem (show i.val < x.val.length by simp; scalar_tac)]
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, by scalar_tac⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem concat_spec (x : Array (Array U8 16#usize) 35#usize) :
    wots.concat x ⦃ r =>
      bytes r.val = (List.range 35).flatMap (fun j => bytes (x.val[j]!).val) ∧
      r.length = 560 ⦄ := by
  unfold wots.concat
  apply concat_loop_spec <;> simp

/-! All chains in lockstep. -/

/-- Lane `i` takes step `t` of its chain. -/
def Active (start «end» : Slice U32) (t i : Nat) : Prop :=
  (start.val[i]!).val ≤ t ∧ t < («end».val[i]!).val

instance (start «end» : Slice U32) (t : Nat) : DecidablePred (Active start «end» t) :=
  fun i => by unfold Active; infer_instance

/-- The block of lane `j` for step `t`. -/
def LaneBlock (a : address.Adrs) (cur : Array (Array U8 16#usize) 35#usize) (t j : Nat)
    (b : Array U8 64#usize) : Prop :=
  bytes b.val = padFrom 64 ({ adrsS a with word2 := j, word3 := t }.compress ++ bytes (cur.val[j]!).val)

theorem pack_active {α} [Inhabited α] (P : Nat → Prop) [DecidablePred P] (Q : Nat → α → Prop)
    (l : List α) (hl : l.length = 35) (i : Nat) (x : α) (hi : i < 35) (hp : P i)
    (h : ∀ j, j < i → P j → Q j l[Nat.count P j]!) (hx : Q i x) :
    ∀ j, j < i + 1 → P j → Q j (l.set (Nat.count P i) x)[Nat.count P j]! := by
  have hc : Nat.count P i < l.length := by
    have := Nat.count_le (p := P) (n := i); omega
  intro j hj hpj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · have := Nat.count_strict_mono hpj hj
    rw [getElem!_set_ne' _ _ _ _ (by omega)]; exact h j hj hpj
  · subst hj; rw [getElem!_set_self' _ _ _ hc]; exact hx

theorem pack_inactive {α} [Inhabited α] (P : Nat → Prop) [DecidablePred P] (Q : Nat → α → Prop)
    (l : List α) (i : Nat) (hp : ¬ P i)
    (h : ∀ j, j < i → P j → Q j l[Nat.count P j]!) :
    ∀ j, j < i + 1 → P j → Q j l[Nat.count P j]! := by
  intro j hj hpj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · exact h j hj hpj
  · subst hj; exact absurd hpj hp

theorem active_iff (start «end» : Slice U32) (t : U32) (i : Usize) (hs : i.val < start.length)
    (he : i.val < «end».length) :
    Active start «end» t.val i.val ↔
      (start.val[i.val]'hs).val ≤ t.val ∧ t.val < («end».val[i.val]'he).val := by
  simp only [Active, getElem!_eq _ _ hs, getElem!_eq _ _ he]

theorem chains_loop0_loop0_spec (cur : Array (Array U8 16#usize) 35#usize) (start «end» : Slice U32)
    (a : address.Adrs) (blocks : Array (Array U8 64#usize) 35#usize) (t : U32) (k i : Usize)
    (hs : start.length = 35) (he : «end».length = 35)
    (hi : i.val ≤ 35) (hk : k.val = Nat.count (Active start «end» t.val) i.val)
    (hinv : ∀ j, j < i.val → Active start «end» t.val j →
      LaneBlock a cur t.val j (blocks.val[Nat.count (Active start «end» t.val) j]!)) :
    wots.chains_loop0_loop0 cur start «end» a blocks t k i ⦃ r =>
      r.2.val = Nat.count (Active start «end» t.val) 35 ∧
      ∀ j, j < 35 → Active start «end» t.val j →
        LaneBlock a cur t.val j (r.1.val[Nat.count (Active start «end» t.val) j]!) ⦄ := by
  unfold wots.chains_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 35#usize × Usize × Usize) => 35 - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ 35 ∧ p.2.1.val = Nat.count (Active start «end» t.val) p.2.2.val ∧
      ∀ j, j < p.2.2.val → Active start «end» t.val j →
        LaneBlock a cur t.val j (p.1.val[Nat.count (Active start «end» t.val) j]!))
  · rintro ⟨blocks, k, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.chains_loop0_loop0.body, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    spec_split
    · have hk35 : k.val < 35 := by
        have := Nat.count_le (p := Active start «end» t.val) (n := i.val)
        scalar_tac
      let* ⟨ i1, i1_post ⟩ ← Slice.index_usize_spec
      split
      · rename_i hst
        let* ⟨ i2, i2_post ⟩ ← Slice.index_usize_spec
        split
        · rename_i hte
          let* ⟨ i3, i3_post ⟩ ← UScalar.cast.step_spec
          let* ⟨ a', a'_post ⟩ ← with_word2_spec
          let* ⟨ a1, a1_post ⟩ ← with_word3_spec
          let* ⟨ a2, a2_post ⟩ ← Array.index_usize_spec
          let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
          let* ⟨ a3, a3_post ⟩ ← short_block_spec
          let* ⟨ a4, a4_post ⟩ ← Array.update_spec
          let* ⟨ k2, k2_post ⟩ ← Usize.add_spec
          let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
          have hact : Active start «end» t.val i.val :=
            (active_iff start «end» t i (by scalar_tac) (by scalar_tac)).mpr
              ⟨by rw [← i1_post]; scalar_tac, by rw [← i2_post]; scalar_tac⟩
          refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
          · rw [i4_post, Nat.count_succ, k2_post, h2]; simp [hact]
          · rw [i4_post, a4_post, Array.set_val_eq, h2]
            refine pack_active _ (LaneBlock a cur t.val) blocks.val (by simp) i.val a3
              (by scalar_tac) hact h3 ?_
            have hil : i.val < cur.val.length := by simp; scalar_tac
            simp only [LaneBlock, a3_post, s_post, a2_post, Array.val_to_slice,
              getElem!_eq _ _ hil, a1_post, a'_post, i3_post, adrsS, cast_u32_val i (by scalar_tac)]
        · rename_i hte
          have hact : ¬ Active start «end» t.val i.val := by
            rw [active_iff start «end» t i (by scalar_tac) (by scalar_tac)]
            rintro ⟨-, h⟩
            exact hte (by rw [i2_post]; scalar_tac)
          step*
          refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
          · rw [i2_post, Nat.count_succ, h2]; simp [hact]
          · rw [i2_post]; exact pack_inactive _ _ _ _ hact h3
      · rename_i hst
        have hact : ¬ Active start «end» t.val i.val := by
          rw [active_iff start «end» t i (by scalar_tac) (by scalar_tac)]
          rintro ⟨h, -⟩
          exact hst (by rw [i1_post]; scalar_tac)
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, Nat.count_succ, h2]; simp [hact]
        · rw [i2_post]; exact pack_inactive _ _ _ _ hact h3
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h2 h3
      exact ⟨h2, h3⟩
  · exact ⟨hi, hk, hinv⟩

/-- Lane `j` after step `t`: the truncated state of its rank if it took the
step, its old value otherwise. -/
def LaneOut (start «end» : Slice U32) (t : Nat) (cur0 : Array (Array U8 16#usize) 35#usize)
    (st : Array (Array U32 8#usize) 35#usize) (j : Nat) (b : Array U8 16#usize) : Prop :=
  (Active start «end» t j →
    bytes b.val = (ser (wv (st.val[Nat.count (Active start «end» t) j]!).val)).take 16) ∧
  (¬ Active start «end» t j → b = cur0.val[j]!)

theorem chains_loop0_loop1_spec (cur0 : Array (Array U8 16#usize) 35#usize) (start «end» : Slice U32)
    (st : Array (Array U32 8#usize) 35#usize) (t : U32)
    (cur : Array (Array U8 16#usize) 35#usize) (k i : Usize)
    (hs : start.length = 35) (he : «end».length = 35)
    (hi : i.val ≤ 35) (hk : k.val = Nat.count (Active start «end» t.val) i.val)
    (hdone : ∀ j, j < i.val → LaneOut start «end» t.val cur0 st j (cur.val[j]!))
    (hrest : ∀ j, i.val ≤ j → cur.val[j]! = cur0.val[j]!) :
    wots.chains_loop0_loop1 cur start «end» st t k i ⦃ r =>
      ∀ j, j < 35 → LaneOut start «end» t.val cur0 st j (r.val[j]!) ⦄ := by
  unfold wots.chains_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 35#usize × Usize × Usize) => 35 - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ 35 ∧ p.2.1.val = Nat.count (Active start «end» t.val) p.2.2.val ∧
      (∀ j, j < p.2.2.val → LaneOut start «end» t.val cur0 st j (p.1.val[j]!)) ∧
      (∀ j, p.2.2.val ≤ j → p.1.val[j]! = cur0.val[j]!))
  · rintro ⟨cur, k, i⟩ ⟨h1, h2, h3, h4⟩
    simp only [wots.chains_loop0_loop1.body, LEN_eq]
    simp only at h1 h2 h3 h4
    simp only [step_simps]
    spec_split
    · have hk35 : k.val < 35 := by
        have := Nat.count_le (p := Active start «end» t.val) (n := i.val)
        scalar_tac
      let* ⟨ i1, i1_post ⟩ ← Slice.index_usize_spec
      split
      · rename_i hst
        let* ⟨ i2, i2_post ⟩ ← Slice.index_usize_spec
        split
        · rename_i hte
          let* ⟨ a, a_post ⟩ ← Array.index_usize_spec
          let* ⟨ a1, a1_post ⟩ ← trunc_spec
          let* ⟨ a2, a2_post ⟩ ← Array.update_spec
          let* ⟨ k2, k2_post ⟩ ← Usize.add_spec
          let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
          have hact : Active start «end» t.val i.val :=
            (active_iff start «end» t i (by scalar_tac) (by scalar_tac)).mpr
              ⟨by rw [← i1_post]; scalar_tac, by rw [← i2_post]; scalar_tac⟩
          have hil : i.val < cur.val.length := by simp; scalar_tac
          refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
          · rw [i3_post, Nat.count_succ, k2_post, h2]; simp [hact]
          · rw [i3_post, a2_post, Array.set_val_eq]
            refine forall_set_succ cur.val i.val a1 (LaneOut start «end» t.val cur0 st) hil h3 ?_
            refine ⟨fun _ => ?_, fun h => absurd hact h⟩
            have hkl : k.val < st.val.length := by simp; scalar_tac
            rw [a1_post, a_post, ← getElem!_eq _ _ hkl, h2]
          · intro j hj
            rw [a2_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
            exact h4 j (by scalar_tac)
        · rename_i hte
          have hact : ¬ Active start «end» t.val i.val := by
            rw [active_iff start «end» t i (by scalar_tac) (by scalar_tac)]
            rintro ⟨-, h⟩
            exact hte (by rw [i2_post]; scalar_tac)
          step*
          refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
          · rw [i2_post, Nat.count_succ, h2]; simp [hact]
          · rw [i2_post]
            intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · exact h3 j hj
            · subst hj; exact ⟨fun h => absurd h hact, fun _ => h4 _ (le_refl _)⟩
          · intro j hj; exact h4 j (by scalar_tac)
      · rename_i hst
        have hact : ¬ Active start «end» t.val i.val := by
          rw [active_iff start «end» t i (by scalar_tac) (by scalar_tac)]
          rintro ⟨h, -⟩
          exact hst (by rw [i1_post]; scalar_tac)
        step*
        refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, Nat.count_succ, h2]; simp [hact]
        · rw [i2_post]
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact h3 j hj
          · subst hj; exact ⟨fun h => absurd h hact, fun _ => h4 _ (le_refl _)⟩
        · intro j hj; exact h4 j (by scalar_tac)
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h3
      exact h3
  · exact ⟨hi, hk, hdone, hrest⟩

theorem chain_step_active (x pk : Spec.Bytes) (A : Spec.Adrs) (j s e t : Nat)
    (h : s ≤ t ∧ t < e) :
    Spec.thash pk { A with word2 := j, word3 := t }
        (Spec.chain x s (min t e - s) pk { A with word2 := j }) =
      Spec.chain x s (min (t + 1) e - s) pk { A with word2 := j } := by
  have h1 : min (t + 1) e - s = (min t e - s) + 1 := by omega
  have h2 : s + (min t e - s) = t := by omega
  rw [h1]
  simp only [Spec.chain, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, h2,
    Spec.F]

theorem chain_step_inactive (x pk : Spec.Bytes) (A : Spec.Adrs) (s e t : Nat)
    (h : ¬ (s ≤ t ∧ t < e)) :
    Spec.chain x s (min t e - s) pk A = Spec.chain x s (min (t + 1) e - s) pk A := by
  have : min (t + 1) e - s = min t e - s := by omega
  rw [this]

theorem slice0_getElem! {α} [Inhabited α] (l : List α) (k c : Nat) (h : c < k) :
    (List.slice 0 k l)[c]! = l[c]! := by
  simp [List.slice, List.getElem!_eq_getElem?_getD, h]

/-- Lane `i` after `t` steps of `chains`. -/
def ChainAt (start «end» : Slice U32) (pk : Spec.Bytes) (A : Spec.Adrs)
    (cur0 : Array (Array U8 16#usize) 35#usize) (t i : Nat) (b : Array U8 16#usize) : Prop :=
  bytes b.val = Spec.chain (bytes (cur0.val[i]!).val) (start.val[i]!).val
    (min t («end».val[i]!).val - (start.val[i]!).val) pk { A with word2 := i }

theorem chains_loop0_spec (cur0 : Array (Array U8 16#usize) 35#usize) (start «end» : Slice U32)
    (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (hs : start.length = 35) (he : «end».length = 35)
    (hend : ∀ i, i < 35 → («end».val[i]!).val ≤ 15)
    (cur : Array (Array U8 16#usize) 35#usize) (blocks : Array (Array U8 64#usize) 35#usize)
    (st : Array (Array U32 8#usize) 35#usize) (t : U32) (ht : t.val ≤ 15)
    (hinv : ∀ i, i < 35 →
      ChainAt start «end» (bytes pk.pk_seed.val) (adrsS a) cur0 t.val i (cur.val[i]!)) :
    wots.chains_loop0 cur start «end» pk a blocks st t ⦃ r =>
      ∀ i, i < 35 → bytes (r.val[i]!).val =
        Spec.chain (bytes (cur0.val[i]!).val) (start.val[i]!).val
          ((«end».val[i]!).val - (start.val[i]!).val) (bytes pk.pk_seed.val)
          { adrsS a with word2 := i } ⦄ := by
  unfold wots.chains_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 35#usize × Array (Array U8 64#usize) 35#usize ×
      Array (Array U32 8#usize) 35#usize × U32) => 15 - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ 15 ∧ ∀ i, i < 35 →
      ChainAt start «end» (bytes pk.pk_seed.val) (adrsS a) cur0 p.2.2.2.val i (p.1.val[i]!))
  · rintro ⟨cur, blocks, st, t⟩ ⟨h1, h2⟩
    simp only [wots.chains_loop0.body, W_eq]
    simp only at h1 h2
    simp only [step_simps]
    let* ⟨ i, i_post, i_post1 ⟩ ← U32.sub_spec
    spec_split
    · let* ⟨ blocks1, k, hk, hb ⟩ ← chains_loop0_loop0_spec cur start «end» a blocks t 0#usize 0#usize
        hs he (by simp) (by simp) (by simp)
      have hk35 : k.val ≤ 35 := by
        have := Nat.count_le (p := Active start «end» t.val) (n := 35)
        omega
      let* ⟨ s, s_post, s_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      let* ⟨ s1, back, s1_post, back_post ⟩ ← Array.to_slice_mut_spec
      let* ⟨ s2, s2_len, s2_post ⟩ ← compress_many_spec
      let* ⟨ cur1, cur1_post ⟩ ← chains_loop0_loop1_spec cur start «end» (back s2) t cur
        0#usize 0#usize hs he (by simp) (by simp) (by simp) (by simp)
      let* ⟨ t1, t1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      have hst : (back s2).val = s2.val := by
        rw [back_post]; exact Array.from_slice_val _ _ (by simp [s2_len, s1_post])
      obtain ⟨hon, hoff⟩ := cur1_post j hj
      have hcj := h2 j hj
      simp only [ChainAt] at hcj ⊢
      rw [t1_post]
      by_cases hact : Active start «end» t.val j
      · have hlt : Nat.count (Active start «end» t.val) j < k.val := by
          rw [hk]; exact Nat.count_strict_mono hact hj
        have hc := s2_post _ (by rw [s_len]; omega)
        rw [s_post, Array.val_to_slice, slice0_getElem! _ _ _ hlt] at hc
        have hw := compress_ok_wv _ _ _ hc
        rw [← hst] at hw
        have hF := thash_short_parts pk hpk _ _ _ _ _ (hb j hj hact) hw (hon hact)
        rw [hF, hcj]
        exact chain_step_active _ _ _ _ _ _ _ hact
      · rw [hoff hact, hcj]
        exact chain_step_inactive _ _ _ _ _ _ hact
    · simp only [step_simps]
      have ht15 : t.val = 15 := by scalar_tac
      intro j hj
      have := h2 j hj
      simp only [ChainAt, ht15] at this
      rw [this, Nat.min_eq_right (hend j hj)]
  · exact ⟨ht, hinv⟩

@[step]
theorem chains_spec (cur : Array (Array U8 16#usize) 35#usize) (start «end» : Slice U32)
    (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (hs : start.length = 35) (he : «end».length = 35)
    (hend : ∀ i, i < 35 → («end».val[i]!).val ≤ 15) :
    wots.chains cur start «end» pk a ⦃ r =>
      ∀ i, i < 35 → bytes (r.val[i]!).val =
        Spec.chain (bytes (cur.val[i]!).val) (start.val[i]!).val
          ((«end».val[i]!).val - (start.val[i]!).val) (bytes pk.pk_seed.val)
          { adrsS a with word2 := i } ⦄ := by
  unfold wots.chains
  apply chains_loop0_spec cur start «end» pk hpk a hs he hend _ _ _ 0#u32 (by simp)
  intro i hi
  simp [ChainAt, Spec.chain]

/-! The three WOTS+ algorithms. -/

theorem repeat_getElem! {α} [Inhabited α] (x : α) (j : Nat) (hj : j < 35) :
    ((Array.repeat 35#usize x).to_slice.val)[j]! = x := by
  rw [Array.val_to_slice, Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  simp [hj]

theorem flatMap_lanes (x : Array (Array U8 16#usize) 35#usize) (f : Nat → Spec.Bytes)
    (h : ∀ i, i < 35 → bytes (x.val[i]!).val = f i) :
    (List.range 35).flatMap (fun j => bytes (x.val[j]!).val) = (List.range 35).flatMap f :=
  List.flatMap_congr (fun i hi => h i (List.mem_range.mp hi))

/-- Chain `i` of `wots_pkGen` in the specification. -/
def pkGenStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 (Spec.w - 1) pk
    { a with word2 := i }

@[step]
theorem wots_pk_gen_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) :
    wots.wots_pk_gen sk pk a ⦃ r =>
      bytes r.val = Spec.wotsPkGen (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_gen
  simp only [step_simps, W_eq]
  step*
  case hend =>
    have hi15 : i = 15#u32 := by rw [i_post]; decide
    intro j hj
    rw [s1_post, repeat_getElem! _ _ hj, hi15]; decide
  have hsk := adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  have hi15 : i = 15#u32 := by rw [i_post]; decide
  have ht : bytes v.deref.val = bytes v.val := by simp [alloc.vec.Vec.deref]
  rw [r_post, adrsS_pk adrs a3 pk_adrs a3_post1 pk_adrs_post, ht, v_post,
    flatMap_lanes cur1 (pkGenStep (bytes sk.val) (bytes pk.pk_seed.val) (adrsS adrs))]
  · rfl
  · intro j hj
    rw [cur1_post j hj, cur_post j hj, hsk, s_post, s1_post, repeat_getElem! _ _ hj,
      repeat_getElem! _ _ hj, hi15]
    rfl

theorem nats_getElem! (l : List U32) (j : Nat) (h : j < l.length) : (nats l)[j]! = (l[j]!).val := by
  simp [nats, h]

theorem digit_le (msg : alloc.vec.Vec U32) (hlen : msg.length = 35) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (j : Nat) (hj : j < 35) : ((alloc.vec.Vec.deref msg).val[j]!).val ≤ 15 := by
  have hj' : j < msg.val.length := by scalar_tac
  have := hdig _ (List.getElem_mem hj')
  rw [vec_deref_val, getElem!_eq _ _ hj']
  omega

/-- Chain `i` of `wots_sign` in the specification. -/
def signStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 digits[i]! pk
    { a with word2 := i }

@[step]
theorem wots_sign_spec (m sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) :
    wots.wots_sign m sk pk a ⦃ r =>
      bytes r.val = Spec.wotsSign (bytes m.val) (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ∧
      r.length = 560 ⦄ := by
  rename' a => adrs
  unfold wots.wots_sign
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  step*
  case hend => exact digit_le msg msg_len msg_dig
  have hsk := adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  refine ⟨?_, by assumption⟩
  rw [r_post, flatMap_lanes cur1
    (signStep (bytes sk.val) (bytes pk.pk_seed.val) (adrsS adrs) (nats msg.val)), msg_post]
  · rfl
  · intro j hj
    rw [cur1_post j hj, cur_post j hj, hsk, s_post, repeat_getElem! _ _ hj, vec_deref_val,
      signStep, nats_getElem! msg.val j (by scalar_tac)]
    rfl

/-- Chain `i` of `wots_pkFromSig` in the specification. -/
def fromSigStep (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.block sig i) digits[i]! (Spec.w - 1 - digits[i]!) pk { a with word2 := i }

theorem wots_pk_from_sig_loop_spec (sig : Slice U8) (cur : Array (Array U8 16#usize) 35#usize)
    (i : Usize) (hsig : 560 ≤ sig.length) (hi : i.val ≤ 35)
    (hinv : ∀ j, j < i.val → bytes (cur.val[j]!).val = Spec.block (bytes sig.val) j) :
    wots.wots_pk_from_sig_loop sig cur i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val = Spec.block (bytes sig.val) j ⦄ := by
  unfold wots.wots_pk_from_sig_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 16#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧
      ∀ j, j < p.2.val → bytes (p.1.val[j]!).val = Spec.block (bytes sig.val) j)
  · rintro ⟨cur, i⟩ ⟨h1, h2⟩
    simp only [wots.wots_pk_from_sig_loop.body, LEN_eq]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i1_post, a1_post, Array.set_val_eq]
    exact forall_set_succ cur.val i.val a
      (fun j (b : Array U8 16#usize) => bytes b.val = Spec.block (bytes sig.val) j)
      (by simp; scalar_tac) h2 a_post1
  · exact ⟨hi, hinv⟩

@[step]
theorem wots_pk_from_sig_spec (sig : Slice U8) (m : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : 560 ≤ sig.length) :
    wots.wots_pk_from_sig sig m pk a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (bytes sig.val) (bytes m.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_from_sig
  simp only [step_simps, W_eq]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ cur1, cur1_post ⟩ ← wots_pk_from_sig_loop_spec
  step*
  case hend =>
    have hi15 : i = 15#u32 := by rw [i_post]; decide
    intro j hj
    rw [s1_post, repeat_getElem! _ _ hj, hi15]; decide
  have hi15 : i = 15#u32 := by rw [i_post]; decide
  have ht : bytes v.deref.val = bytes v.val := by simp [alloc.vec.Vec.deref]
  rw [r_post, adrsS_pk adrs a2 pk_adrs a2_post1 pk_adrs_post, ht, v_post,
    flatMap_lanes cur2 (fromSigStep (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) (nats msg.val)),
    msg_post]
  · rfl
  · intro j hj
    rw [cur2_post j hj, cur1_post j hj, s1_post, repeat_getElem! _ _ hj, vec_deref_val,
      fromSigStep, nats_getElem! msg.val j (by scalar_tac), hi15]
    rfl

end slhdsa
