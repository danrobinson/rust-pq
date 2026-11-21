import Ideal.Games.MsgPrf
import Ideal.Sha.HmacShape
import Ideal.Inst.WotsPre128
import Reduction.Basic

/-!
# `PRF_msg` as a PRF at SLH-DSA-SHA2-128s, ideal-compression model

`PRF_msg(SK.prf, opt_rand, M) = Trunc_16(HMAC-SHA-256(SK.prf, opt_rand ‖ M))` over a compression
table `g` is the HMAC-shaped keyed function of `Ideal/Games/MsgPrfDefs.lean`
(`msgPrf_shape`, `msgPrf_eq`):

`PRF_msg_g(k, (r, M)) = out16 (g (g (IV128, okey k), oblock (mdFold g (g (IV128, ikey k)) (iblocks r M))))`.

`msgPrf_bound_128s`: for a distinguisher making at most `q` compression queries and `qO`
`PRF_msg`-oracle queries on messages of at most `mlen` bytes, with `g` a uniformly random table,

`msgRealI A ≤ msgIdealI A + ε` and `msgIdealI A ≤ msgRealI A + ε`,
`ε = 2 q / 2^128 + (q + qO ((mlen + 24) / 64 + 1) + 2)² / 2^256`

(`(mlen + 24) / 64 + 1` bounds the number of SHA-256 blocks of `opt_rand ‖ M ‖ pad`, i.e. the
number of compression calls of the inner hash after its key block).
-/

open OracleComp OracleSpec ENNReal PRFScheme SLHDSA SLHDSA.Concrete

namespace Ideal

/-- The inner blocks after the key block, as first block and remaining blocks. -/
def ib128 (d : Bytes 16 × List Byte) : Blk × List Blk :=
  ((iblocks d.1 d.2).headD (Vector.replicate 64 0), (iblocks d.1 d.2).tail)

theorem iblocks_eq_cons (d : Bytes 16 × List Byte) :
    iblocks d.1 d.2 = (ib128 d).1 :: (ib128 d).2 := by
  have h := iblocks_ne_nil d.1 d.2
  unfold ib128
  cases hb : iblocks d.1 d.2 with
  | nil => exact absurd hb h
  | cons b bs => rfl

theorem ib128_injective : Function.Injective ib128 := by
  intro d d' h
  have h1 : iblocks d.1 d.2 = iblocks d'.1 d'.2 := by
    rw [iblocks_eq_cons, iblocks_eq_cons, h]
  obtain ⟨h2, h3⟩ := iblocks_injective h1
  exact Prod.ext h2 h3

/-- Number of inner blocks after the first one. -/
theorem ib128_snd_length (d : Bytes 16 × List Byte) :
    (ib128 d).2.length = (d.2.length + 24) / 64 := by
  have h := iblocks_length d.1 d.2
  rw [iblocks_eq_cons] at h
  simpa using h

/-! ## The Reduction's scheme is the generic scheme -/

/-- `PRF_msg` of the 128s bundle over `g` is the HMAC-shaped keyed function. -/
theorem PRFmsg_128s_eq (g : CF St Blk) (k r : Bytes 16) (M : List Byte) :
    (primsG (liftC g)).PRFmsg k r M = macF IV128 ikey okey ib128 oblock out16 g k (r, M) := by
  rw [msgPrf_shape, iblocks_eq_cons (r, M)]
  rfl

/-- **`Reduction.msgPrf` at the 128s bundle over `g` is the generic scheme `⟨$ᵗ K, mac_g⟩`.** -/
theorem msgPrf_eq (g : CF St Blk) :
    Reduction.msgPrf Link.vp (primsG (liftC g)) = macSchemeI IV128 ikey okey ib128 oblock out16 g := by
  unfold Reduction.msgPrf SLHDSA.msgPrfScheme macSchemeI
  congr 1
  funext k d
  exact PRFmsg_128s_eq g k d.1 d.2

/-! ## The two probabilities and the bound -/

/-- Ideal-model distinguishers for `PRF_msg`: uniform sampling, compression queries, and the
candidate function on inputs `(opt_rand, M)`. -/
abbrev MsgPrfAdvI : Type := PrfAdvI St Blk (Bytes 16) (List Byte) (Bytes 16)

/-- `Pr[A outputs 1]` in the real world of the Reduction's `PRF_msg` game at the 128s bundle
over a uniformly random compression table `g` (the adversary's compression queries answered by
`g`), i.e. `𝒟[do let g ← $ᵗ (CF St Blk);
(Reduction.msgPrf Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g)] {true}`. -/
noncomputable def msgRealI (A : MsgPrfAdvI) : ℝ≥0∞ :=
  cfAdvantage fun g => (Reduction.msgPrf Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g)

/-- `Pr[A outputs 1]` in the ideal world (lazily sampled random function on
`Bytes 16 × List Byte`), the adversary's compression queries answered by a uniformly random
table, i.e. `𝒟[do let g ← $ᵗ (CF St Blk); prfIdealExperiment (A.inst g)] {true}`. -/
noncomputable def msgIdealI (A : MsgPrfAdvI) : ℝ≥0∞ :=
  cfAdvantage fun g => prfIdealExperiment (A.inst g)

/-- `cfAdvantage` of the real experiment of the generic scheme is `prT` of the real game. -/
theorem cfAdvantage_macReal {St Blk K P M Y : Type} [SampleableType K]
    [SampleableType (CF St Blk)] [SampleableType Y] [DecidableEq P] [DecidableEq M] (IV : St)
    (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (A : PrfAdvI St Blk P M Y) :
    (cfAdvantage fun g => prfRealExperiment (macSchemeI IV ik ok ib ob out g) (A.inst g)) =
      HP.prT (macRealGameI IV ik ok ib ob out A) := by
  rw [HP.prT_eq]
  rfl

/-- `cfAdvantage` of the ideal experiment is `prT` of the ideal game. -/
theorem cfAdvantage_prfIdeal {St Blk P M Y : Type} [SampleableType (CF St Blk)]
    [SampleableType Y] [DecidableEq P] [DecidableEq M] (A : PrfAdvI St Blk P M Y) :
    (cfAdvantage fun g => prfIdealExperiment (A.inst g)) = HP.prT (prfIdealGameI A) := by
  rw [HP.prT_eq]
  rfl

theorem msgRealI_eq (A : MsgPrfAdvI) :
    msgRealI A = HP.prT (macRealGameI IV128 ikey okey ib128 oblock out16 A) := by
  rw [← cfAdvantage_macReal]
  unfold msgRealI
  refine congrArg cfAdvantage (funext fun g => ?_)
  exact congrArg (fun s : PRFScheme (Bytes 16) (Bytes 16 × List Byte) (Bytes 16) =>
    s.prfRealExperiment (A.inst g)) (msgPrf_eq g)

theorem msgIdealI_eq (A : MsgPrfAdvI) : msgIdealI A = HP.prT (prfIdealGameI A) :=
  cfAdvantage_prfIdeal A

/-- `msgIdealI` with the ideal experiment typed at the carriers (and their instances) of the
128s bundle over `g`, as in `Reduction.msgIdealPr (prims := primsG (liftC g))`. -/
theorem msgIdealI_prims (A : MsgPrfAdvI) :
    msgIdealI A = cfAdvantage fun g =>
      prfIdealExperiment (D := (primsG (liftC g)).Y × List Byte) (R := (primsG (liftC g)).Y)
        (A.inst g) := by
  unfold msgIdealI
  refine congrArg cfAdvantage (funext fun g => ?_)
  rfl

/-- Every `PRF_msg`-oracle query has a message of at most `mlen` bytes. -/
def msgLenLe (mlen : ℕ) : ℕ ⊕ ((St × Blk) ⊕ (Bytes 16 × List Byte)) → Prop
  | .inr (.inr d) => d.2.length ≤ mlen
  | _ => True

theorem ibLenLe_of_msgLenLe (mlen : ℕ) (t : ℕ ⊕ ((St × Blk) ⊕ (Bytes 16 × List Byte)))
    (h : msgLenLe mlen t) : ibLenLe ib128 ((mlen + 24) / 64) t := by
  rcases t with n | q | d
  · trivial
  · trivial
  · show (ib128 d).2.length ≤ (mlen + 24) / 64
    rw [ib128_snd_length]
    have h' : d.2.length ≤ mlen := h
    exact Nat.div_le_div_right (by omega)

/-- **`PRF_msg` is a PRF at SLH-DSA-SHA2-128s in the ideal-compression model.**  A distinguisher
making at most `q` compression queries and `qO` `PRF_msg`-oracle queries, each on a message of
at most `mlen` bytes, satisfies, with
`ε = 2 q / 2^128 + (q + qO ((mlen + 24) / 64 + 1) + 2)² / 2^256`,
`msgRealI A ≤ msgIdealI A + ε` and `msgIdealI A ≤ msgRealI A + ε`. -/
theorem msgPrf_bound_128s (A : MsgPrfAdvI) (q qO mlen : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hM : AllQueriesSatisfy A (msgLenLe mlen)) :
    msgRealI A ≤ msgIdealI A + (2 * (q : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) ∧
      msgIdealI A ≤ msgRealI A + (2 * (q : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hL : AllQueriesSatisfy A (ibLenLe ib128 ((mlen + 24) / 64)) :=
    AllQueriesSatisfy.mono hM fun t ht => ibLenLe_of_msgLenLe mlen t ht
  have h := prT_mac_two_sided IV128 ikey okey ikey_injective okey_injective
    (fun k => ikey_ne_okey k k) ib128 ib128_injective oblock oblock_injective out16 prEvent_out16
    A q qO ((mlen + 24) / 64) hq hO hL
  have hε : 2 * (q : ℝ≥0∞) * (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ +
        ((3 * q + qO * (1 + 3 * ((mlen + 24) / 64)) + 3 +
          (q + qO * (1 + (mlen + 24) / 64)) ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ ≤
      2 * (q : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have e1 : ((256 ^ 16 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by
      rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]; norm_num
    have e2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = 2 ^ 256 := by norm_num
    rw [card_bytes 16, card_St, div_eq_mul_inv, div_eq_mul_inv, e1, e2]
    refine add_le_add le_rfl (mul_le_mul_left (Nat.cast_le.mpr ?_) _)
    generalize (mlen + 24) / 64 = L
    have h1 : qO * (1 + 3 * L) ≤ 3 * (qO * (1 + L)) := by nlinarith
    have h2 : (q + qO * (L + 1) + 2) ^ 2 =
        (q + qO * (1 + L)) ^ 2 + 4 * (q + qO * (1 + L)) + 4 := by ring
    rw [h2]
    omega
  rw [msgRealI_eq, msgIdealI_eq]
  exact ⟨h.1.trans (add_le_add le_rfl hε), h.2.trans (add_le_add le_rfl hε)⟩

/-- The bound for messages of at most `ℓ` SHA-256 blocks (`64 ℓ` bytes):
`ε = 2 q / 2^128 + (q + qO (ℓ + 1) + 2)² / 2^256`. -/
theorem msgPrf_bound_128s_blocks (A : MsgPrfAdvI) (q qO ℓ : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (hO : IsQueryBoundP A (fun i => isPrfQ i = true) qO)
    (hM : AllQueriesSatisfy A (msgLenLe (64 * ℓ))) :
    msgRealI A ≤ msgIdealI A + (2 * (q : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * (ℓ + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) ∧
      msgIdealI A ≤ msgRealI A + (2 * (q : ℝ≥0∞) / 2 ^ 128 +
        (((q + qO * (ℓ + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have h := msgPrf_bound_128s A q qO (64 * ℓ) hq hO hM
  rwa [show (64 * ℓ + 24) / 64 = ℓ by omega] at h

end Ideal

#print axioms Ideal.msgPrf_shape
#print axioms Ideal.msgPrf_eq
#print axioms Ideal.msgIdealI_prims
#print axioms Ideal.msgPrf_bound_128s
#print axioms Ideal.msgPrf_bound_128s_blocks
