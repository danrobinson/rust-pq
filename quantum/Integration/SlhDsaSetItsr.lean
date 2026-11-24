import Integration.SlhDsaSetItsrMach
import Integration.SlhDsaItsrWidths
import Integration.SlhDsaSetTcr
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)

open QItsr QMsg
def hmsgTable (c : Caps) (H : S.Node × (S.Node × S.Node × BList Byte c.ml) → Bytes S.vp.params.m) :=
  fun r pk root m => H (r,pk,root,m)

noncomputable instance (c : Caps) : Fintype (S.Node × (S.Node × S.Node × BList Byte c.ml) → Bytes S.vp.params.m) := by
  classical
  exact Pi.instFintype

theorem avg_hmsg (c : Caps) (f : FinFns S.vp.params c → ℝ≥0∞) :
    SetOracle.avg S c f = SetOracle.avg S c fun g =>
      ∑ H : S.Node × (S.Node × S.Node × BList Byte c.ml) → Bytes S.vp.params.m,
        (Fintype.card (S.Node × (S.Node × S.Node × BList Byte c.ml) → Bytes S.vp.params.m) : ℝ≥0∞)⁻¹ * f (g.withHmsg (hmsgTable S c H)) :=
  avg_resample (Ω := FinFns S.vp.params c)
    (T := S.Node × (S.Node × S.Node × BList Byte c.ml) → Bytes S.vp.params.m)
    (fun g H => g.withHmsg (hmsgTable S c H)) (fun g (r,pk,root,m) => g.hmsg r pk root m)
    (by rintro ⟨⟨_,_,_,_⟩,_⟩; rfl) f

theorem cover_mono (a b : Finset (Bytes S.vp.params.m)) (u) (h : a ⊆ b)
    (hc : SetDigest.idxCov S.vp a u) : SetDigest.idxCov S.vp b u :=
  fun i hi => by obtain ⟨d, hd, hdi⟩ := hc i hi; exact ⟨d, h hd, hdi⟩

theorem digest_bound (q s : ℕ) :
    (((2 * (q : ℝ≥0∞) + 1)^2 * coverProb (Fin s) (SetDigest.idxCov S.vp)) ^ (2⁻¹ : ℝ) +
      2*q*((s : ℝ≥0∞) * (Fintype.card S.Node : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ))^2 ≤ itsrBound S.vp.params q s := by
  have hc := SetDigest.coverProb_idxCov_le S.vp s
  rw [coverProb_fors] at hc
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hk : Fintype.card S.Node = 2^(8*S.vp.params.n) := by rw [card_bytes', pow_mul]; rfl
  rw [hk, Nat.cast_pow, Nat.cast_ofNat]
  unfold itsrBound
  gcongr

section Win
open KeyedHash
variable (c : Caps)

/-- A message truncated to the cap. -/
def tg (x : S.Node × S.Node × List Byte) : (S.Node × S.Node × BList Byte c.ml) := (x.1, x.2.1, cutB c x.2.2)

theorem tg_inj (x y : S.Node × S.Node × List Byte) (hx : x.2.2.length ≤ c.ml) (hy : y.2.2.length ≤ c.ml)
    (h : tg S c x = tg S c y) : x = y := by
  obtain ⟨a, b, m⟩ := x
  obtain ⟨a', b', m'⟩ := y
  simp only [tg, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  rw [cutB_of c m hx, cutB_of c m' hy] at h
  have := congrArg (fun z : BList Byte c.ml ↦ List.ofFn z.2) h
  simp only [BList.ofFn_ofList] at this
  rw [this]

theorem hash_withHmsg (ω₀ : FinFns S.vp.params c) (Hf : S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m)) (R : S.Node) (x : S.Node × S.Node × List Byte)
    (hx : x.2.2.length ≤ c.ml) :
    (itsrProblem S.vp (worldPrims (ω₀.withHmsg (hmsgTable S c Hf)))).khf.hash R x = Hf (R, tg S c x) := by
  obtain ⟨pk, root, m⟩ := x
  simp only at hx
  show (if h : m.length ≤ c.ml then _ else _) = _
  rw [dite_eq_left hx]
  simp only [tg, cutB_of c m hx]
  rfl

theorem mem_pairs {s : ℕ} (Rs : Fin s → S.Node) (t : List (S.Node × S.Node × List Byte)) (e : S.Node × (S.Node × S.Node × List Byte)) :
    e ∈ pairs Rs 0 t ↔ ∃ (j : ℕ) (h : j < t.length), (rndAt Rs j, t[j]) = e := by
  unfold pairs
  rw [List.mem_mapIdx]
  simp

set_option maxRecDepth 100000 in
theorem win_conv (ω₀ : FinFns S.vp.params c) (Hf : S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m)) {s : ℕ} (Rs : Fin s → S.Node)
    (cand : S.Node × (S.Node × S.Node × List Byte)) (t : List (S.Node × S.Node × List Byte))
    (hcand : cand.2.2.2.length ≤ c.ml) (ht : ∀ y ∈ t, y.2.2.length ≤ c.ml) (hlen : t.length ≤ s)
    (hw : (itsrProblem S.vp (worldPrims (ω₀.withHmsg (hmsgTable S c Hf)))).Wins (pairs Rs 0 t) cand) :
    itsrAWin (SetDigest.idxCov S.vp) Rs Hf (⟨QReg.of Unit, ((cand.1, tg S c cand.2), t.map (tg S c))⟩ :
      Σ _ : QReg, (S.Node × (S.Node × S.Node × BList Byte c.ml)) × List ((S.Node × S.Node × BList Byte c.ml))) := by
  classical
  set prob := itsrProblem S.vp (worldPrims (ω₀.withHmsg (hmsgTable S c Hf))) with hprob
  obtain ⟨hnot, hcov⟩ := hw
  have hidx : ∀ (R : S.Node) (x : S.Node × S.Node × List Byte), x.2.2.length ≤ c.ml →
      prob.indexSet (R, x) = (SetDigest.idxOf S.vp) (Hf (R, tg S c x)) := fun R x hx ↦ by
    show prob.indices (prob.khf.hash R x) = _
    rw [hash_withHmsg S c ω₀ Hf R x hx]
    rfl
  refine ⟨fun hmem ↦ hnot ?_, fun i hi ↦ ?_⟩
  · have hmem' : isTgt Rs (t.map (tg S c)) (cand.1, tg S c cand.2) := by
      unfold itsrATargets at hmem
      exact (Finset.mem_filter.1 hmem).2
    obtain ⟨j, hj, hj'⟩ := hmem'
    simp only [List.getElem?_map] at hj'
    obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hj'
    have hjl : j.1 < t.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hy
      cases hy
    have hyt : t[j.1] = y := by
      rw [List.getElem?_eq_getElem hjl] at hy
      exact Option.some.inj hy
    have hyc : y = cand.2 := tg_inj S c y cand.2 (ht y (hyt ▸ List.getElem_mem hjl)) hcand hyx
    refine (mem_pairs S Rs t cand).2 ⟨j.1, hjl, ?_⟩
    rw [rndAt_lt Rs j.1 j.2, hyt, hyc]
    exact Prod.ext hj rfl
  · have hi' : i ∈ prob.indexSet cand := by rw [hidx cand.1 cand.2 hcand]; exact hi
    obtain ⟨e, he, hie⟩ := List.mem_flatMap.1 (hcov i hi')
    obtain ⟨j, hj, rfl⟩ := (mem_pairs S Rs t e).1 he
    have hjs : j < s := lt_of_lt_of_le hj hlen
    have htg : (Rs ⟨j, hjs⟩, tg S c t[j]) ∈ itsrATargets Rs (t.map (tg S c)) := by
      unfold itsrATargets
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨⟨j, hjs⟩, rfl, ?_⟩⟩
      simp [List.getElem?_map, List.getElem?_eq_getElem hj]
    refine ⟨Hf (Rs ⟨j, hjs⟩, tg S c t[j]), Finset.mem_image.2 ⟨_, htg, rfl⟩, ?_⟩
    · rw [hidx _ _ (ht _ (List.getElem_mem hj)), rndAt_lt Rs j hjs] at hie
      exact hie

end Win

section Final
open KeyedHash

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- The embedding of the `H_msg` table domain into the port domain. -/
def ιH : S.Node × (S.Node × S.Node × BList Byte c.ml) → Input S c := fun z ↦ .inr (.inl (z.1, z.2.1, z.2.2.1, z.2.2.2))

theorem ιH_injective : Function.Injective (ιH S c) := by
  rintro ⟨a, b, d, e⟩ ⟨a', b', d', e'⟩ h
  simp only [ιH, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The candidate read within the cap. -/
noncomputable def ocO : Option (S.Node × (S.Node × S.Node × List Byte)) → S.Node × (S.Node × S.Node × BList Byte c.ml)
  | some z => (z.1, tg S c z.2)
  | none => Classical.arbitrary _

theorem encΩ_withHmsg_local (ω₀ : FinFns S.vp.params c) (H G : S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m)) (z : Input S c)
    (h : oracle S (ω₀.withHmsg (hmsgTable S c H)) z ≠ oracle S (ω₀.withHmsg (hmsgTable S c G)) z) :
    ∃ w, ιH S c w = z ∧ H w ≠ G w := by
  rcases z with x | x | x | x
  · exact absurd rfl h
  · refine ⟨(x.1, x.2.1, x.2.2.1, x.2.2.2), rfl, fun he ↦ h ?_⟩
    change (0, H (x.1, x.2.1, x.2.2.1, x.2.2.2)) = (0, G (x.1, x.2.1, x.2.2.1, x.2.2.2))
    rw [he]
  · exact absurd rfl h
  · exact absurd rfl h

theorem supp_qbItsrL (qs : ℕ) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (ω : FinFns S.vp.params c) :
    AllQueries (QG (WS (Input S c) (Output S) E) (Gfin (Ptgt (worldPrims ω) c.ml)))
        (fun r : S.Node × ItsrIn (worldPrims ω) ↦ r.2.2.2.length ≤ c.ml)
        (qbItsrL (internal S c optRand₀ pkSeedDist₀ F ω)) ∧
      CountBound (QC (WS (Input S c) (Output S) E) isR)
        (qbItsrL (internal S c optRand₀ pkSeedDist₀ F ω)) qs := by
  have hQ : ∀ pk, AllQueries (QG (WS (Input S c) (Output S) E) (Gint c.ml))
      (fun z : List Byte × _ ↦ z.1.length ≤ c.ml)
      ((internal S c optRand₀ pkSeedDist₀ F ω).main pk) := fun pk ↦
    allQ_and (allQ_qPureBytesToInternal c.ml _
        (fun pkb ↦ allQ_compileQ c (oracle S ω) (F.main pkb) (hcap pkb)) pk)
      (out_qPureBytesToInternal _ c.ml
        (fun pkb ↦ allQ_out_simulateQ (compileImplQ (oracle S ω)) (hcap pkb)) pk)
  have hO := allQ_qItsrOpen (worldPrims ω) c.ml _ hQ
  refine ⟨allQ_and (allQ_qLazyRun _ (Ptgt (worldPrims ω) c.ml) _
      (allQ_mono (fun _ h ↦ h) (fun _ _ ↦ trivial) hO)) (out_qLazyRun _ _ hO), ?_⟩
  exact cb_qLazyRun _ _ (cb_qItsrOpen (worldPrims ω) _ fun pk ↦
    cb_qPureBytesToInternal _ (fun pkb ↦ cb_compileQ (oracle S ω) (F.main pkb) (hqs pkb)) pk)

/-- **The ITSR term**, from an interactive adversary over the PORT oracle (machine side,
`hPort`) and the forger hypotheses `hqs`, `hcap`. -/
theorem itsr_term_port (q' qs : ℕ)
    (hPort : ∀ ω₀ : FinFns S.vp.params c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
      (x : IAdv L (qromSpec (Input S c) (Output S)) (S.Node × S.Node × List Byte) S.Node (fun _ ↦ Option (S.Node × (S.Node × S.Node × List Byte))) qs A),
      IAdv.IsQueryBound qs x (fun _ ↦ q') ∧
      ∀ (Hm : S.Node → S.Node → S.Node → BList Byte c.ml → (Bytes S.vp.params.m)) (Rs : Fin qs → S.Node)
        (Ev : Option (S.Node × (S.Node × S.Node × List Byte)) × List (S.Node × S.Node × List Byte) → Prop) [DecidablePred Ev],
        qprob I (oracle S (ω₀.withHmsg Hm))
            (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (Input S c) (Output S))) qs [] x)
            ρ (fun p ↦ Ev p.2) =
          qWeight (fun z ↦ Ev (some z.1, z.2))
            (close (rndImpl (X := (S.Node × S.Node × List Byte)) Rs) (qbItsrL (internal S c optRand₀ pkSeedDist₀ F
              (ω₀.withHmsg Hm))) []) F.ρ₀)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.avg S c (fun ω ↦ qItsrAdvantage (itsrProblem S.vp (worldPrims ω))
      (qbItsrL (internal S c optRand₀ pkSeedDist₀ F ω))
      (internal S c optRand₀ pkSeedDist₀ F ω).ρ₀) ≤ itsrBound S.vp.params q' qs := by
  classical
  rw [avg_hmsg S c]
  refine (SetOracle.avg_mono S c fun ω₀ ↦ ?_).trans (le_of_eq (SetOracle.avg_const S c _))
  obtain ⟨L, A, I, ρ, x, hx, hEq⟩ := hPort ω₀
  let Ev : (Fin qs → S.Node) → (S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m)) →
      Option (S.Node × (S.Node × S.Node × List Byte)) × List (S.Node × S.Node × List Byte) → Prop :=
    fun Rs Hf ot ↦ itsrAWin (SetDigest.idxCov S.vp) Rs Hf (⟨QReg.of Unit, (ocO S c ot.1, ot.2.map (tg S c))⟩ :
      Σ _ : QReg, (S.Node × (S.Node × S.Node × BList Byte c.ml)) × List ((S.Node × S.Node × BList Byte c.ml)))
  have key : ∀ Hf : S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m),
      qItsrAdvantage (itsrProblem S.vp (worldPrims (ω₀.withHmsg (hmsgTable S c Hf))))
        (qbItsrL (internal S c optRand₀ pkSeedDist₀ F (ω₀.withHmsg (hmsgTable S c Hf))))
        (internal S c optRand₀ pkSeedDist₀ F (ω₀.withHmsg (hmsgTable S c Hf))).ρ₀ ≤
      PQ.QROM.avg fun Rs : Fin qs → S.Node ↦ qprob I (oracle S (ω₀.withHmsg (hmsgTable S c Hf)))
        (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (Input S c) (Output S))) qs [] x) ρ
        (fun p ↦ Ev Rs Hf p.2) := by
    intro Hf
    obtain ⟨hA, hC⟩ := supp_qbItsrL S c optRand₀ pkSeedDist₀ F qs hqs hcap
      (ω₀.withHmsg (hmsgTable S c Hf))
    unfold qItsrAdvantage
    rw [presample (s := qs) (itsrProblem S.vp (worldPrims (ω₀.withHmsg (hmsgTable S c Hf)))) rfl _ _ qs [] []
      (cb_isT hC) (by simp) _]
    refine PQ.QROM.avg_mono fun Rs ↦ ?_
    rw [hEq (hmsgTable S c Hf) Rs (Ev Rs Hf)]
    refine qWeight_mono_allQ (close_rndImpl_supp Rs _ _ _ qs [] hA hC) (fun z hz hw ↦ ?_) _
    simp only [List.length_nil, List.drop_zero, List.nil_append, Nat.zero_add] at hw hz
    exact win_conv S c ω₀ Hf Rs z.1 z.2 hz.1
      (fun y hy ↦ (hz.2.2 y hy).resolve_left (List.not_mem_nil)) hz.2.1 hw
  calc _ ≤ ∑ Hf : S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m), (Fintype.card (S.Node × (S.Node × S.Node × BList Byte c.ml) → (Bytes S.vp.params.m)) : ℝ≥0∞)⁻¹ *
          PQ.QROM.avg (fun Rs : Fin qs → S.Node ↦ qprob I (oracle S (ω₀.withHmsg (hmsgTable S c Hf)))
            (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (Input S c) (Output S))) qs [] x)
            ρ (fun p ↦ Ev Rs Hf p.2)) :=
        Finset.sum_le_sum fun Hf _ ↦ mul_le_mul' le_rfl (key Hf)
    _ = Pull.itsrPExp (fun H ↦ oracle S (ω₀.withHmsg (hmsgTable S c H))) (tg S c) (fun _ ↦ ocO S c)
          I ρ qs x (SetDigest.idxCov S.vp) := by
        unfold Pull.itsrPExp PQ.QROM.avg
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Rs _ ↦ Finset.sum_congr rfl fun Hf _ ↦ ?_
        rw [show (fun p ↦ Ev Rs Hf p.2) = (fun p ↦ itsrAWin (SetDigest.idxCov S.vp) Rs Hf
          (Pull.lv (tg S c) (fun _ ↦ ocO S c) p)) from rfl]
        ring
    _ ≤ _ := Pull.itsrP_adaptive_le (ιH_injective S c) (encΩ_withHmsg_local S c ω₀) (cover_mono S) hx
    _ ≤ _ := digest_bound S q' qs

theorem itsr_closed (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.avg S c (fun ω ↦ qItsrAdvantage (itsrProblem S.vp (worldPrims ω))
      (qbItsrL (internal S c optRand₀ pkSeedDist₀ F ω))
      (internal S c optRand₀ pkSeedDist₀ F ω).ρ₀) ≤
      itsrBound S.vp.params (q + itsrHashes S.vp qs) qs := by
  exact itsr_term_port S c optRand₀ pkSeedDist₀ F (q + itsrHashes S.vp qs) qs
    (itsr_hPort S c optRand₀ pkSeedDist₀ F q qs hq hqs) hqs hcap

end Final
end Reduction.SetOracle

#print axioms Reduction.SetOracle.itsr_closed
