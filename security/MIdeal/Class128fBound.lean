import MIdeal.Class128fFixed

/-! Classical class-TCR at SHA2-128f for the forger induced by the pure-byte
signature reduction. Phase one walks the key structure before the seed is revealed.
Phase two runs the byte forger, signer and final search against the public SHA-256
table. The outer average permits public access to the independent SHA-512 table. -/
namespace MIdeal.Class128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport
open TweakableHash ENNReal

attribute [local irreducible] arityTargets tcrTargets Lazy.sparseTable Lazy.structSecIdx
local instance (g : CompressionTables) : SampleableType (P g).Y := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
variable (seeds : ProbComp (Bytes 16)) (ref : CompressionTables) (n : ℕ)
local notation "B" => vp.params.len
private abbrev State := (SecIdx → Bytes 16) × List (Bytes 22 × List (Bytes 16))
private abbrev Ph (n : ℕ) := OracleComp (Spec1 (Bytes 22) (Bytes 16) (fun xs => xs.length = n)) State
private noncomputable def phase (ref : CompressionTables) (n : ℕ) : Ph n := tcrPhase1 vp (P ref) n

private theorem okLengths {xs : List (Bytes 16)} (h : OkLen vp xs) : xs.length ≤ B := by
  rcases h with h|h|h|h <;> rw [h] <;> decide

private noncomputable def adversary : TcrAdv (Hash128f.F128T seeds n) where
  State := State
  choose := simulateQ embImpl (phase ref n)
  forge := fun st pk => forge rand A ref n st.1 (clampL B st.2) pk

private theorem choose_eq : (adversary rand A seeds ref n).choose = simulateQ embImpl (phase ref n) := by krfl

private theorem phase_caps (oa : Ph n) (h : oa = phase ref n) :
    IsQueryBoundP oa (fun t => t.isRight = true) (tcrTargets vp) ∧
    IsQueryBoundP oa (fun t => bad1 (Tweak := Bytes 22) (fun xs : List (Bytes 16) => xs.length = n) B t = true) 0 := by
  delta phase tcrPhase1 at h
  generalize hc : tcrChooseHF vp (P ref) = c at h
  subst h
  constructor
  · exact (routeHF_cap (PkSeed := Bytes 16) (fun xs : List (Bytes 16) => xs.length = n) (tcrTargets vp) c []).mono (by simp)
  · exact routeHF_len (PkSeed := Bytes 16) (fun xs : List (Bytes 16) => xs.length = n) (tcrTargets vp) B c (hc ▸ tcrChooseHF_len (vp := vp) (prims := P ref) B (fun _ => okLengths)) []

private theorem choose_bound : (adversary rand A seeds ref n).ChooseBound 0 := by
  unfold TcrAdv.ChooseBound
  rw [choose_eq]
  generalize phase ref n = oa
  exact emb_noH (fun i => (Hash128f.F128T seeds n).isH i = true) (fun t => by rcases t with m|t <;> simp [embIdx,THFam.isH]) oa

private theorem challenge_bound : (adversary rand A seeds ref n).ChalBound (tcrTargets vp) := by
  unfold TcrAdv.ChalBound
  rw [choose_eq]
  generalize h : phase ref n = oa
  refine emb_bound (fun i => (Hash128f.F128T seeds n).isChal i = true) oa _ (Tcr.of_imp' (fun t ht => ?_) (phase_caps ref n oa h.symm).1)
  rcases t with m|t
  · simp [embIdx,THFam.isChal] at ht
  · rfl

private theorem collection_bound : (adversary rand A seeds ref n).CollBound (tcrTargets vp) := by
  unfold TcrAdv.CollBound
  rw [choose_eq]
  generalize h : phase ref n = oa
  refine emb_bound (fun i => (Hash128f.F128T seeds n).isColl i = true) oa _ (Tcr.of_imp' (fun t ht => ?_) (phase_caps ref n oa h.symm).1)
  rcases t with m|t
  · simp [embIdx,THFam.isColl] at ht
  · rfl

private theorem collection_len : (adversary rand A seeds ref n).CollLen ((22+16*B+8)/64) := by
  classical
  unfold TcrAdv.CollLen
  rw [← isQueryBoundP_zero_iff,choose_eq]
  generalize h : phase ref n = oa
  refine emb_bound _ oa 0 (Tcr.of_imp' (fun t ht => ?_) (phase_caps ref n oa h.symm).2)
  rcases t with m|⟨tw,xs⟩|⟨u,tw,xs⟩
  · simp [embIdx] at ht
  · simp [embIdx] at ht
  · simp only [embIdx, Hash128f.F128T,Ideal.F128T,not_le] at ht
    have hl := tblocks_snd_length tw xs
    simp only [bad1,decide_eq_true_eq]
    omega

private theorem phase_transport {v : ValidatedParams} (base : Primitives v.params)
    [Inhabited base.Y] [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
    [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey]
    (T : base.PkSeed → base.AdrsKey → List base.Y → base.Y)
    (H : base.Y → base.PkSeed → base.Y → List Byte → Bytes v.params.m)
    (prf : base.PkSeed → base.SkSeed → Adrs → base.Y) (pm : base.SkPrf → base.Y → List Byte → base.Y) :
    (tcrPhase1 v (setPrf (withTH base T H) prf pm) n : OracleComp (TcrP1Spec base n) (TcrP1State v base)) =
      tcrPhase1 v base n := by krfl

private theorem phase_same (g : CompressionTables) : phase g n = phase ref n := by
  let T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 := (P g).Thash
  let H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 34 := (P g).Hmsg
  let prf : Bytes 16 → Bytes 16 → Adrs → Bytes 16 := (P g).PRF
  let pm : Bytes 16 → Bytes 16 → List Byte → Bytes 16 := (P g).PRFmsg
  have h := phase_transport n (v := vp) (P ref) T H prf pm
  dsimp only [T,H,prf,pm,phase,withTH,setPrf,setPrfC,P,tablePrimitives,sha2PrimitivesMixed] at h ⊢
  kexact h

private theorem phase_clamp :
    (fun z : State => (z.1,clampL B z.2)) <$> phase ref n = phase ref n :=
  routeHF_clamp _ _ B _ (tcrChooseHF_len (vp := vp) (prims := P ref) B (fun _ => okLengths)) [] (by simp)

private noncomputable abbrev reduced (g : CompressionTables) :=
  bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary

set_option maxHeartbeats 600000 in
private theorem experiment_eq (c : CF St Blk) :
    let g : CompressionTables := (c,ref.2)
    let D := adversary rand A seeds ref n
    SM_DT_TCR_Experiment (bTcrArM n (reduced rand A seeds g)) =
      SM_DT_TCR_Experiment (D.inst c) := by
  let g : CompressionTables := (c,ref.2)
  let C := bTcrArM n (reduced rand A seeds g)
  let D := adversary rand A seeds ref n
  have ch : C.choose = phase ref n := (bTcrArM_choose_eq n _).trans (phase_same ref n g)
  have hc : (D.inst c).choose = phase ref n := instImpl_emb c (phase ref n)
  let cut := fun z : State => (z.1,clampL B z.2)
  have prep := experiment_map_choose (prob := thashArityProblemT vp (P g) seeds n)
    cut (phase ref n) C.forge
  have hcut : cut <$> phase ref n = phase ref n := phase_clamp ref n
  apply (Tcr.exp_choose_congr C ch).trans
  have mapChoose := congrArg (fun choose : Ph n =>
    SM_DT_TCR_Experiment (⟨State,choose,C.forge⟩ :
      SM_DT_TCR_Adversary (thashArityProblemT vp (P g) seeds n))) hcut.symm
  apply mapChoose.trans
  apply prep.trans
  have hf (st : State) (pk : Bytes 16) :
      (D.inst c).forge st pk = C.forge (cut st) pk := by
    exact forge_fixed rand A ref.1 g seeds n st.1 (clampL B st.2) pk
  refine (SM_DT_TCR_Experiment_congr (iT' := inferInstanceAs (DecidableEq (Bytes 22)))
    (iM' := inferInstanceAs (DecidableEq {xs : List (Bytes 16) // xs.length = n}))
    (iY' := inferInstanceAs (DecidableEq (Bytes 16))) (ι := Unit) (PkSeed := Bytes 16) (Tweak := Bytes 22)
    (M := {xs : List (Bytes 16) // xs.length = n}) (Y := Bytes 16) seeds
    (fun pk tw m => (P g).Thash pk tw m.1) ((Hash128f.F128T seeds n).evalT c)
    (fun _ => List (Bytes 16)) (fun _ => (P g).Thash) ((Hash128f.F128T seeds n).evalC c)
    (arityTargets vp n) (Hash128f.F128T seeds n).numTargets
    (by funext pk tw m; exact Hash128f.shape g pk tw m.1)
    (by funext _ pk tw xs; exact Hash128f.shape g pk tw xs) rfl
    (State) (phase ref n) (fun st pk => C.forge (cut st) pk)).trans ?_
  exact congrArg SM_DT_TCR_Experiment (adv_ext hc.symm (funext fun st => funext fun pk => (hf st pk).symm))

noncomputable def classLoss (n q qs L : ℕ) : ℝ≥0∞ :=
  let Q := forgeBudget q qs L
  let t := tcrTargets vp
  let b := (22+16*n+8)/64
  let w := (22+16*vp.params.len+8)/64
  (Q + 2*b + 4 : ℕ) * ((2:ℝ≥0∞)^128)⁻¹ +
    (18 * tcrMultiQ 0 t t w Q b ^ 2 + (t+t)*(1+2*max b w)+1 : ℕ) * ((2:ℝ≥0∞)^256)⁻¹

/-- The class-TCR contribution of the actual byte-forger reduction, averaged over
both random compression tables. The public-key seed distribution is arbitrary. -/
theorem class_term (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L) :
    PureCompression.average (fun g => SM_DT_TCR_Advantage (bTcrArM n
      (bytesToTyped (PureCompression.internalBytes Sha2Set.s128f rand seeds A g).toUnforgeableAdversary))) ≤
        classLoss n q qs L := by
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => SM_DT_TCR_Advantage (bTcrArM n (reduced rand A seeds (c,other)))) ≤ classLoss n q qs L := by
    let m : CompressionTables := (default,other)
    let D := adversary rand A seeds m n
    have he (c : CF St Blk) := congrArg evalDist (experiment_eq rand A seeds m n c)
    have eq := (cfAvg_of_evalDist_eq he).trans ((cfAdvantage_eq_idealAdvT _).trans
      (tcrAdvantage_eq_idealAdv (Hash128f.F128T seeds n) D).symm)
    apply eq.le.trans
    have hf : D.ForgeBound (forgeBudget q qs L) := fun st pk =>
      forge_count rand A m n st.1 (clampL B st.2) pk q qs L hq hs hl ho (clampL_mem _ _)
    have h := Hash128f.tcrArityT_bound_multi seeds n 1
      (fun s => by exact le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _))
      D 0 (tcrTargets vp) (tcrTargets vp) ((22+16*B+8)/64) (forgeBudget q qs L)
      (choose_bound rand A seeds m n) (challenge_bound rand A seeds m n)
      (collection_bound rand A seeds m n) (collection_len rand A seeds m n) hf
    simpa only [classLoss,Nat.cast_zero,zero_mul,Nat.mul_zero,Nat.add_zero,add_zero] using h
  unfold PureCompression.average
  apply (cfAvg_mono bound).trans
  let _ : MeasurableSpace (CF Chain512 Block512) := ⊤
  unfold cfAvg
  rw [MeasureTheory.lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end MIdeal.Class128f

#print axioms MIdeal.Class128f.class_term
