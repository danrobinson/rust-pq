import MIdeal.Itsr128fFixed
import Ideal.Realize.MsgReal

/-! The actual SHA2-128f byte-forger reduction satisfies the shared-compression
ITSR bound, including the signer, the final message, and both MGF1 counters. -/

namespace MIdeal.Itsr128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open
open Ideal.Realize.Itsr Reduction.Lazy Ideal.Transport KeyedHash
open Class128f (vp P)
open ENNReal

attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
variable (seeds : ProbComp (Bytes 16))

private def messageHash {K X Y : Type} : PublicHashQuery K X Y → Bool
  | .thash _ _ _ => false
  | .hmsg _ _ _ _ => true

private def overLimit {K X Y : Type} (B L : ℕ) : PublicHashQuery K X Y → Bool
  | .thash _ _ xs => decide (B < xs.length)
  | .hmsg _ _ _ msg => decide (L < msg.length)

private def longTarget {K Y : Type} (L : ℕ) : (K × Y × List Byte) ⊕ (St × Blk) → Bool
  | .inl x => decide (L < x.2.2.length)
  | .inr _ => false

variable (m : CompressionTables) (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)

private noncomputable abbrev raw :=
  itsrOpenP (vp := vp) (prims := P m) (fun k => rand k.pkSeed k.pkRoot) seeds (PureCompression.typed Sha2Set.s128f A m m.2)
private theorem okLen {xs : List (Bytes 16)} (h : OkLen vp xs) : xs.length ≤ vp.params.len := by
  rcases h with h|h|h|h <;> rw [h] <;> decide

def budget (q qs L : ℕ) :=
  q + (keygenHashes vp + qs * signHashes vp) * thashCost vp.params.len + qs * ((L+257+56)/64+4)

include hq hs hl in
theorem count : IsQueryBoundP (program rand A seeds m) (fun i => Ideal.Itsr.isCompI i = true)
    (budget q qs L) := by
  classical
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  let o := raw rand A seeds m
  have hp : IsQueryBoundP o (fun (t : IdxI (P m)) => predR (D := SecIdx) (fun x : ItsrIn (P m) ⊕ (St × Blk) => x.isRight) (fun _ => false) t = true) q :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | z <;> simp_all [predR,isPortI]) (itsrOpenP_port r seeds f (PureCompression.typed_port _ A m _ hq))
  have hh : IsQueryBoundP o (fun (t : IdxI (P m)) => predR (D := SecIdx) (fun _ : ItsrIn (P m) ⊕ (St × Blk) => false) (fun _ => true) t = true)
      (keygenHashes vp + qs * signHashes vp) :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | z <;> simp_all [predR,Lazy.kind]) (itsrOpenP_hashes r seeds f (PureCompression.typed_sign _ A m _ hs))
  have hm : IsQueryBoundP o (fun (t : IdxI (P m)) => predR (D := SecIdx) (fun _ : ItsrIn (P m) ⊕ (St × Blk) => false) messageHash t = true) qs :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | (q|q) <;> simp_all [predR,messageHash,isHmsgIdx]) (itsrOpenP_hmsg r seeds f (PureCompression.typed_sign _ A m _ hs))
  have hb : IsQueryBoundP o (fun (t : IdxI (P m)) => predR (D := SecIdx) (fun _ : ItsrIn (P m) ⊕ (St × Blk) => false) (overLimit vp.params.len (L+257)) t = true) 0 :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | (z|z) <;> simp_all [predR,overLimit,isBadIdx]) (itsrOpenP_bad r seeds f vp.params.len (fun _ => okLen) (PureCompression.typed_long _ A m _ hl))
  have p := lazyRes_predR (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ _ hp
  have h := lazyRes_predR (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ _ hh
  have d := lazyRes_predR (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ _ hm
  have b := lazyRes_predR (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ _ hb
  refine (qb_simulateQ_classes 1 (thashCost vp.params.len) ((L+257+56)/64+4)
    (fun t ht => ?_) b p h d).mono (by simp [budget])
  rcases t with n | (x|c) | u | h
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hx => by cases hx
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hx => by cases hx
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · exact Msg.liftM_zero _ _ (fun _ h => by cases h)
  · have hb := Msg.cEmb_bound (X := TargetSpec) (Class128f.hashImpl m h) _
      (Class128f.hash_count m h) (fun i => Ideal.Itsr.isCompI i = true) (fun _ => rfl) (fun _ h => by cases h)
    apply hb.mono
    cases h with
    | thash pk a xs =>
      have len : xs.length ≤ vp.params.len := by simpa only [predR,overLimit,decide_eq_true_eq,not_lt] using ht
      simpa only [Class128f.stepCost,predR,messageHash,ite_true,Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero]
        using thashCost_mono len
    | hmsg R pk root msg =>
      have len : msg.length ≤ L+257 := by simpa only [predR,overLimit,decide_eq_true_eq,not_lt] using ht
      simp only [Class128f.stepCost,predR,messageHash,ite_true,Bool.false_eq_true,ite_false,Nat.zero_add]
      omega

include hs in
theorem targets : IsQueryBoundP (program rand A seeds m) (fun i => Ideal.Itsr.isTgtI i = true) qs := by
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  have ht : IsQueryBoundP (raw rand A seeds m)
      (fun (t : IdxI (P m)) => predR (D := SecIdx) (fun x : ItsrIn (P m) ⊕ (St × Blk) => x.isLeft) (fun _ => false) t = true) qs :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | z <;> simp_all [predR,Ideal.Realize.Itsr.isTgtI]) (itsrOpenP_tgt r seeds f (PureCompression.typed_sign _ A m _ hs))
  have h := lazyRes_predR (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ _ ht
  refine IsQueryBoundP.simulateQ_of_step (p := fun (t : (USpec m).Domain) => predR (D := Unit) (fun x : ItsrIn (P m) ⊕ (St × Blk) => x.isLeft) (fun _ => false) t = true) h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (x|c) | u | z
    · simp [predR] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [predR] at ht
    · simp [predR] at ht
    · simp [predR] at ht
  · rcases t with n | (x|c) | u | z
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by cases h
    · simp [predR] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => by cases h
    · exact Msg.liftM_zero _ _ (fun _ h => by cases h)
    · exact Msg.cEmb_zero _ _ (fun _ h => by cases h) (fun _ h => by cases h)

include hl in
theorem targets_length : AllQueriesSatisfy (program rand A seeds m) (Ideal.Itsr.tgtOK (Hmsg.Fast128.lengthOK (L+257))) := by
  classical
  let f := PureCompression.typed Sha2Set.s128f A m m.2
  let r := fun (k : PublicKeyCore (P m).core) => rand k.pkSeed k.pkRoot
  have h0 : IsQueryBoundP (raw rand A seeds m)
      (fun (t : IdxI (P m)) => predR (D := SecIdx) (longTarget (L+257)) (fun _ => false) t = true) 0 :=
    IsQueryBoundP.of_imp (fun t ht => by rcases t with n | (x|c) | u | z <;> simp_all [predR,longTarget,isLongTgtI]) (itsrOpenP_longTgt r seeds f (PureCompression.typed_long _ A m _ hl))
  classical
  refine AllQueriesSatisfy.simulateQ (lazyRes_predR_all (G := gI (P m)) (hspec := publicHashSpec (P m).core) _ _ _ h0) fun t ht => ?_
  rcases t with n | (x|c) | u | z
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · have hx : x.2.2.length ≤ L+257 := by simpa [predR,longTarget] using ht
    exact (allQueriesSatisfy_query_iff _ _).2 fun _ => hx
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · rw [← isQueryBoundP_zero_iff]
    exact Msg.liftM_zero _ _ (fun _ h => h trivial)
  · rw [← isQueryBoundP_zero_iff]
    exact Msg.cEmb_zero _ _ (fun _ h => h trivial) (fun _ h => h trivial)

include ho in
theorem output_length (z : Hmsg.Fast128.Input) (hz : z ∈ support (program rand A seeds m)) :
    Hmsg.Fast128.lengthOK (L+257) z := by
  have h := support_simulateQ_subset _ _ hz
  unfold lazyRes at h
  have hh := support_simulateQ_run'_subset _ _ _ h
  exact itsrOpenP_out (prims := P m) (fun k => rand k.pkSeed k.pkRoot) seeds
    (PureCompression.typed Sha2Set.s128f A m m.2) (PureCompression.typed_out _ A m _ ho) z hh

noncomputable def loss (q qs L : ℕ) : ℝ≥0∞ :=
  let Q := budget q qs L + (qs+1)*((L+257+56)/64+4)
  reuseSum 66 6 33 Q + ((Q^2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)^256)⁻¹

include hq hs hl ho in
theorem term :
    PureCompression.average (fun g => ITSRAdvantage (bItsrL (prims := P g) (reduced rand A seeds g))) ≤
      loss q qs L := by
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => ITSRAdvantage (bItsrL (prims := P (c,other)) (reduced rand A seeds (c,other)))) ≤ loss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := program rand A seeds ref
    have he (c : CF St Blk) := congrArg evalDist (experiment rand A seeds ref.1 (c,other))
    have hp (c : CF St Blk) :
        ITSRAdvantage (bItsrL (prims := P (c,other)) (reduced rand A seeds (c,other))) =
          𝒟[ITSRExperiment (bItsrL (prims := P (c,other)) (reduced rand A seeds (c,other)))] {true} := ITSRAdvantage_eq_evalDist_experiment _
    apply ((cfAvg_congr hp).trans ((cfAvg_of_evalDist_eq he).trans (cfAdvantage_eq_prT _))).le.trans
    exact Hmsg.Fast128.itsr_bound D other (budget q qs L) qs (L+257)
      (count rand A seeds ref q qs L hq hs hl)
      (targets rand A seeds ref qs hs)
      (targets_length rand A seeds ref L hl)
      (output_length rand A seeds ref L ho)
  apply (cfAvg_mono bound).trans
  let _ : MeasurableSpace (CF Chain512 Block512) := ⊤
  unfold cfAvg
  rw [MeasureTheory.lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end MIdeal.Itsr128f

#print axioms MIdeal.Itsr128f.count
#print axioms MIdeal.Itsr128f.targets
#print axioms MIdeal.Itsr128f.targets_length
#print axioms MIdeal.Itsr128f.output_length
#print axioms MIdeal.Itsr128f.term
