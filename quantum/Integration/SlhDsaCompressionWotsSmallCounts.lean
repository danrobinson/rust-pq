import Integration.SlhDsaCompressionWotsSmallFirst
import Ideal.Realize.WotsRealizers
import Reduction.Gen.Forger
import MReduction.Resources

/-! First-phase query counts used in the SHA2-128s and SHA2-128f quantum WOTS compression games. -/
namespace Reduction.Compression.Wots256
open Ideal Ideal.HP Ideal.Realize Ideal.Realize.Wots Open MLink SLHDSA SLHDSA.Security TweakableHash OracleComp OracleSpec PQ.Interactive Quantum ENNReal
attribute [local irreducible] wotsInsts wotsChainTargets wotsStepTargetsT wotsStepTargets Lazy.sparseTable Lazy.structSecIdx
set_option maxRecDepth 1500
set_option maxHeartbeats 450000
attribute [local irreducible] prePhase1 udPhase1 wotsTcrPhase1 simPhase1 WotsGame.simChoose
section
variable {v : ValidatedParams} (base : Primitives v.params)
  [SampleableType base.SkSeed] [SampleableType base.SkPrf] [SampleableType base.Y]
  [DecidableEq base.Y] [DecidableEq base.PkSeed] [DecidableEq base.AdrsKey] [Inhabited base.Y]
  (seeds : ProbComp base.PkSeed)

private theorem pre_raw :
    let o := prePhase1 (vp := v) (prims := base) seeds
    IsQueryBoundP o isChalI ((wotsInsts v).length * (v.params.len * 1)) ∧
      IsQueryBoundP o isColl (wotsQc v + (wotsInsts v).length * (v.params.len * (v.params.w-1))) ∧
      @IsQueryBoundP _ _ _ o (badG (vp := v) (prims := base)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
  let f : HashFns base := ⟨base.Thash,base.Hmsg,base.PRF,base.PRFmsg⟩
  let b := Gen.dummyForger (vp := v) (prims := withHash base f) (optRand := fun _ => pure default) (pkSeedDist := seeds)
  have eq := wotsPre_phase1_q1_zero (vp := v) (prims := base) (pkSeedDist := seeds) f b
  have h1 := rPre_choose_chal seeds b
  have h2 := rPre_choose_coll seeds b
  have h3 := rPre_choose_len seeds b
  rw [eq] at h1 h2 h3
  refine ⟨?_,?_,?_⟩
  · kexact h1
  · kexact h2
  · kexact h3

private theorem ud_raw :
    let o := udPhase1 (vp := v) (prims := base) seeds
    IsQueryBoundP o isChalI ((wotsInsts v).length * (v.params.len * 1)) ∧
      IsQueryBoundP o isColl (wotsQc v + (wotsInsts v).length * (v.params.len * (v.params.w-1))) ∧
      @IsQueryBoundP _ _ _ o (badG (vp := v) (prims := base)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
  let f : HashFns base := ⟨base.Thash,base.Hmsg,base.PRF,base.PRFmsg⟩
  let b := Gen.dummyForger (vp := v) (prims := withHash base f) (optRand := fun _ => pure default) (pkSeedDist := seeds)
  have eq := wotsUd_phase1_q1_zero (vp := v) (prims := base) (pkSeedDist := seeds) f b
  have h1 := rUd_pick_chal seeds b
  have h2 := rUd_pick_coll seeds b
  have h3 := rUd_pick_len seeds b
  rw [eq] at h1 h2 h3
  refine ⟨?_,?_,?_⟩
  · kexact h1
  · kexact h2
  · kexact h3

private theorem tcr_raw :
    let o := wotsTcrPhase1 (vp := v) (prims := base) seeds
    IsQueryBoundP o isChalI ((wotsInsts v).length * (v.params.len * (v.params.w-1))) ∧
      IsQueryBoundP o isColl (wotsQc v + (wotsInsts v).length * (v.params.len * 1)) ∧
      @IsQueryBoundP _ _ _ o (badG (vp := v) (prims := base)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
  let f : HashFns base := ⟨base.Thash,base.Hmsg,base.PRF,base.PRFmsg⟩
  let b := Gen.dummyForger (vp := v) (prims := withHash base f) (optRand := fun _ => pure default) (pkSeedDist := seeds)
  have eq := wotsTcrT_phase1_q1_zero (vp := v) (prims := base) (pkSeedDist := seeds) f b
  have h1 := rTcrT_choose_chal seeds b
  have h2 := rTcrT_choose_coll seeds b
  have h3 := rTcrT_choose_len seeds b
  rw [eq] at h1 h2 h3
  refine ⟨?_,?_,?_⟩
  · kexact h1
  · kexact h2
  · kexact h3
end

def chooseBudget (S : Sha2Set) : ℕ :=
  wotsQc S.vp + (wotsInsts S.vp).length * (S.vp.params.len * S.vp.params.w)

private def blocksOK {T : Type} : ℕ ⊕ ((St × Blk) ⊕ (T ⊕ ((_ : Unit) × Bytes 22 × List Node))) → Prop
  | .inr (.inr (.inr q)) => (tblocks q.2.1 q.2.2).2.length ≤ 9
  | _ => True

private theorem length_embed {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List Node))}
    {α : Type} (oa : OracleComp (unifSpec + X) α)
    (bad : (unifSpec + X).Domain → Prop) [DecidablePred bad] (hb : IsQueryBoundP oa bad 0)
    (hbad : ∀ t, ¬ blocksOK (embIdx t) → bad t) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) (blocksOK (T := T)) := by
  classical
  exact (isQueryBoundP_zero_iff _ _).1 (emb_bound _ oa 0 (IsQueryBoundP.of_imp hbad hb))

private theorem singleton_length (seeds : ProbComp Node) (n : ℕ) (t : Bytes 22) (m : Node) :
    ((family seeds n).tch t m).2.length ≤ 9 := by
  change (tblocks t [m]).2.length ≤ 9
  rw [tblocks_snd_of_length_one _ _ rfl]
  decide


private def tooLong {T : Type} : ℕ ⊕ (T ⊕ ((_ : Unit) × Bytes 22 × List Node)) → Prop
  | .inr (.inr row) => 35 < row.2.2.length
  | _ => False
private instance decLong {T : Type} : DecidablePred (tooLong (T := T)) := fun t => by cases t with
  | inl => exact isFalse id
  | inr t => cases t with
    | inl => exact isFalse id
    | inr q => exact (inferInstanceAs (Decidable (35 < q.2.2.length)))

private theorem long_embed {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List Node))}
    {α : Type} (oa : OracleComp (unifSpec + X) α) (hl : IsQueryBoundP oa tooLong 0) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) (blocksOK (T := T)) := by
  apply length_embed oa _ hl
  rintro (u|t|row) ht
  · exact (ht trivial).elim
  · exact (ht trivial).elim
  · change 35 < row.2.2.length
    change ¬ (tblocks row.2.1 row.2.2).2.length ≤ 9 at ht
    rw [tblocks_snd_length] at ht
    omega

private theorem pre_budgets  (seeds : ProbComp Node) (n : ℕ) {σ : Type}
    (o : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ) (qch qc : ℕ)
    (hc : IsQueryBoundP o isChalI qch) (ho : IsQueryBoundP o isColl qc) (hl : @IsQueryBoundP _ _ _ o (tooLong (T := Bytes 22)) decLong 0) :
    let A := preFirst seeds n o
    IsQueryBoundP (preProg₁ id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (preProg₁ id A) (fun i => isChain i = true) (qch + qc) ∧
      AllQueriesSatisfy (preProg₁ id A) (chainLenLe 9) := by
  let A := preFirst seeds n o
  have z : A.ChooseBound 0 := genP_q1 (family seeds n) o
  have c : A.ChalBound qch := genP_chal (family seeds n) o _ hc
  have co : A.CollBound qc := genP_coll (family seeds n) o _ ho
  have lb : A.CollLen 9 := by
    have h := long_embed o hl
    dsimp only [A,preFirst,PreAdv.CollLen,family,FWots128T,blocksOK] at h ⊢
    kexact h
  exact ⟨preProg₁_pubBound id A z,preProg₁_chainBound id A c co,
    preProg₁_chainLen id A (singleton_length seeds n) lb⟩

private theorem tcr_budgets  (seeds : ProbComp Node) (n : ℕ) {σ : Type}
    (o : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ) (qch qc : ℕ)
    (hc : IsQueryBoundP o isChalI qch) (ho : IsQueryBoundP o isColl qc) (hl : @IsQueryBoundP _ _ _ o (tooLong (T := Bytes 22 × Node)) decLong 0) :
    let A := tcrFirst seeds n o
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (qch + qc) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let A := tcrFirst seeds n o
  have z : A.ChooseBound 0 := genT_q1 (family seeds n) o
  have c : A.ChalBound qch := genT_chal (family seeds n) o _ hc
  have co : A.CollBound qc := genT_coll (family seeds n) o _ ho
  have lb : A.CollLen 9 := by
    have h := long_embed o hl
    dsimp only [A,tcrFirst,TcrAdv.CollLen,family,FWots128T,blocksOK] at h ⊢
    kexact h
  exact ⟨tcrProg₁_pubBound A z,tcrProg₁_chainBound A c co,
    tcrProg₁_chainLen A (singleton_length seeds n) lb⟩

private theorem ud_budgets  (world : SM_DT_UD_World) (seeds : ProbComp Node) (n : ℕ) {σ : Type}
    (o : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ) (qch qc : ℕ)
    (hc : IsQueryBoundP o isChalI qch) (ho : IsQueryBoundP o isColl qc) (hl : @IsQueryBoundP _ _ _ o (tooLong (T := Bytes 22)) decLong 0) :
    let A := udFirst seeds n o
    IsQueryBoundP (udProg₁ world id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (udProg₁ world id A) (fun i => isChain i = true) (qch + qc) ∧
      AllQueriesSatisfy (udProg₁ world id A) (chainLenLe 9) := by
  let A := udFirst seeds n o
  have z : A.PickBound 0 := genP_q1 (family seeds n) o
  have c : A.ChalBound qch := genP_chal (family seeds n) o _ hc
  have co : A.CollBound qc := genP_coll (family seeds n) o _ ho
  have lb : A.CollLen 9 := by
    have h := long_embed o hl
    dsimp only [A,udFirst,UdAdv.CollLen,family,FWots128T,blocksOK] at h ⊢
    kexact h
  exact ⟨udProg₁_pubBound world id A z,udProg₁_chainBound world id A c co,
    udProg₁_chainLen world id A (singleton_length seeds n) lb⟩

private theorem noLong {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List Node))}
    {α : Type} (o : OracleComp (unifSpec + X) α) (bad : (unifSpec + X).Domain → Prop)
    [DecidablePred bad] (h : IsQueryBoundP o bad 0)
    (hb : ∀ row : (_ : Unit) × Bytes 22 × List Node, 35 < row.2.2.length → bad (.inr (.inr row))) :
    IsQueryBoundP o tooLong 0 := by
  apply IsQueryBoundP.of_imp (p' := bad) _ h
  rintro (u|t|row) ht
  · exact False.elim ht
  · exact False.elim ht
  · exact hb row ht

private theorem sum_pre (v : ValidatedParams) (hw : v.params.w = 16) :
    (wotsInsts v).length * (v.params.len * 1) + (wotsQc v + (wotsInsts v).length * (v.params.len * (v.params.w-1))) =
      wotsQc v + (wotsInsts v).length * (v.params.len * v.params.w) := by rw [hw]; ring
private theorem sum_tcr (v : ValidatedParams) (hw : v.params.w = 16) :
    (wotsInsts v).length * (v.params.len * (v.params.w-1)) + (wotsQc v + (wotsInsts v).length * (v.params.len * 1)) =
      wotsQc v + (wotsInsts v).length * (v.params.len * v.params.w) := by rw [hw]; ring
variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp Node) (F : PortForger Input Output E)
private theorem ok_128s (xs : List Node) (ok : OkLen Sha2Set.s128s.vp xs) : xs.length ≤ 35 := by
  rcases ok with h|h|h|h <;> rw [h] <;> decide

theorem pre_counts_128s :
    let A := preFirst seeds (wotsChainTargets Sha2Set.s128s.vp) ((preSelect Sha2Set.s128s seeds F).choose)
    IsQueryBoundP (preProg₁ id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (preProg₁ id A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128s) ∧
      AllQueriesSatisfy (preProg₁ id A) (chainLenLe 9) := by
  let v := Sha2Set.s128s.vp
  let p := randPrims (carrier Sha2Set.s128s)
  let o := prePhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := pre_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128s _ ok)) ht)
  have h := pre_budgets seeds (wotsChainTargets v) o _ _ hc ho hlen
  rw [sum_pre v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,preSelect] at h ⊢
  kexact h

theorem ud_counts_128s (world : SM_DT_UD_World) :
    let A := udFirst seeds (wotsChainTargets Sha2Set.s128s.vp) ((udSelect Sha2Set.s128s seeds F).pick)
    IsQueryBoundP (udProg₁ world id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (udProg₁ world id A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128s) ∧
      AllQueriesSatisfy (udProg₁ world id A) (chainLenLe 9) := by
  let v := Sha2Set.s128s.vp
  let p := randPrims (carrier Sha2Set.s128s)
  let o := udPhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := ud_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128s _ ok)) ht)
  have h := ud_budgets world seeds (wotsChainTargets v) o _ _ hc ho hlen
  rw [sum_pre v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,udSelect] at h ⊢
  kexact h

theorem tcr_counts_128s :
    let A := tcrFirst seeds (wotsStepTargetsT Sha2Set.s128s.vp) ((chainTcrSelect Sha2Set.s128s seeds F).choose)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128s) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let v := Sha2Set.s128s.vp
  let p := randPrims (carrier Sha2Set.s128s)
  let o := wotsTcrPhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := tcr_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128s _ ok)) ht)
  have h := tcr_budgets seeds (wotsStepTargetsT v) o _ _ hc ho hlen
  rw [sum_tcr v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,chainTcrSelect] at h ⊢
  kexact h
private theorem ok_128f (xs : List Node) (ok : OkLen Sha2Set.s128f.vp xs) : xs.length ≤ 35 := by
  rcases ok with h|h|h|h <;> rw [h] <;> decide

theorem pre_counts_128f :
    let A := preFirst seeds (wotsChainTargets Sha2Set.s128f.vp) ((preSelect Sha2Set.s128f seeds F).choose)
    IsQueryBoundP (preProg₁ id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (preProg₁ id A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128f) ∧
      AllQueriesSatisfy (preProg₁ id A) (chainLenLe 9) := by
  let v := Sha2Set.s128f.vp
  let p := randPrims (carrier Sha2Set.s128f)
  let o := prePhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := pre_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128f _ ok)) ht)
  have h := pre_budgets seeds (wotsChainTargets v) o _ _ hc ho hlen
  rw [sum_pre v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,preSelect] at h ⊢
  kexact h

theorem ud_counts_128f (world : SM_DT_UD_World) :
    let A := udFirst seeds (wotsChainTargets Sha2Set.s128f.vp) ((udSelect Sha2Set.s128f seeds F).pick)
    IsQueryBoundP (udProg₁ world id A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (udProg₁ world id A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128f) ∧
      AllQueriesSatisfy (udProg₁ world id A) (chainLenLe 9) := by
  let v := Sha2Set.s128f.vp
  let p := randPrims (carrier Sha2Set.s128f)
  let o := udPhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := ud_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128f _ ok)) ht)
  have h := ud_budgets world seeds (wotsChainTargets v) o _ _ hc ho hlen
  rw [sum_pre v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,udSelect] at h ⊢
  kexact h

theorem tcr_counts_128f :
    let A := tcrFirst seeds (wotsStepTargetsT Sha2Set.s128f.vp) ((chainTcrSelect Sha2Set.s128f seeds F).choose)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (chooseBudget Sha2Set.s128f) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let v := Sha2Set.s128f.vp
  let p := randPrims (carrier Sha2Set.s128f)
  let o := wotsTcrPhase1 (vp := v) (prims := p) seeds
  obtain ⟨hc,ho,hl⟩ := tcr_raw (v := v) p seeds
  have hlen := @noLong _ _ _ o (badG (vp := v) (prims := p)) instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG hl
    (fun row ht ok => (Nat.not_lt_of_ge (ok_128f _ ok)) ht)
  have h := tcr_budgets seeds (wotsStepTargetsT v) o _ _ hc ho hlen
  rw [sum_tcr v (by decide)] at h
  dsimp only [o,v,p,chooseBudget,chainTcrSelect] at h ⊢
  kexact h

theorem chooseBudget_128s : chooseBudget Sha2Set.s128s = 1062883849265657430958591 := by
  let v := Sha2Set.s128s.vp
  have hc := wotsQc_closed v
  have hi : (wotsInsts v).length = 9241421688590303744 := (Resources.wotsInsts_length v).trans (by decide)
  rw [hi, show treeC v = 1023 by decide, show forsC v = 114675 by decide, show v.params.h = 63 by decide] at hc
  change wotsQc v + (wotsInsts v).length * (v.params.len * v.params.w) = _
  rw [hi, show v.params.len = 35 by decide, show v.params.w = 16 by decide]
  omega
theorem chooseBudget_128f : chooseBudget Sha2Set.s128f = 356696784405861438361543 := by
  let v := Sha2Set.s128f.vp
  have hc := wotsQc_closed v
  have hi : (wotsInsts v).length = 84327972908386521672 := MReduction.wotsInsts_length_128f
  rw [hi, show treeC v = 15 by decide, show forsC v = 4192 by decide, show v.params.h = 66 by decide] at hc
  change wotsQc v + (wotsInsts v).length * (v.params.len * v.params.w) = _
  rw [hi, show v.params.len = 35 by decide, show v.params.w = 16 by decide]
  omega
end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_counts_128s
#print axioms Reduction.Compression.Wots256.pre_counts_128f
#print axioms Reduction.Compression.Wots256.ud_counts_128s
#print axioms Reduction.Compression.Wots256.ud_counts_128f
#print axioms Reduction.Compression.Wots256.tcr_counts_128s
#print axioms Reduction.Compression.Wots256.tcr_counts_128f
