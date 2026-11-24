import MIdeal.Wots128fFirst

/-! First-phase SHA2-128f compression, challenge, and collection budgets for the
WOTS undetectability, preimage, and chain target-collision games. -/

namespace MIdeal.Wots128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Ideal.Realize.Wots Reduction.Resources2 Reduction.Lazy
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance countOutputSampler (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance countSeedSampler (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance countPrfSampler (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance countOutputInhabited (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance countOutputEq (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance countSeedEq (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance countAddressEq (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance countOutputFinite (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
private theorem okLen {xs : List (Bytes 16)} (h : OkLen vp xs) : xs.length ≤ vp.params.len := by
  rcases h with h|h|h|h <;> rw [h] <;> decide

attribute [local irreducible] udChoose preChoose tcrChoose
section First
set_option maxRecDepth 2500
variable (seeds : ProbComp (Bytes 16)) (ref : CompressionTables)
def blockBudget : ℕ := (22+16*vp.params.len+8)/64

private def lengthOk {T : Type} : ℕ ⊕ ((St × Blk) ⊕ (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))) → Prop
  | .inr (.inr (.inr q)) => (tblocks q.2.1 q.2.2).2.length ≤ blockBudget
  | _ => True

private theorem emb_length {T : Type} {X : OracleSpec (T ⊕ ((_ : Unit) × Bytes 22 × List (Bytes 16)))}
    {α : Type} (m : CompressionTables) (oa : OracleComp (unifSpec + X) α)
    (h : @IsQueryBoundP _ (unifSpec + X) _ oa (badG (vp := vp) (prims := P m) (T := T))
       (instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG) 0) :
    AllQueriesSatisfy (simulateQ (embImpl (X := X)) oa) (lengthOk (T := T)) := by
  classical
  refine (isQueryBoundP_zero_iff _ _).1 (emb_bound _ oa 0 ?_)
  refine @IsQueryBoundP.of_imp _ _ _ _ (fun t => ¬ lengthOk (embIdx t)) (badG (vp := vp) (prims := P m) (T := T)) _ instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 (fun t ht => ?_) h
  rcases t with n|t|q
  · exact (ht trivial).elim
  · exact (ht trivial).elim
  · intro ok
    apply ht
    change (tblocks q.2.1 q.2.2).2.length ≤ blockBudget
    rw [tblocks_snd_length]
    have len := okLen ok
    unfold blockBudget
    omega

theorem ud_zero : (udAdv rand A seeds ref).PickBound 0 := by
  have h := genP_q1 (α := PhaseState) (Hash128f.chainFamily seeds) (udChoose rand A seeds ref)
  dsimp only [UdAdv.PickBound,udAdv, Hash128f.chainFamily, Hash128f.FWots128T, Ideal.FWots128T,
    THFam.pIsH, THFam.isH, THFam.collS] at h ⊢
  kexact h

theorem pre_zero : (preAdv rand A seeds ref).ChooseBound 0 := by
  have h := genP_q1 (α := PhaseState) (Hash128f.chainFamily seeds) (preChoose rand A seeds ref)
  dsimp only [PreAdv.ChooseBound,preAdv, Hash128f.chainFamily, Hash128f.FWots128T, Ideal.FWots128T,
    THFam.pIsH, THFam.isH, THFam.collS] at h ⊢
  kexact h

theorem tcr_zero : (tcrAdv rand A seeds ref).ChooseBound 0 := by
  have h := genT_q1 (α := PhaseState) (Hash128f.FWots128T seeds) (tcrChoose rand A seeds ref)
  dsimp only [TcrAdv.ChooseBound,tcrAdv, Hash128f.chainFamily, Hash128f.FWots128T, Ideal.FWots128T,
    THFam.pIsH, THFam.isH, THFam.collS] at h ⊢
  kexact h

theorem ud_chal : (udAdv rand A seeds ref).ChalBound ((wotsInsts vp).length * (vp.params.len * (1))) := by
  have raw : IsQueryBoundP (udChoose rand A seeds ref) isChalI ((wotsInsts vp).length * (vp.params.len * (1))) := by
    unfold udChoose
    kexact rUd_pick_chal (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genP_chal (α := PhaseState) (Hash128f.chainFamily seeds) (udChoose rand A seeds ref) _ raw
  dsimp only [UdAdv.ChalBound,udAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem ud_coll : (udAdv rand A seeds ref).CollBound (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  have raw : IsQueryBoundP (udChoose rand A seeds ref) isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
    unfold udChoose
    kexact rUd_pick_coll (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genP_coll (α := PhaseState) (Hash128f.chainFamily seeds) (udChoose rand A seeds ref) _ raw
  dsimp only [UdAdv.CollBound,udAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem ud_len : (udAdv rand A seeds ref).CollLen blockBudget := by
  have raw : @IsQueryBoundP _ _ _ (udChoose rand A seeds ref) (badG (vp := vp) (prims := P ref))
      instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
    unfold udChoose
    kexact rUd_pick_len (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := emb_length (α := PhaseState) ref (udChoose rand A seeds ref) raw
  dsimp only [UdAdv.CollLen,udAdv, Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,lengthOk] at h ⊢
  kexact h

private theorem pre_as_irred :
    @Eq (OracleComp (preSpecC (Bytes 22) (Bytes 16)) PhaseState)
      (preChoose rand A seeds ref) (preChooseI (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)) := by
  unfold preChoose preChooseI
  dsimp only [reduced,PureCompression.internalBytes,PureCompression.codec,P,tablePrimitives,sha2PrimitivesMixed]
  rfl

theorem pre_chal : (preAdv rand A seeds ref).ChalBound ((wotsInsts vp).length * (vp.params.len * (1))) := by
  have raw : IsQueryBoundP (preChoose rand A seeds ref) isChalI ((wotsInsts vp).length * (vp.params.len * (1))) := by
    rw [pre_as_irred]
    exact preChooseI_chal (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genP_chal (α := PhaseState) (Hash128f.chainFamily seeds) (preChoose rand A seeds ref) _ raw
  dsimp only [PreAdv.ChalBound,preAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem pre_coll : (preAdv rand A seeds ref).CollBound (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  have raw : IsQueryBoundP (preChoose rand A seeds ref) isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
    rw [pre_as_irred]
    exact preChooseI_coll (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genP_coll (α := PhaseState) (Hash128f.chainFamily seeds) (preChoose rand A seeds ref) _ raw
  dsimp only [PreAdv.CollBound,preAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem pre_len : (preAdv rand A seeds ref).CollLen blockBudget := by
  have raw : @IsQueryBoundP _ _ _ (preChoose rand A seeds ref) (badG (vp := vp) (prims := P ref))
      instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
    rw [pre_as_irred]
    exact preChooseI_len (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := emb_length (α := PhaseState) ref (preChoose rand A seeds ref) raw
  dsimp only [PreAdv.CollLen,preAdv, Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,lengthOk] at h ⊢
  kexact h

private theorem tcr_as_irred :
    @Eq (OracleComp (tcrSpecC (Bytes 22) (Bytes 16)) PhaseState)
      (tcrChoose rand A seeds ref) (tcrChooseI (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)) := by
  unfold tcrChoose tcrChooseI
  dsimp only [reduced,PureCompression.internalBytes,PureCompression.codec,P,tablePrimitives,sha2PrimitivesMixed]
  rfl

theorem tcr_chal : (tcrAdv rand A seeds ref).ChalBound ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  have raw : IsQueryBoundP (tcrChoose rand A seeds ref) isChalI ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
    rw [tcr_as_irred]
    exact tcrChooseI_chal (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genT_chal (α := PhaseState) (Hash128f.FWots128T seeds) (tcrChoose rand A seeds ref) _ raw
  dsimp only [TcrAdv.ChalBound,tcrAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem tcr_coll : (tcrAdv rand A seeds ref).CollBound (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (1))) := by
  have raw : IsQueryBoundP (tcrChoose rand A seeds ref) isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (1))) := by
    rw [tcr_as_irred]
    exact tcrChooseI_coll (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := genT_coll (α := PhaseState) (Hash128f.FWots128T seeds) (tcrChoose rand A seeds ref) _ raw
  dsimp only [TcrAdv.CollBound,tcrAdv,Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,
    THFam.pIsChal,THFam.pIsColl,THFam.isChal,THFam.isColl,THFam.collS] at h ⊢
  kexact h

theorem tcr_len : (tcrAdv rand A seeds ref).CollLen blockBudget := by
  have raw : @IsQueryBoundP _ _ _ (tcrChoose rand A seeds ref) (badG (vp := vp) (prims := P ref))
      instDecidablePredSumNatSigmaUnitProdAdrsKeyListYBadG 0 := by
    rw [tcr_as_irred]
    exact tcrChooseI_len (vp := vp) (prims := P ref) seeds (reduced rand A seeds ref)
  have h := emb_length (α := PhaseState) ref (tcrChoose rand A seeds ref) raw
  dsimp only [TcrAdv.CollLen,tcrAdv, Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T,lengthOk] at h ⊢
  kexact h
end First
end MIdeal.Wots128f

#print axioms MIdeal.Wots128f.pre_zero
#print axioms MIdeal.Wots128f.pre_chal
#print axioms MIdeal.Wots128f.pre_coll
#print axioms MIdeal.Wots128f.pre_len
#print axioms MIdeal.Wots128f.tcr_zero
#print axioms MIdeal.Wots128f.tcr_chal
#print axioms MIdeal.Wots128f.tcr_coll
#print axioms MIdeal.Wots128f.tcr_len
#print axioms MIdeal.Wots128f.ud_zero
#print axioms MIdeal.Wots128f.ud_chal
#print axioms MIdeal.Wots128f.ud_coll
#print axioms MIdeal.Wots128f.ud_len
