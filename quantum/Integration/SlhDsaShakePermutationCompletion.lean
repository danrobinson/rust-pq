import Integration.SlhDsaShakePermutationBlocks
import Integration.SlhDsaShakePermutationFixSimulator
import Integration.SlhDsaShakeXofRows
import Integration.SlhDsaShakeApiRaw

namespace Reduction.ShakePermutation.Completion
open MLink SLHDSA ShakeXof Classical ENNReal

def bytes (w : Rate) : Bytes 136 := Vector.ofFn fun i => UInt8.ofBitVec (blockByte w i)
def words (x : Bytes 136) : Rate := rateBlock (sp x.toList) 0

theorem bytes_words (x : Bytes 136) : bytes (words x) = x := by
  apply Vector.ext
  intro i hi
  simp [bytes,words,blockByte_rateBlock,sp]

def equiv : Rate ≃ Bytes 136 := by
  classical
  have count : Fintype.card Rate = Fintype.card (Bytes 136) := by
    change Fintype.card (Fin 17 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,card_bytes']
    decide +kernel
  have inj := ((Fintype.bijective_iff_surjective_and_card bytes).mpr
    ⟨Function.RightInverse.surjective bytes_words,count⟩).1
  exact ⟨bytes,words,fun x => inj (bytes_words _),bytes_words⟩

def blockCap (N : ℕ) := N/136+1

private theorem ofFn_inj {α : Type} {L : ℕ} (a b : BList α L) (e : List.ofFn a.2 = List.ofFn b.2) : a = b := by
  let f (xs : List α) := if h : xs.length ≤ L then some (BList.ofList xs h) else none
  have ok (a : BList α L) : f (List.ofFn a.2) = some a := by
    have h : (List.ofFn a.2).length ≤ L := by simpa only [List.length_ofFn] using Nat.le_of_lt_succ a.1.isLt
    simp only [f,dite_eq_left h,BList.ofList_ofFn]
  exact Option.some.inj ((ok _).symm.trans ((congrArg f e).trans (ok _)))

def address {N T : ℕ} (cap : blockCap N ≤ T) : ShakeApi.Input N ↪ Fix.Domain T where
  toFun x := BList.ofList (messageBlocks (sp (List.ofFn x.2))) (by
    rw [messageBlocks_length]
    apply le_trans _ cap
    unfold blockCap
    simp only [sp,List.length_map,List.length_ofFn]
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_of_lt_succ x.1.isLt)) _)
  inj' x y eq := by
    have e := congrArg (fun j : Fix.Domain T => List.ofFn j.2) eq
    simp only [BList.ofFn_ofList] at e
    apply ofFn_inj
    have eq' := congrArg cv (messageBlocks_injective e)
    simpa [cv,sp,List.map_map,Function.comp_def] using eq'

variable (S : Sha2Set) {N T : ℕ} (cap : blockCap N ≤ T)
abbrev Private (T : ℕ) := Fix.Domain T → Bytes 136

noncomputable def complete (g : Private T) (H : ShakeApi.RawTable S N) : Fix.Table T :=
  fun x => equiv.symm (write (address cap) g H x)

theorem prefix_complete (g : Private T) (H : ShakeApi.RawTable S N) (x : ShakeApi.Input N)
    (size : S.vp.params.m ≤ 136) :
    head size (bytes (complete S cap g H (address cap x))) = H x := by
  change head size (equiv (equiv.symm _)) = _
  simp only [Equiv.apply_symm_apply,write,locate_emb,Option.elim_some,head_replace]

theorem uniform_complete (size : S.vp.params.m ≤ 136) (test : Fix.Table T → ℝ≥0∞) :
    SetOracle.uniformMean test = SetOracle.uniformMean (fun g : Private T =>
      SetOracle.uniformMean (fun H : ShakeApi.RawTable S N => test (complete S cap g H))) := by
  let e : Private T ≃ Fix.Table T := Equiv.arrowCongr (Equiv.refl _) equiv.symm
  have changeWorld := Equiv.sum_comp e (fun H => unifW _ H * test H)
  calc SetOracle.uniformMean test = SetOracle.uniformMean (fun g => test (e g)) := by
         simpa only [SetOracle.uniformMean,unifW,Fintype.card_congr e] using changeWorld.symm
       _ = _ := resample (address cap) size (fun g => test (e g))

end Reduction.ShakePermutation.Completion
#print axioms Reduction.ShakePermutation.Completion.prefix_complete
#print axioms Reduction.ShakePermutation.Completion.uniform_complete
