import Integration.SlhDsaCompressionShortBlocks
import Ideal.Realize.TcrCount

namespace Reduction.Compression.ShortBlocks
open Ideal Ideal.HP Ideal.Realize MLink SLHDSA SLHDSA.Security TweakableHash OracleComp OracleSpec Reduction.Open Wots256
attribute [local irreducible] tcrTargets arityTargets wotsInsts Lazy.sparseTable Lazy.structSecIdx
set_option maxHeartbeats 500000

private theorem raw {v : ValidatedParams} (p : Primitives v.params)
    [SampleableType p.SkSeed] [SampleableType p.SkPrf] [SampleableType p.Y]
    [DecidableEq p.Y] [DecidableEq p.PkSeed] [DecidableEq p.AdrsKey] [Inhabited p.Y]
    (ar : ℕ) (ok : ∀ xs : List p.Y, OkLen v xs → xs.length ≤ 35) :
    let o := tcrPhase1 v p ar
    IsQueryBoundP o (fun t => t.isRight = true) (tcrTargets v) ∧
      IsQueryBoundP o (fun t => bad1 (Tweak := p.AdrsKey) (fun xs : List p.Y => xs.length = ar) 35 t = true) 0 := by
  dsimp only
  unfold tcrPhase1
  generalize eq : tcrChooseHF v p = chooser
  exact ⟨(routeHF_cap (PkSeed := p.PkSeed) (fun xs : List p.Y => xs.length = ar) (tcrTargets v) chooser []).mono (by simp),
    routeHF_len (PkSeed := p.PkSeed) _ _ 35 chooser (eq ▸ tcrChooseHF_len (vp := v) (prims := p) 35 ok) []⟩

/-- The chooser has one joint budget for both kinds of hash request. Each
successful challenge or collection query costs only one chain call. -/
private theorem joint {St Blk PK T M Y ι : Type} {F : THFam St Blk PK T M Y ι}
    [DecidableEq T] (A : TcrAdv F) (q : ℕ)
    (hb : IsQueryBoundP A.choose (fun i => (F.isChal i || F.isColl i) = true) q) :
    IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) q := by
  refine IsQueryBoundP.simulateQ_run_of_step hb (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | tm | q
    · simp [THFam.isChal,THFam.isColl] at ht
    · simp [THFam.isChal,THFam.isColl] at ht
    · rcases s with ⟨qs,tw⟩
      by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;> simp [tcrGameM,h,isChain]
    · rcases s with ⟨qs,tw⟩
      by_cases h : TweakReserved (Q := T × M) Prod.fst qs q.2.1 <;> simp [tcrGameM,h,isChain]
  · rcases t with n | q | tm | q
    · simp [tcrGameM,isChain]
    · simp [tcrGameM,isChain]
    · simp [THFam.isChal,THFam.isColl] at ht
    · simp [THFam.isChal,THFam.isColl] at ht

private theorem setup {σ : Type} (seeds : ProbComp Node) (ar n cap : ℕ)
    (o : OracleComp (Spec1 (Bytes 22) Node (fun xs => xs.length = ar)) σ)
    (hc : IsQueryBoundP o (fun t => t.isRight = true) cap)
    (hl : IsQueryBoundP o (fun t => bad1 (Tweak := Bytes 22) (fun xs : List Node => xs.length = ar) 35 t = true) 0) :
    let A := classFirst seeds ar n o
    A.ChooseBound 0 ∧ IsQueryBoundP A.choose
        (fun i => ((family seeds ar n).isChal i || (family seeds ar n).isColl i) = true) cap ∧ A.CollLen 9 := by
  let A := classFirst seeds ar n o
  have h0 : A.ChooseBound 0 := by
    exact emb_noH (fun i => (family seeds ar n).isH i = true) (fun t => by rcases t with m|t <;> simp [embIdx,THFam.isH]) o
  have hq : IsQueryBoundP A.choose (fun i => ((family seeds ar n).isChal i || (family seeds ar n).isColl i) = true) cap := by
    apply emb_bound _ o cap (Tcr.of_imp' _ hc)
    rintro (u|c) h
    · simp [embIdx,THFam.isChal,THFam.isColl] at h
    · rfl
  have hlen : A.CollLen 9 := by
    classical
    unfold TcrAdv.CollLen
    rw [← isQueryBoundP_zero_iff]
    apply emb_bound _ o 0 (Tcr.of_imp' _ hl)
    rintro (u|⟨tw,xs⟩|⟨u,tw,xs⟩) ht
    · simp [embIdx] at ht
    · simp [embIdx] at ht
    · simp only [embIdx,family,not_le] at ht
      have t := tblocks_snd_length tw xs
      simp only [bad1,decide_eq_true_eq]
      omega
  exact ⟨h0,hq,hlen⟩

private theorem budgets {σ : Type} (seeds : ProbComp Node) (ar n cap : ℕ) (ha : ar ≤ 35)
    (o : OracleComp (Spec1 (Bytes 22) Node (fun xs => xs.length = ar)) σ)
    (hc : IsQueryBoundP o (fun t => t.isRight = true) cap)
    (hl : IsQueryBoundP o (fun t => bad1 (Tweak := Bytes 22) (fun xs : List Node => xs.length = ar) 35 t = true) 0) :
    let A := classFirst seeds ar n o
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) cap ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let A := classFirst seeds ar n o
  obtain ⟨h0,hq,hlen⟩ := setup seeds ar n cap o hc hl
  exact ⟨tcrProg₁_pubBound A h0, joint A cap hq,
    tcrProg₁_chainLen A (fun tw x => by change (tblocks tw x.val).2.length ≤ 9; rw [tblocks_snd_length,x.property]; omega) hlen⟩

theorem long_counts_128s (seeds : ProbComp Node) (ar : ℕ) (ha : ar ≤ 35) :
    let A := classFirst seeds ar (arityTargets Sha2Set.s128s.vp ar)
      (tcrPhase1 Sha2Set.s128s.vp (randPrims (carrier Sha2Set.s128s)) ar)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (tcrTargets Sha2Set.s128s.vp) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let v := Sha2Set.s128s.vp
  let p := randPrims (carrier Sha2Set.s128s)
  have h := raw (v := v) p ar (fun xs ok => by rcases ok with h|h|h|h <;> rw [h] <;> decide)
  exact budgets seeds ar (arityTargets v ar) (tcrTargets v) ha (tcrPhase1 v p ar) h.1 h.2

theorem long_counts_128f (seeds : ProbComp Node) (ar : ℕ) (ha : ar ≤ 35) :
    let A := classFirst seeds ar (arityTargets Sha2Set.s128f.vp ar)
      (tcrPhase1 Sha2Set.s128f.vp (randPrims (carrier Sha2Set.s128f)) ar)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (tcrTargets Sha2Set.s128f.vp) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := by
  let v := Sha2Set.s128f.vp
  let p := randPrims (carrier Sha2Set.s128f)
  have h := raw (v := v) p ar (fun xs ok => by rcases ok with h|h|h|h <;> rw [h] <;> decide)
  exact budgets seeds ar (arityTargets v ar) (tcrTargets v) ha (tcrPhase1 v p ar) h.1 h.2

theorem class_counts_128s (seeds : ProbComp Node) (ar : ℕ) (ha : ar ≤ 2) :
    let A := classFirst seeds ar (arityTargets Sha2Set.s128s.vp ar)
      (tcrPhase1 Sha2Set.s128s.vp (randPrims (carrier Sha2Set.s128s)) ar)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (tcrTargets Sha2Set.s128s.vp) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := long_counts_128s seeds ar (by omega)

theorem class_counts_128f (seeds : ProbComp Node) (ar : ℕ) (ha : ar ≤ 2) :
    let A := classFirst seeds ar (arityTargets Sha2Set.s128f.vp ar)
      (tcrPhase1 Sha2Set.s128f.vp (randPrims (carrier Sha2Set.s128f)) ar)
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) 0 ∧
      IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (tcrTargets Sha2Set.s128f.vp) ∧
      AllQueriesSatisfy (tcrProg₁ A) (chainLenLe 9) := long_counts_128f seeds ar (by omega)

private theorem setup_individual {σ : Type} (seeds : ProbComp Node) (ar n cap : ℕ)
    (o : OracleComp (Spec1 (Bytes 22) Node (fun xs => xs.length = ar)) σ)
    (hc : IsQueryBoundP o (fun t => t.isRight = true) cap)
    (hl : IsQueryBoundP o (fun t => bad1 (Tweak := Bytes 22) (fun xs : List Node => xs.length = ar) 35 t = true) 0) :
    let A := classFirst seeds ar n o
    A.ChooseBound 0 ∧ A.ChalBound cap ∧ A.CollBound cap ∧ A.CollLen 9 := by
  obtain ⟨h0,hj,hlen⟩ := setup seeds ar n cap o hc hl
  exact ⟨h0,hj.of_imp (fun t h => by simp [h]),hj.of_imp (fun t h => by simp [h]),hlen⟩

theorem setup_128s (seeds : ProbComp Node) (ar : ℕ) :
    let v := Sha2Set.s128s.vp
    let A := classFirst seeds ar (arityTargets v ar) (tcrPhase1 v (randPrims (carrier Sha2Set.s128s)) ar)
    A.ChooseBound 0 ∧ A.ChalBound (tcrTargets v) ∧ A.CollBound (tcrTargets v) ∧ A.CollLen 9 := by
  let v := Sha2Set.s128s.vp
  let p := randPrims (carrier Sha2Set.s128s)
  have h := raw (v := v) p ar (fun xs ok => by rcases ok with h|h|h|h <;> rw [h] <;> decide)
  exact setup_individual seeds ar (arityTargets v ar) (tcrTargets v) (tcrPhase1 v p ar) h.1 h.2

theorem setup_128f (seeds : ProbComp Node) (ar : ℕ) :
    let v := Sha2Set.s128f.vp
    let A := classFirst seeds ar (arityTargets v ar) (tcrPhase1 v (randPrims (carrier Sha2Set.s128f)) ar)
    A.ChooseBound 0 ∧ A.ChalBound (tcrTargets v) ∧ A.CollBound (tcrTargets v) ∧ A.CollLen 9 := by
  let v := Sha2Set.s128f.vp
  let p := randPrims (carrier Sha2Set.s128f)
  have h := raw (v := v) p ar (fun xs ok => by rcases ok with h|h|h|h <;> rw [h] <;> decide)
  exact setup_individual seeds ar (arityTargets v ar) (tcrTargets v) (tcrPhase1 v p ar) h.1 h.2

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.long_counts_128s
#print axioms Reduction.Compression.ShortBlocks.long_counts_128f
#print axioms Reduction.Compression.ShortBlocks.setup_128s
#print axioms Reduction.Compression.ShortBlocks.setup_128f
