import Integration.SlhDsaCompressionShortBlocks
import Ideal.Games.TcrMultiPhase2

namespace Reduction.Compression.LongClass.Certificate
set_option linter.unusedSectionVars false
open Ideal Ideal.HP Ideal.MP2
variable {St Blk K T M Y I : Type} [DecidableEq St] [DecidableEq Blk]

/-- The physical SHA input for a public or private-row compression cell. -/
def address (cv : St) : Cell St Blk → St × Blk
  | .inl x => x
  | .inr b => (cv,b)

def select (cv : St) (p : St × Blk) : Cell St Blk :=
  if p.1 = cv then .inr p.2 else .inl p

/-- Replay the actual table, retaining only queries whose answers are not
already fixed by the seed prefix or the honest transcript. -/
def observe (IV : St) (sb : Blk) (cv : St) (c : Cell St Blk → Option St)
    (g : CF St Blk) (p : St × Blk) : List ((St × Blk) × St) :=
  if p = (IV,sb) ∨ (c (select cv p)).isSome then [] else [(p,g p)]

def walkLog (log : St × Blk → List ((St × Blk) × St)) (g : CF St Blk) :
    St → List Blk → List ((St × Blk) × St)
  | _, [] => []
  | s,b::bs => log (s,b) ++ walkLog log g (g (s,b)) bs

def pathLog (log : St × Blk → List ((St × Blk) × St)) (g : CF St Blk) (cv : St)
    (X : Blk × List Blk) :=
  log (cv,X.1) ++ walkLog log g (g (cv,X.1)) X.2

variable (IV : St) (sb : Blk) (cv : St) (c : Cell St Blk → Option St) (g : CF St Blk)
local notation "rec" => observe IV sb cv c g

private theorem len_obs (p : St × Blk) : (rec p).length ≤ 1 := by
  unfold observe
  split <;> simp

theorem walk_length (s : St) (bs : List Blk) : (walkLog rec g s bs).length ≤ bs.length := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [walkLog,List.length_append,List.length_cons]
    have := len_obs IV sb cv c g (s,b)
    have := ih (g (s,b))
    omega

theorem path_length (X : Blk × List Blk) : (pathLog rec g cv X).length ≤ X.2.length+1 := by
  unfold pathLog
  rw [List.length_append]
  have := len_obs IV sb cv c g (cv,X.1)
  have := walk_length IV sb cv c g (g (cv,X.1)) X.2
  omega

variable {IV sb cv c g}
variable {d : Cell St Blk → Option St}

/-- The completed physical compression table respects the fixed entries on
all physically accessible cells except the separately programmed seed. -/
def Fixed (IV : St) (sb : Blk) (cv : St) (c : Cell St Blk → Option St)
    (g : CF St Blk) : Prop :=
  ∀ p v, p ≠ (IV,sb) → c (select cv p) = some v → g p = v

def Matches (cv : St) (d : Cell St Blk → Option St) (l : List ((St × Blk) × St)) : Prop :=
  ∀ p v, (p,v) ∈ l → d (select cv p) = some v

private theorem matches_append {x y : List ((St × Blk) × St)} (h : Matches cv d (x++y)) :
    Matches cv d x ∧ Matches cv d y :=
  ⟨fun p v h₁ => h p v (List.mem_append_left _ h₁),fun p v h₂ => h p v (List.mem_append_right _ h₂)⟩

private theorem at_cell (hp : p ≠ (IV,sb)) (hf : Fixed IV sb cv c g) (he : CLe c d)
    (hm : Matches cv d (rec p)) : d (select cv p) = some (g p) := by
  cases h : c (select cv p) with
  | none => exact hm p (g p) (by simp [observe,h,hp])
  | some v => rw [hf p v hp h]; exact he _ _ h

private theorem walk_recorded (hf : Fixed IV sb cv c g) (he : CLe c d)
    (hn : ∀ x, d x ≠ some IV ∧ d x ≠ some cv) (s : St) (bs : List Blk)
    (hi : s ≠ IV) (hc : s ≠ cv) (hm : Matches cv d (walkLog rec g s bs)) :
    walk d s bs = some (mdFold g s bs) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨h₁,h₂⟩ := matches_append hm
    have h := at_cell (p := (s,b)) (fun e => hi (congrArg Prod.fst e)) hf he h₁
    simp only [select,hc,ite_false] at h
    simp only [walk,h,Option.bind_some]
    exact ih _ (fun e => (hn _).1 (h.trans (congrArg some e)))
      (fun e => (hn _).2 (h.trans (congrArg some e))) h₂

theorem chain_recorded (hf : Fixed IV sb cv c g) (he : CLe c d)
    (hn : ∀ x, d x ≠ some IV ∧ d x ≠ some cv) (hcv : cv ≠ IV) (X : Blk × List Blk)
    (hm : Matches cv d (pathLog rec g cv X)) :
    chainVal d X = some (mdFold g (g (cv,X.1)) X.2) := by
  obtain ⟨h₁,h₂⟩ := matches_append hm
  have h := at_cell (p := (cv,X.1)) (fun e => hcv (congrArg Prod.fst e)) hf he h₁
  simp only [select,ite_true] at h
  simp only [chainVal,h,Option.bind_some]
  exact walk_recorded hf he hn _ _ (fun e => (hn _).1 (h.trans (congrArg some e)))
      (fun e => (hn _).2 (h.trans (congrArg some e))) h₂

private theorem observe_fresh {p q : St × Blk} {v : St} (hm : (q,v) ∈ rec p) :
    q ≠ (IV,sb) ∧ c (select cv q) = none ∧ g q = v := by
  unfold observe at hm
  split at hm
  · simp at hm
  next h =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    exact ⟨fun e => h (Or.inl e), Option.not_isSome_iff_eq_none.mp (fun e => h (Or.inr e)), rfl⟩

private theorem walk_fresh {p : St × Blk} {v : St} {s : St} {bs : List Blk}
    (hm : (p,v) ∈ walkLog rec g s bs) : p ≠ (IV,sb) ∧ c (select cv p) = none ∧ g p = v := by
  induction bs generalizing s with
  | nil => contradiction
  | cons b bs ih =>
    obtain h|h := List.mem_append.mp hm
    · exact observe_fresh h
    · exact ih h

theorem path_fresh {p : St × Blk} {v : St} {Xb : Blk × List Blk}
    (hm : (p,v) ∈ pathLog rec g cv Xb) : p ≠ (IV,sb) ∧ c (select cv p) = none ∧ g p = v := by
  obtain h|h := List.mem_append.mp hm
  · exact observe_fresh h
  · exact walk_fresh h

variable (F : THFam St Blk K T M Y I) (btw : Blk → T) (L : ℕ) (qs : List (T × M))
variable (pk : K) (cv : St) (c : Cell St Blk → Option St) (g : CF St Blk)
local notation "trace" => pathLog (observe F.IV (F.sb pk) cv c g) g cv
def comparisonLog (t : T) (m org : M) := trace (F.tch t m) ++ trace (F.tch t org)

theorem comparison_length (hlen : ∀ t m, (F.tch t m).2.length = L) (t : T) (m org : M) :
    (comparisonLog F pk cv c g t m org).length ≤ 2*(L+1) := by
  unfold comparisonLog
  rw [List.length_append]
  have h₁ := path_length F.IV (F.sb pk) cv c g (F.tch t m)
  have h₂ := path_length F.IV (F.sb pk) cv c g (F.tch t org)
  rw [hlen] at h₁ h₂
  omega

theorem bad_of_comparison (hlen : ∀ t m, (F.tch t m).2.length = L)
    (hbtw : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m')
    (hcv : cv ≠ F.IV) (hseed : g (F.IV,F.sb pk) = cv) (hf : Fixed F.IV (F.sb pk) cv c g)
    (he : CLe c d) {t : T} {m org : M} (ht : (t,org) ∈ qs) (hne : m ≠ org)
    (hw : F.out (keyedChain F.IV F.sb g pk (F.tch t m)) =
      F.out (keyedChain F.IV F.sb g pk (F.tch t org)))
    (hm : Matches cv d (comparisonLog F pk cv c g t m org)) :
    ¬ Good F btw L qs cv d := by
  intro hg
  obtain ⟨h₁,h₂⟩ := matches_append hm
  obtain ⟨v,hv,hu⟩ := hg.tgt _ _ ht
  have hnew := chain_recorded hf he hg.nov hcv _ h₁
  have hold := chain_recorded hf he hg.nov hcv _ h₂
  rw [hold] at hv
  cases Option.some.inj hv
  exact hu _ _ (hlen _ _) (hbtw _ _) (fun e => hne (hinj _ _ _ e)) hnew
    (by simpa only [keyedChain,hseed] using hw)

section Normalized
/-- The normalized table used after exposing the honest chooser's cache. -/
def normalized (IV : St) (sb : Blk) (cv : St) (c : Cell St Blk → Option St)
    (U : CF St Blk) (V : Blk → St) :=
  gstar IV sb cv (fun x => (c (.inl x)).getD (U x)) (fun b => (c (.inr b)).getD (V b))

theorem fixed_normalized (U : CF St Blk) (V : Blk → St) :
    Fixed IV sb cv c (normalized IV sb cv c U V) := by
  intro p v hne hv
  by_cases h : p.1 = cv <;> simp [normalized,gstar,hne,select,h] at hv ⊢ <;> simp [hv]

theorem seed_normalized (U : CF St Blk) (V : Blk → St) :
    normalized IV sb cv c U V (IV,sb) = cv := by simp [normalized,gstar]
end Normalized

open OracleComp OracleSpec PQ.Interactive
open Wots256 (Node)
section ReaderCost
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable (table : (X → Y) → CF St Blk)
    (step : ∀ p, EvalCost (fun H => (pure (table H p) : ProbComp St)) 1)
local notation "Entry" => List ((St × Blk) × St)
local notation "obs" => fun H => observe IV sb cv c (table H)
include step in
private theorem walk_cost (s : St) (bs : List Blk) :
    EvalCost (fun H => (pure (mdFold (table H) s bs, walkLog (obs H) (table H) s bs) : ProbComp (St × Entry))) bs.length := by
  induction bs generalizing s with
  | nil => exact EvalCost.const (X := X) (Y := Y) (pure (s,([] : Entry)))
  | cons b bs ih =>
    let log := fun y : St => if (s,b) = (IV,sb) ∨ (c (select cv (s,b))).isSome then [] else [((s,b),y)]
    have hh := EvalCost.bind (step (s,b))
      (g := fun y H => (fun z : St × Entry => (z.1,log y ++ z.2)) <$>
        (pure (mdFold (table H) y bs,walkLog (obs H) (table H) y bs) : ProbComp (St × Entry)))
      (fun y => (ih y).map _)
    simpa only [log,walkLog,observe,mdFold,List.foldl_cons,map_pure,pure_bind,List.length_cons,Nat.add_comm 1] using hh

include step in
theorem path_cost (Xb : Blk × List Blk) :
    EvalCost (fun H => (pure (mdFold (table H) (table H (cv,Xb.1)) Xb.2,
      pathLog (obs H) (table H) cv Xb) : ProbComp (St × Entry))) (Xb.2.length+1) := by
  let log := fun y : St => if (cv,Xb.1) = (IV,sb) ∨ (c (select cv (cv,Xb.1))).isSome then [] else [((cv,Xb.1),y)]
  have hh := EvalCost.bind (step (cv,Xb.1))
    (g := fun y H => (fun z : St × Entry => (z.1,log y ++ z.2)) <$>
      (pure (mdFold (table H) y Xb.2,walkLog (obs H) (table H) y Xb.2) : ProbComp (St × Entry)))
    (fun y => (walk_cost (IV := IV) (sb := sb) (cv := cv) (c := c) table step y Xb.2).map _)
  simpa only [log,pathLog,observe,map_pure,pure_bind,Nat.add_comm 1] using hh
end ReaderCost

open SLHDSA MLink
variable (seeds : ProbComp Node) (ar n : ℕ)
local notation "fam" => ShortBlocks.family seeds ar n
local notation "L₀" => (22 + 16*ar + 8)/64
variable (pk₀ : Node) (cv₀ : Ideal.St) (c₀ : Cell Ideal.St Ideal.Blk → Option Ideal.St)
variable (U : CF Ideal.St Ideal.Blk) (V : Ideal.Blk → Ideal.St)
local notation "g₀" => normalized IV128 (sb128 pk₀) cv₀ c₀ U V
local notation "Log₀" => List ((Ideal.St × Ideal.Blk) × Ideal.St)
variable (qs₀ : List (Bytes 22 × ShortBlocks.Msg ar))
def report (jm : ℕ × ShortBlocks.Msg ar) : Bool × Log₀ :=
  match qs₀[jm.1]? with
  | none => (false,[])
  | some (t,m) =>
    (decide (jm.2 ≠ m ∧ out16 (keyedChain IV128 sb128 g₀ pk₀ (tblocks t jm.2.val)) =
      out16 (keyedChain IV128 sb128 g₀ pk₀ (tblocks t m.val))),
      comparisonLog fam pk₀ cv₀ c₀ g₀ t jm.2 m)

theorem report_length (jm : ℕ × ShortBlocks.Msg ar) :
    (report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm).2.length ≤ 2*(L₀+1) := by
  unfold report
  split
  · simp
  · exact comparison_length fam L₀ pk₀ cv₀ c₀ g₀
      (fun t m => (tblocks_snd_length t m.val).trans (by rw [m.property])) _ _ _

theorem bad_of_report (hcv : cv₀ ≠ IV128) {dst : Cell Ideal.St Ideal.Blk → Option Ideal.St}
    (he : CLe c₀ dst) (jm : ℕ × ShortBlocks.Msg ar)
    (hw : (report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm).1 = true)
    (hm : Matches cv₀ dst (report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm).2) :
    ¬ Good fam btw128 L₀ qs₀ cv₀ dst := by
  unfold report at hw hm
  split at hw
  · contradiction
  next x t m eq =>
    rw [eq] at hm
    obtain ⟨ne,win⟩ := of_decide_eq_true hw
    exact bad_of_comparison fam btw128 L₀ qs₀ pk₀ cv₀ c₀ g₀
      (fun t m => (tblocks_snd_length t m.val).trans (by rw [m.property]))
      (fun t m => btw128_tblocks t m.val) (fun _ _ _ e => Subtype.ext (tblocks_injective e).2)
      hcv (seed_normalized ..) (fixed_normalized cv₀ c₀ U V) he (List.mem_of_getElem? eq) ne win hm

theorem report_fresh (jm : ℕ × ShortBlocks.Msg ar) {p : Ideal.St × Ideal.Blk} {v : Ideal.St}
    (hm : (p,v) ∈ (report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm).2) :
    p ≠ (IV128,sb128 pk₀) ∧ c₀ (select cv₀ p) = none ∧ g₀ p = v := by
  unfold report at hm
  split at hm
  · simp at hm
  · obtain h|h := List.mem_append.mp hm <;> exact path_fresh h

theorem report_physical (jm : ℕ × ShortBlocks.Msg ar) {p : Ideal.St × Ideal.Blk} {v : Ideal.St}
    (hm : (p,v) ∈ (report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm).2) :
    rowRep U cv₀ V p = v := by
  obtain ⟨hp,hm,hv⟩ := report_fresh seeds ar n pk₀ cv₀ c₀ U V qs₀ jm hm
  by_cases hc : p.1 = cv₀ <;> simp only [select,hc,ite_true,ite_false] at hm <;>
    simpa only [normalized,gstar,rowRep,hp,hc,hm,ite_false,ite_true,Option.getD_none] using hv

theorem normalized_twice :
    normalized IV128 (sb128 pk₀) cv₀ c₀ g₀ (fun b => g₀ (cv₀,b)) = g₀ := by
  funext p
  by_cases hp : p = (IV128,sb128 pk₀)
  · simp [normalized,gstar,hp]
  by_cases hc : p.1 = cv₀
  · obtain ⟨s,b⟩ := p
    change s = cv₀ at hc
    subst s
    cases hm : c₀ (.inr b) <;> simp [normalized,gstar,hp,hm]
  · cases hm : c₀ (.inl p) <;> simp [normalized,gstar,hp,hc,hm]

theorem report_normalized (jm : ℕ × ShortBlocks.Msg ar) :
    report seeds ar n pk₀ cv₀ c₀ g₀ (fun b => g₀ (cv₀,b)) qs₀ jm =
      report seeds ar n pk₀ cv₀ c₀ U V qs₀ jm := by
  unfold report
  rw [normalized_twice]

theorem address_select (p : St × Blk) : address cv (select cv p) = p := by
  cases p with
  | mk s b => by_cases h : s = cv <;> simp [address,select,h]

set_option quotPrecheck false in
local notation "portTable" => fun (H : Input → Output) => normalized IV128 (sb128 pk₀) cv₀ c₀
  (tablesOf H).1 (fun b => (tablesOf H).1 (cv₀,b))

private theorem phys_step (p : Ideal.St × Ideal.Blk) :
    EvalCost (fun H => (pure (portTable H p) : ProbComp Ideal.St)) 1 := by
  by_cases hp : p = (IV128,sb128 pk₀)
  · simpa only [normalized,gstar,hp,ite_true] using
      (EvalCost.const (X := Input) (Y := Output) (pure cv₀)).mono (Nat.zero_le 1)
  by_cases hc : p.1 = cv₀
  · cases p with
    | mk s b =>
      change s = cv₀ at hc
      subst s
      simpa only [normalized,gstar,hp,ite_false,ite_true,tablesOf] using
        (EvalCost.eval (X := Input) (Y := Output) (.inl (cv₀,b)) (fun y => (c₀ (.inr b)).getD y.1))
  · simpa only [normalized,gstar,hp,hc,ite_false,tablesOf] using
      (EvalCost.eval (X := Input) (Y := Output) (.inl p) (fun y => (c₀ (.inl p)).getD y.1))

theorem report_cost (jm : ℕ × ShortBlocks.Msg ar) :
    EvalCost (fun H => (pure (report seeds ar n pk₀ cv₀ c₀ (tablesOf H).1
      (fun b => (tablesOf H).1 (cv₀,b)) qs₀ jm) : ProbComp (Bool × Log₀))) (2*(L₀+1)) := by
  unfold report
  split
  · exact (EvalCost.const (X := Input) (Y := Output) _).mono (Nat.zero_le _)
  next _ t m _ =>
    let Xb := tblocks t jm.2.val
    let Yb := tblocks t m.val
    let cost := fun (Z : Ideal.Blk × List Ideal.Blk) => path_cost
      (IV := IV128) (sb := sb128 pk₀) (c := c₀) (cv := cv₀) portTable (phys_step pk₀ cv₀ c₀) Z
    let combine := fun (a b : Ideal.St × Log₀) => (decide (jm.2 ≠ m ∧ out16 a.1 = out16 b.1),a.2 ++ b.2)
    have comb := EvalCost.bind (cost Xb) (g := fun a H => combine a <$>
      (pure (mdFold (portTable H) (portTable H (cv₀,Yb.1)) Yb.2,
         pathLog (observe IV128 (sb128 pk₀) cv₀ c₀ (portTable H)) (portTable H) cv₀ Yb) : ProbComp _))
      (fun a => (cost Yb).map _)
    have hl : (Xb.2.length + 1) + (Yb.2.length + 1) = 2*(L₀+1) := by
      dsimp [Xb,Yb]
      rw [tblocks_snd_length,tblocks_snd_length,jm.2.property,m.property]
      omega
    rw [hl] at comb
    simpa only [Xb,Yb,combine,comparisonLog,ShortBlocks.family,keyedChain,seed_normalized,pure_bind,map_pure] using comb

section Machine
variable {E : Type} [Fintype E] [DecidableEq E] {σ : Type}
local notation "W" => WS Input Output E
/-- Attaching the two-path verifier to an arbitrary port-uniform quantum
attacker adds the two path lengths, and logs exactly the unfixed reads. -/
theorem report_pue (mach : (Input → Output) → Closed W (ℕ × ShortBlocks.Msg ar))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 mach q) :
    PUE (spec := unifSpec) cnt0 (fun H => mach H >>= fun jm => pure (report seeds ar n pk₀ cv₀ c₀
      (tablesOf H).1 (fun b => (tablesOf H).1 (cv₀,b)) qs₀ jm)) (q+2*(L₀+1)) := by
  apply hq.bind
  intro jm
  have h := report_cost seeds ar n pk₀ cv₀ c₀ qs₀ jm E _ (fun a _ => pure a) 0 (fun a => PUE.pure a 0)
  simpa only [liftU_pure,pure_bind,Nat.zero_add] using h
end Machine

end Reduction.Compression.LongClass.Certificate
#print axioms Reduction.Compression.LongClass.Certificate.bad_of_report
#print axioms Reduction.Compression.LongClass.Certificate.report_pue
