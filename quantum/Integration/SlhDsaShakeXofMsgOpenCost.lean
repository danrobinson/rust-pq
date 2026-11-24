import Integration.SlhDsaShakeXofMsgOpen

namespace Reduction.ShakeApi.Msg.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg QItsr
open ShakePermutation.Honest (RawSpec)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
local notation "Raw" => RawSpec S N
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)
local notation "OSU" => Lazy.RSpec (Lazy.msgG P₀) Unit S.Node (publicHashSpec (Primitives.core (primitives S base)))
local notation "Wc" => Msg.hashWeight S base SecIdx
local notation "Wu" => Msg.hashWeight S base Unit
local notation "rawWt" => ShakePermutation.Honest.hashWeight
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
local notation "Work" => WS (Input N) (Bytes S.vp.params.m) E

private theorem prefix_public (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) :
    PU (beforeCheck S N base rand seeds F) q := by
  apply PU.liftQ_bind
  intro pk
  apply PU.liftQ_bind
  intro root
  simpa only [Nat.add_zero] using PU.bind (PU.wrap _ (Sk.Mixed.forger_public S N base F _ q hq) [])
    (q₂ := 0) (fun z => PU.pure _ 0)

theorem public_cost (c : Caps) (a : ShakeXof.MsgDomain S c.ml → S.Node) (q : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) :
    PU (machine S N rand seeds F c a) q := by
  unfold machine interpreted
  simpa only [Nat.add_zero] using PU.bind
    (PU.wrap0 _ (PU.map _ (PU.wrap _ (prefix_public S N _ rand seeds F q hq) [])))
    (q₂ := 0) (fun z => PU.liftQ (E := E) _ 0)

private theorem prefix_reads (s : ℕ) (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : RawTable S N) :
    WCount (qw Work Wc) (beforeCheck S N base rand seeds F H) (Lazy.keygenHashes S.vp+s*Lazy.signHashes S.vp) := by
  unfold beforeCheck
  nth_rewrite 1 [← Nat.zero_add (Lazy.keygenHashes S.vp+_)]
  refine WCount.bind (WCount.liftQ (wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) seeds))) fun pk => ?_
  have hk := wCount_of_isQueryBoundP _ _ _
    ((Lazy.openKeygen_kindBound (prims := P₀) (gspec := Lazy.msgG P₀) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp)))
  refine WCount.bind (WCount.liftQ hk) fun root => ?_
  nth_rewrite 1 [← Nat.add_zero (s*Lazy.signHashes S.vp)]
  refine WCount.bind (WCount.wrap _ (Msg.signCost S base rand _)
    (Sk.Mixed.forger_signs S N base F _ _ s hs H) []) fun _ => wCount_pure _ _ _

private theorem lazy_reads (t : (OS).Domain) (cache) :
    WCount Wu ((Lazy.lazyImplR (gspec := Lazy.msgG P₀) (hspec := publicHashSpec (P₀).core) t).run cache) (Wc t) := by
  refine wCount_of_isQueryBoundP _ _ _ ?_
  rcases t with n|d|a|h
  · simp [Lazy.lazyImplR,Lazy.kind]
  · simp [Lazy.lazyImplR,Lazy.kind]
  · rcases hc : cache.lookup a with _|v
    · rw [Lazy.lazyImplR_sec_run_miss a cache hc]; simp [Lazy.kind]
    · rw [Lazy.lazyImplR_sec_run_hit a cache v hc]; simp
  · simp [Lazy.lazyImplR,Lazy.kind,Msg.hashWeight]

private theorem raw_reads (a : S.Node × List SLHDSA.Byte → S.Node) (t : (OSU).Domain) :
    WCount rawWt (rawEnd S N base a t) (Wu t) := by
  rcases t with n|d|u|h
  · exact wCount_liftM_query _ _ le_rfl
  · trivial
  · change WCount rawWt (liftM ($ᵗ S.Node : ProbComp S.Node) : OracleComp Raw _) 0
    generalize ($ᵗ S.Node : ProbComp S.Node) = P
    induction P using OracleComp.inductionOn with
    | pure => trivial
    | query_bind n k ih =>
      rw [liftM_bind]
      exact WCount.bind (wCount_liftM_query (sp := Raw) rawWt (.inl n) le_rfl) ih
  · exact Sk.Mixed.public_count S N base h

theorem read_cost (c : Caps) (a : ShakeXof.MsgDomain S c.ml → S.Node) (s : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : RawTable S N) :
    CountBound (QC Work isR) (machine S N rand seeds F c a H) (Msg.budget S 0 s) := by
  apply (countBound_iff_wCount _ _ _).2
  apply WCount.wmono (w' := qw Work (spec := Raw) rawWt) (fun t => by rcases t with j|n|x <;> rfl)
  unfold machine interpreted Msg.budget
  simp only [Nat.add_zero]
  refine WCount.bind (WCount.wrap0 _ (raw_reads S N _ _)
    (WCount.map (WCount.wrap _ (lazy_reads S _) (prefix_reads S N _ rand seeds F s hs H) []) _)) fun z => ?_
  exact WCount.liftQ (Sk.Mixed.check_count S N _ z.1 z.2.1 z.2.2)

end Reduction.ShakeApi.Msg.Mixed
#print axioms Reduction.ShakeApi.Msg.Mixed.public_cost
#print axioms Reduction.ShakeApi.Msg.Mixed.read_cost
