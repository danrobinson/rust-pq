import Integration.SlhDsaCompressionForger
import Integration.SlhDsaCompressionForsSign

namespace Reduction.Compression
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg Resources2

theorem close_congr_on {ι σ α β W : Type} [Fintype W] {sp : OracleSpec ι}
    (a b : QueryImpl sp (StateT σ ProbComp)) {G : ι → Prop} {ok : α → Prop}
    (ha : ∀ t, G t → a t = b t) (ka kb : α × σ → Closed W β)
    (hk : ∀ x, ok x.1 → ka x = kb x) (P : QOC W sp α)
    (hp : AllQueries (QG W G) ok P) (s : σ) :
    (close a P s >>= ka) = (close b P s >>= kb) := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure x => simpa only [close_pure, pure_bind] using hk (x,s) hp
  | query_bind t k ih =>
    rcases t with j|t
    · simp only [close_instr_bind, bind_assoc]
      exact bind_congr fun i => ih i (hp.2 i) s
    · simp only [close_query_bind, bind_assoc, ha t hp.1]
      exact bind_congr fun x => ih x.1 (hp.2 x.1) x.2

private theorem hmsg_mono (S : Sha2Set) {a b : ℕ} (h : a ≤ b) : hmsgCalls S a ≤ hmsgCalls S b := by
  cases S <;> simp only [hmsgCalls] <;> omega

theorem signMax_mono (S : Sha2Set) {a b : ℕ} (h : a ≤ b) : signMax S a ≤ signMax S b :=
  max_le_max_left _ (hmsg_mono S h)

variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
variable {E : Type} [Fintype E] [DecidableEq E]
    (rand : S.Node → S.Node → ProbComp S.Node) (F : PortForger Input Output E)

abbrev PhaseState := SecretTable S.vp P₀ × List (Bytes 22 × S.Node) × List S.Node
abbrev SignState := G2Log P₀ × List ℕ × List (Adrs × ℕ)

private noncomputable def signClip (L : ℕ) (st : PhaseState S f) (pk root : S.Node) (H : Input → Output) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (SignState S f) ProbComp)
  | .inl n => fSignS (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 st.2.1 st.2.2 pk root (.inl n)
  | .inr m => fSignS (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 st.2.1 st.2.2 pk root (.inr (m.take L))

private theorem signClip_cost (L : ℕ) (st : PhaseState S f) (pk root : S.Node) (t) (s : SignState S f) :
    EvalCost (fun H => (signClip S f rand L st pk root H t).run s)
      (sgnW ((forsSignHashes S.vp+1)*signMax S L) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · let msg := m.take L
    change EvalCost (fun H => rand pk root >>= fun rnd => lazyRandomizer s.1 msg rnd >>= fun R =>
      (simulateQ (fImpl (hashPort S f H) st.1 st.2.1) (fSignOpen ⟨pk,root⟩ st.2.2 msg R)).run s.2.1 >>=
      fun r => (pure (r.1.1, (s.1 ++ [(msg,rnd,R)],r.2,s.2.2 ++ r.1.2)) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (rand pk root)) fun rnd =>
      EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (lazyRandomizer s.1 msg rnd)) fun R =>
        EvalCost.bind (forsSign_cost S f st.1 st.2.1 ⟨pk,root⟩ st.2.2 msg R s.2.1) fun r =>
          EvalCost.const (X := Input) (Y := Output)
            (pure (r.1.1, (s.1 ++ [(msg,rnd,R)],r.2,s.2.2 ++ r.1.2)) : ProbComp _)
    apply h.mono
    simp only [Nat.zero_add, Nat.add_zero, sgnW]
    exact Nat.mul_le_mul_left _ (signMax_mono S (by simp [msg]))

def forsBudget (L q qs : ℕ) := Lazy.keygenHashes S.vp * keygenMax S + q +
    qs * ((forsSignHashes S.vp+1)*signMax S L) + hmsgCalls S L + S.vp.params.k*thashCalls S 1

noncomputable def phaseMachine (st : PhaseState S f) (pk : S.Node) (H : Input → Output) :=
  fRun (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) (mainAt S f F H) st pk

private noncomputable def answer (st : PhaseState S f) (pk root : S.Node) (H : Input → Output)
    (s : SignState S f) (m : List Byte) (sig : GeneralScheme.SignatureCore S.vp (P₀).core) :
    ProbComp ((ℕ × S.Node) × List ℕ) := (simulateQ (fImpl (hashPort S f H) st.1 st.2.1)
      (fAnswerO ⟨pk,root⟩ st.2.2 s.2.2 m sig)).run s.2.1

theorem phaseMachine_pue (c : Caps) (st : PhaseState S f) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (phaseMachine S f rand F st pk) (forsBudget S c.ml q qs) := by
  let K := (forsSignHashes S.vp + 1) * signMax S c.ml
  let V := hmsgCalls S c.ml + S.vp.params.k * thashCalls S 1
  let work := fun (root : S.Node) (H : Input → Output) =>
    close (signClip S f rand c.ml st pk root H) (mainAt S f F H ⟨pk,root⟩) ([], [], []) >>= fun z =>
      (liftU (answer S f st pk root H z.2 (z.1.1.take c.ml) z.1.2) : Closed (WS Input Output E) _)
  have hwork (root : S.Node) : PUE (spec := unifSpec) cnt0 (work root) (q + qs*K + V) := by
    refine PUE.bind (PUE.close _ (signClip_cost S f rand c.ml st pk root)
      (mainAt_pue S f F q qs K hq hs ⟨pk,root⟩) _) fun z => ?_
    have hv := (forsAnswer_cost S f st.1 st.2.1 ⟨pk,root⟩ st.2.2 z.2.2.2 (z.1.1.take c.ml)
      z.1.2 z.2.2.1).mono (Nat.add_le_add_right (hmsg_mono S (by simp : (z.1.1.take c.ml).length ≤ c.ml)) _)
    have hv' := PUE.liftU_bind (E := E) (q := 0)
      (B := fun o _ => (pure o : Closed (WS Input Output E) _)) hv (fun o => PUE.pure o 0)
    simpa only [bind_pure, Nat.zero_add, answer, V] using hv'
  have hw := PUE.liftU_bind (keygen_cost S f st.1 pk) hwork
  have same : phaseMachine S f rand F st pk = fun H =>
      liftU (simulateQ (qmImpl (hashPort S f H) st.1) (Lazy.openKeygen P₀ []ₒ pk)) >>= fun root => work root H := by
    funext H
    unfold phaseMachine fRun
    apply bind_congr
    intro root
    apply close_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (n|m) ht
      · rfl
      · change m.length ≤ c.ml at ht
        exact congrArg (β := StateT (SignState S f) ProbComp (GeneralScheme.SignatureCore S.vp (P₀).core))
          (fun m : List Byte => fSignS (fun k => rand k.pkSeed k.pkRoot)
          (hashPort S f H) st.1 st.2.1 st.2.2 pk root (.inr m)) (List.take_of_length_le ht).symm
    · intro z hz
      simp only [answer, List.take_of_length_le hz]
    · exact mainAt_cap S f F c hc H ⟨pk,root⟩
  rw [same]
  apply hw.mono
  dsimp only [forsBudget,K,V]
  omega

end Reduction.Compression
#print axioms Reduction.Compression.phaseMachine_pue
