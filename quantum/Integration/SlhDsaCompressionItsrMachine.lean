import Integration.SlhDsaCompressionItsrTransport

namespace Reduction.Compression.MessageHash
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
local notation "Game" => Lazy.itsrG P₀
local notation "OS" => Lazy.OSpec P₀ Game
local notation "Sig" => GeneralScheme.SignatureCore (Sha2Set.vp S) (Primitives.core (randPrims f))
local notation "SG" => unifSpec + (List Byte →ₒ Sig)
local notation "Wc" => openWeight S f Game

private theorem hash_count {α : Type} (P : OracleComp OS α) (q B : ℕ)
    (hh : IsQueryBoundP P (fun t => Lazy.kind t = .hash) q)
    (hc : IsQueryBoundP P (fun t => B < Wc t) 0) : WCount Wc P (q*B) := by
  exact cappedCount Wc (fun t => Lazy.kind t = .hash) B
    (fun t h => by rcases t with n|g|d|h' <;> first | rfl | exact (h rfl).elim) _ _ hh hc

private theorem len_cap {L : ℕ} (pk : S.Node) (key : Bytes 22) (xs : List S.Node)
    (hx : Realize.OkLen S.vp xs) :
    ¬signMax S L < Wc (Realize.thIdx P₀ _ pk key xs) := by
  change ¬signMax S L < thashCalls S xs.length
  rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega

private theorem key_cost (pk : S.Node) :
    WCount Wc (Lazy.openKeygen P₀ Game pk) (Lazy.keygenHashes S.vp * signMax S 0) := by
  apply hash_count
  · exact (Lazy.openKeygen_kindBound (vp := S.vp) (prims := P₀) (gspec := Game) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp))
  · apply Realize.np_openKeygen
    · exact fun _ => Nat.not_lt_zero _
    · exact len_cap S f pk

private theorem sign_count (m : List Byte) (pk root R : S.Node) :
    WCount Wc (Lazy.openSign P₀ Game m pk root R) (Lazy.signHashes S.vp * signMax S m.length) := by
  apply hash_count
  · exact (Lazy.openSign_kindBound (vp := S.vp) (prims := P₀) (gspec := Game) .hash m pk root R).mono
      (by simpa [Lazy.ind] using Lazy.signB_hash (vp := S.vp))
  · apply Realize.np_openSign
    · exact fun _ => Nat.not_lt_zero _
    · exact len_cap S f pk
    · exact not_lt_of_ge (le_max_right ..)

private theorem sample_free {α : Type} (p : ProbComp α) : WCount Wc (liftM p : OracleComp OS α) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [liftM_pure]; exact trivial
  | query_bind i k ih =>
    rw [liftM_bind]
    exact WCount.bind (n := 0) (m := 0) (wCount_liftM_query (sp := OS) _ (.inl i) le_rfl) ih

variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
local notation "Work" => WS Input Output E
noncomputable def signer (pk : PublicKeyCore (P₀).core) :
    QueryImpl SG (StateT (G2Log P₀) (OracleComp OS)) :=
  (QueryImpl.ofLift unifSpec (OracleComp OS)).liftTarget (StateT (G2Log P₀) (OracleComp OS)) +
      logSignOracle (fun pk => r pk.pkSeed pk.pkRoot) pk (Lazy.itsrRandomizerO pk.pkSeed pk.pkRoot)
        (fun m R => Lazy.openSign P₀ Game m pk.pkSeed pk.pkRoot R)

private noncomputable def clip (L : ℕ) (pk : PublicKeyCore (P₀).core) :
    QueryImpl SG (StateT (G2Log P₀) (OracleComp OS))
  | .inl n => signer S f r pk (.inl n)
  | .inr m => signer S f r pk (.inr (m.take L))

private theorem clip_count (L : ℕ) (pk : PublicKeyCore (P₀).core) (t : (SG).Domain) (s : G2Log P₀) :
    WCount Wc ((clip S f r L pk t).run s) (sgnW (Lazy.signHashes S.vp * signMax S L) t) := by
  rcases t with n|m
  · exact WCount.map (wCount_liftM_query (sp := OS) Wc (.inl n) le_rfl) (fun r => (r,s))
  · let msg := m.take L
    have rand (v) : WCount Wc (Lazy.itsrRandomizerO (prims := P₀) pk.pkSeed pk.pkRoot s msg v) 0 := by
      unfold Lazy.itsrRandomizerO
      split
      · exact trivial
      · exact wCount_liftM_query (sp := OS) Wc (.inr (.inl _)) le_rfl
    have h := WCount.bind (sample_free S f (r pk.pkSeed pk.pkRoot)) fun v =>
      WCount.bind (rand v) fun R => WCount.bind (sign_count S f msg pk.pkSeed pk.pkRoot R)
        (m := 0) fun sig => wCount_pure Wc (sig,s ++ [(msg,v,R)]) 0
    simp only [Nat.zero_add,Nat.add_zero] at h
    have hh := h.mono (Nat.mul_le_mul_left (Lazy.signHashes S.vp) (signMax_mono S (List.length_take_le L m)))
    simpa [clip,signer,sgnW,logSignOracle,msg] using hh

def machineBudget (L q qs : ℕ) := Lazy.keygenHashes S.vp * signMax S 0 + q + qs * (Lazy.signHashes S.vp * signMax S L)

private theorem open_cost (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE Wc (fun H => qmItsrOpen (fun pk => r pk.pkSeed pk.pkRoot) seeds (mainAt S f F H))
      (machineBudget S c.ml q qs) := by
  let K := Lazy.signHashes S.vp * signMax S c.ml
  let extract := fun (pk : PublicKeyCore (P₀).core) (z : (List Byte × Sig) × G2Log P₀) =>
    (z.1.2.randomness,(pk.pkSeed,pk.pkRoot,z.1.1))
  let work := fun (pk : PublicKeyCore (P₀).core) (H : Input → Output) =>
    extract pk <$> wrap (clip S f r c.ml pk) (mainAt S f F H pk) []
  have hw (pk) : PUE Wc (work pk) (q + qs*K) :=
    PUE.map _ (PUE.wrap _ (clip_count S f r c.ml pk) (mainAt_pue S f F q qs K hq hs pk) [])
  have eq : (fun H => qmItsrOpen (fun pk => r pk.pkSeed pk.pkRoot) seeds (mainAt S f F H)) =
      fun H => liftQ (liftM seeds : OracleComp OS S.Node) >>= fun pk =>
        liftQ (Lazy.openKeygen P₀ Game pk) >>= fun root => work ⟨pk,root⟩ H := by
    funext H
    unfold qmItsrOpen
    apply bind_congr
    intro pk
    apply bind_congr
    intro root
    simp only [work,map_eq_bind_pure_comp,Function.comp_def,liftQ_pure]
    apply HmacKey.wrap_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (n|m) ht
      · rfl
      · change m.length ≤ c.ml at ht
        rw [clip,List.take_of_length_le ht]
        rfl
    · intro z _; rfl
    · exact mainAt_cap S f F c hc H ⟨pk,root⟩
  rw [eq]
  have h := PUE.liftQ_bind _ (sample_free S f seeds) fun pk => PUE.liftQ_bind _ (key_cost S f pk)
    fun root => hw ⟨pk,root⟩
  exact h.mono (by dsimp only [K,machineBudget]; omega)

private def weightU : (Lazy.RSpec Game Unit (P₀).Y (publicHashSpec (P₀).core)).Domain → ℕ
  | .inr (.inr (.inr h)) => hashCalls S f h
  | _ => 0

theorem machine_cost (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (fun _ => 0) (machine S f r seeds F) (machineBudget S c.ml q qs) := by
  unfold machine qLazyRun
  refine PUE.wrap0E (fun H => Lazy.interp (hashPort S f H)) (cnt := weightU S f) ?_
    (PUE.map _ (PUE.wrap _ (cnt := Wc) ?_ (open_cost S f r seeds F c q qs hq hs hc) []))
  · rintro (n|d|u|hash)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact HmacKey.pureEvalQ (fun _ => 0) (fun _ => rfl) _ (hashPort_cost S f hash)
  · let sp := Lazy.RSpec Game Unit S.Node (publicHashSpec (P₀).core)
    rintro (n|d|a|hash) s
    · exact WCount.map (wCount_liftM_query (sp := sp) (weightU S f) (.inl n) le_rfl) (fun x => (x,s))
    · exact WCount.map (wCount_liftM_query (sp := sp) (weightU S f) (.inr (.inl d)) le_rfl) (fun x => (x,s))
    · cases hl : s.lookup a with
      | some b => rw [Lazy.lazyImplR_sec_run_hit a s b hl]; exact trivial
      | none => rw [Lazy.lazyImplR_sec_run_miss a s hl]; exact WCount.map (wCount_liftM_query (sp := sp) (weightU S f) (.inr (.inr (.inl ()))) le_rfl) (fun x => (x,(a,x)::s))
    · exact WCount.map (wCount_liftM_query (sp := sp) (weightU S f) (.inr (.inr (.inr hash))) le_rfl) (fun x => (x,s))
end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.machine_cost
