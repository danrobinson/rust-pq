import Integration.SlhDsaCompressionHmacWork
import Integration.SlhDsaCompressionPrfBudget

/-! Run the pure byte forger in the open message-PRF game. The bounds on its
encoded messages cap the signing and final verification costs. -/
namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
variable (S : Sha2Set) (f : RandFns S.vp.params) {E : Type} [Fintype E] [DecidableEq E]
local notation "P₀" => randPrims f
local notation "Work" => WS Input Output E
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)
local notation "Sig" => GeneralScheme.SignatureCore (Sha2Set.vp S) (Primitives.core (randPrims f))
local notation "SG" => unifSpec + (List Byte →ₒ Sig)
local notation "Wc" => openCharge S f SecIdx
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : PortForger Input Output E)

private theorem wrap_congr_on {ι κ σ α β W : Type} [Fintype W] {sp : OracleSpec ι} {sp' : OracleSpec κ}
    (a b : QueryImpl sp (StateT σ (OracleComp (unifSpec + sp')))) {G : ι → Prop} {ok : α → Prop}
    (ha : ∀ t, G t → a t = b t) (ka kb : α × σ → QOC W (unifSpec + sp') β)
    (hk : ∀ x, ok x.1 → ka x = kb x) (P : QOC W sp α)
    (hp : AllQueries (QG W G) ok P) (s : σ) :
    (wrap a P s >>= ka) = (wrap b P s >>= kb) := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure x => simpa only [wrap_pure, pure_bind] using hk (x,s) hp
  | query_bind t k ih =>
    rcases t with j|t
    · simp only [wrap_instr_bind, bind_assoc]
      exact bind_congr fun i => ih i (hp.2 i) s
    · simp only [wrap_query_bind, bind_assoc, ha t hp.1]
      exact bind_congr fun x => ih x.1 (hp.2 x.1) x.2

noncomputable def signImpl (pk : PublicKeyCore (P₀).core) :
    QueryImpl SG (StateT (SigLog S.vp P₀) (OracleComp OS)) :=
  (QueryImpl.ofLift unifSpec (OracleComp OS)).liftTarget (StateT (SigLog S.vp P₀) (OracleComp OS)) +
    sigSignOracle (Lazy.msgSignO (fun k => rand k.pkSeed k.pkRoot) pk)

private noncomputable def clip (L : ℕ) (pk : PublicKeyCore (P₀).core) :
    QueryImpl SG (StateT (SigLog S.vp P₀) (OracleComp OS))
  | .inl n => signImpl S f rand pk (.inl n)
  | .inr m => signImpl S f rand pk (.inr (m.take L))

private theorem clip_cost (L : ℕ) (pk : PublicKeyCore (P₀).core) (t : (SG).Domain)
    (log : SigLog S.vp P₀) :
    WCount Wc ((clip S f rand L pk t).run log) (sgnW (signCharge S L) t) := by
  rcases t with n|m
  · exact WCount.map (wCount_liftM_query (sp := OS) Wc (.inl n) le_rfl) (fun x => (x,log))
  · simp only [clip,signImpl,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    have h := WCount.bind (sign_count S f (fun k => rand k.pkSeed k.pkRoot) pk (m.take L))
      (m := 0) fun sig => wCount_pure Wc (sig,log ++ [⟨m.take L,sig⟩]) 0
    apply h.mono
    have le := List.length_take_le L m
    change signCharge S (m.take L).length + 0 ≤ signCharge S L
    unfold signCharge
    have mul := Nat.mul_le_mul_left (Lazy.signHashes S.vp) (signMax_mono S le)
    omega

noncomputable def verdict (H : Input → Output) (pk : PublicKeyCore (P₀).core)
    (z : (List Byte × Sig) × SigLog S.vp P₀) : Bool :=
  simulateQ (hashPort S f H) (sufCheckOpen pk z.1 z.2)

private theorem verdict_cost (pk : PublicKeyCore (P₀).core) (z : (List Byte × Sig) × SigLog S.vp P₀) :
    EvalCostQ E Wc (fun H => (pure (verdict S f H pk z) : OracleComp OS Bool))
      ((1 + Resources2.verifyHashes S.vp) * signMax S z.1.1.length) := by
  apply pureEvalQ Wc (fun _ => rfl)
  have hi (H : Input → Output) : (fun t => pure (hashPort S f H t) : QueryImpl _ ProbComp) =
      (hashPort S f H).liftTarget ProbComp := by funext t; rfl
  have h := SkGame.check_cost S f pk z.1 z.2
  simp only [hi,simulateQ_liftTarget] at h
  kexact h

noncomputable def openMachine (H : Input → Output) : QOC Work OS Bool := do
  let pk ← liftQ (liftM seeds : OracleComp OS S.Node)
  let root ← liftQ (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk)
  let z ← wrap (signImpl S f rand ⟨pk,root⟩) (mainAt S f F H ⟨pk,root⟩) []
  pure (verdict S f H ⟨pk,root⟩ z)

/-- Compression and message-oracle budget for key generation, the forger,
the signing requests, and the final verification. -/
def budget (L q qs : ℕ) := Lazy.keygenHashes S.vp * signMax S 0 + q + qs * signCharge S L +
  (1 + Resources2.verifyHashes S.vp) * signMax S L

theorem openMachine_cost (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE Wc (openMachine S f rand seeds F) (budget S c.ml q qs) := by
  let V := (1 + Resources2.verifyHashes S.vp) * signMax S c.ml
  let K := signCharge S c.ml
  let work := fun (pk : PublicKeyCore (P₀).core) (H : Input → Output) =>
    wrap (clip S f rand c.ml pk) (mainAt S f F H pk) [] >>= fun z =>
      (pure (verdict S f H pk ((z.1.1.take c.ml,z.1.2),z.2)) : QOC Work OS Bool)
  have hw (pk) : PUE Wc (work pk) (q + qs*K + V) := by
    apply PUE.bind (PUE.wrap _ (clip_cost S f rand c.ml pk) (mainAt_pue S f F q qs K hq hs pk) [])
    intro z
    have ev := (verdict_cost (E := E) S f pk ((z.1.1.take c.ml,z.1.2),z.2)).mono
      (Nat.mul_le_mul_left _ (signMax_mono S (List.length_take_le c.ml z.1.1)))
    have h := ev Bool (fun b _ => (pure b : QOC Work OS Bool)) 0 (fun b => PUE.pure b 0)
    simpa only [liftQ_pure,pure_bind,Nat.zero_add,V] using h
  have eq : openMachine S f rand seeds F = fun H => liftQ (liftM seeds : OracleComp OS S.Node) >>= fun pk =>
      liftQ (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk) >>= fun root => work ⟨pk,root⟩ H := by
    funext H
    apply bind_congr
    intro pk
    apply bind_congr
    intro root
    apply wrap_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (n|m) ht
      · rfl
      · change m.length ≤ c.ml at ht
        exact congrArg (β := StateT (SigLog S.vp P₀) (OracleComp OS) Sig)
          (fun m => signImpl S f rand ⟨pk,root⟩ (.inr m)) (List.take_of_length_le ht).symm
    · intro z hz
      simp only [List.take_of_length_le hz]
    · exact mainAt_cap S f F c hc H ⟨pk,root⟩
  rw [eq]
  have h := PUE.liftQ_bind _ (open_sample S f seeds) fun pk => PUE.liftQ_bind _ (keygen_count S f pk)
    fun root => hw ⟨pk,root⟩
  exact h.mono (by dsimp only [K,V,budget]; omega)

noncomputable def machine (H : Input → Output) :=
  qLazyRun (hashPort S f H) (openMachine S f rand seeds F H)

theorem machine_cost (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (messageCharge S) (machine S f rand seeds F) (budget S c.ml q qs) :=
  lazy_cost S f _ _ (openMachine_cost S f rand seeds F c q qs hq hs hc)

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.machine_cost
