import Integration.SlhDsaShakePermutationHonestTransport
import Integration.SlhDsaCompressionBudget

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec Ideal.Realize Quantum PQ.Interactive
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (base : Xof S) (L : ℕ)
local notation "P₀" => ShakeApi.primitives S base
local notation "ROM" => unifSpec + hashSpec (Primitives.core (ShakeApi.primitives S base))

def over : (ROM).Domain → Prop
  | .inl _ => False
  | .inr (.inl (.thash _ _ xs)) => ¬ OkLen S.vp xs
  | .inr (.inl (.hmsg _ _ _ m)) => L < m.length
  | .inr (.inr q) => L < q.msg.length

local notation "p" => over S base L
local instance : DecidablePred p := fun t => by
  rcases t with n | (q|q)
  · exact isFalse id
  · cases q <;> unfold over <;> infer_instance
  · exact Nat.decLt _ _

private theorem query_ok {t : (ROM).Domain} (h : ¬ p t) :
    IsQueryBoundP (liftM ((ROM).query t) : OracleComp ROM _) p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun a => (h a).elim

private theorem okF (pk : S.Node) (a : Adrs) (x : S.Node) :
    IsQueryBoundP (PublicHash.f (P₀).core pk a x : OracleComp ROM _) p 0 :=
  query_ok S base L (fun h => h (Or.inl rfl))

private theorem okH (pk : S.Node) (a : Adrs) (x y : S.Node) :
    IsQueryBoundP (PublicHash.h (P₀).core pk a x y : OracleComp ROM _) p 0 :=
  query_ok S base L (fun h => h (Or.inr (Or.inl rfl)))

private theorem okT (pk : S.Node) (a : Adrs) (xs : List S.Node)
    (h : xs.length = S.vp.params.len ∨ xs.length = S.vp.params.k) :
    IsQueryBoundP (PublicHash.tl (P₀).core pk a xs : OracleComp ROM _) p 0 :=
  query_ok S base L (fun bad => bad (Or.inr (Or.inr h)))

private theorem key_ok (pk sk : S.Node) :
    IsQueryBoundP (GeneralScheme.keygenInternalWithSecretM (vp := S.vp) (P₀).core
      (oracleSecret (P₀).core (Equiv.refl _) pk sk) pk : OracleComp ROM S.Node) p 0 :=
  np_xmssNode p (P₀).core (hash := PublicHash.f (P₀).core pk) (compress := PublicHash.tl (P₀).core pk)
    (nodeHash := PublicHash.h (P₀).core pk) (secret := oracleSecret (P₀).core (Equiv.refl _) pk sk)
    (okF S base L pk) (okT S base L pk) (okH S base L pk) (fun a => okF S base L pk a sk) _ _ _

private theorem sign_ok (sk : SecretKeyCore (P₀).core) (r : S.Node) (m : List SLHDSA.Byte) (hm : m.length ≤ L) :
    IsQueryBoundP (GeneralScheme.signInternalWithSecretRandomizerM (P₀).core
      (oracleSecret (P₀).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r :
        OracleComp ROM (GeneralScheme.SignatureCore S.vp (P₀).core)) p 0 := by
  have hf := okF S base L sk.pkSeed
  have ht := okT S base L sk.pkSeed
  have hh := okH S base L sk.pkSeed
  have hs (a) : IsQueryBoundP (oracleSecret (P₀).core (Equiv.refl _) sk.pkSeed sk.skSeed a : OracleComp ROM _) p 0 := hf a _
  have hd : IsQueryBoundP (PublicHash.hmsg (P₀).core r sk.pkSeed sk.pkRoot m : OracleComp ROM _) p 0 :=
    query_ok S base L (Nat.not_lt.mpr hm)
  unfold GeneralScheme.signInternalWithSecretRandomizerM
  exact isQueryBoundP_bind_zero _ _ hd fun digest =>
    isQueryBoundP_bind_zero _ _ (np_forsSign p (P₀).core hf hh hs _ _) fun forsSig =>
      isQueryBoundP_bind_zero _ _ (np_forsPk p (P₀).core hf ht hh forsSig _ _) fun forsPk =>
        isQueryBoundP_bind_zero _ _ (np_signFromPos p (P₀).core hf ht hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _

private theorem verify_ok (pk : PublicKeyCore (P₀).core) (s : GeneralScheme.SignatureCore S.vp (P₀).core)
    (m : List SLHDSA.Byte) (hm : m.length ≤ L) :
    IsQueryBoundP (GeneralScheme.verifyInternalM S.vp (P₀).core m s pk : OracleComp ROM _) p 0 := by
  have hf := okF S base L pk.pkSeed
  have ht := okT S base L pk.pkSeed
  have hh := okH S base L pk.pkSeed
  have hd : IsQueryBoundP (PublicHash.hmsg (P₀).core s.randomness pk.pkSeed pk.pkRoot m : OracleComp ROM _) p 0 :=
    query_ok S base L (Nat.not_lt.mpr hm)
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  exact isQueryBoundP_bind_zero _ _ hd fun digest =>
    isQueryBoundP_bind_zero _ _ (np_forsPk p (P₀).core hf ht hh _ _ _) fun forsPk =>
      isQueryBoundP_bind_zero _ _ (np_recover p (P₀).core hf ht hh pk.pkSeed S.vp.params.d _ _ _ _)
      fun root => isQueryBoundP_pure _ _ _

private theorem uniform_ok {α : Type} (u : ProbComp α) : IsQueryBoundP (liftM u : OracleComp ROM α) p 0 := by
  induction u using OracleComp.inductionOn with
  | pure => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftM_bind]
    exact isQueryBoundP_bind_zero _ _ (query_ok S base L (t := .inl t) (fun h => h)) ih


variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
local notation "A" => pureBytesRomScheme S base (ShakeApi.signRand S rand base) seeds

private theorem bytes_key_ok : IsQueryBoundP (A).keygen p 0 := by
  change IsQueryBoundP (_ <$> ((romScheme (vp := S.vp) (P₀).core (Equiv.refl _) (ShakeApi.signRand S rand base) seeds).keygen)) _ _
  rw [isQueryBoundP_map_iff,romScheme_keygen]
  exact isQueryBoundP_bind_zero _ _ (uniform_ok S base L seeds) fun pk =>
    isQueryBoundP_bind_zero _ _ (uniform_ok S base L ($ᵗ S.Node)) fun sk =>
      isQueryBoundP_bind_zero _ _ (uniform_ok S base L ($ᵗ S.Node)) fun pr =>
        isQueryBoundP_bind_zero _ _ (key_ok S base L pk sk) fun root => isQueryBoundP_pure _ _ _

private theorem msg_len (mc : ByteMessage) (h : mc.1.length + mc.2.length + 2 ≤ L)
    (m : List SLHDSA.Byte) (hm : pureEncode mc = .ok m) : m.length ≤ L := by
  rw [((encodePureMessage_ok_iff mc.2 mc.1 m).1 hm).2]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

private theorem bytes_sign_ok (pk sk : List SLHDSA.Byte) (mc : ByteMessage) (h : mc.1.length + mc.2.length + 2 ≤ L) :
    IsQueryBoundP ((A).sign pk sk mc) p 0 := by
  dsimp only [pureBytesRomScheme]
  split
  · split
    · apply isQueryBoundP_bind_zero _ _ (uniform_ok S base L _)
      intro r
      unfold romSignPureBytes
      split
      · cases hm : pureEncode (mc.1,mc.2) with
        | error e => exact isQueryBoundP_pure _ _ _
        | ok m =>
          rw [isQueryBoundP_map_iff]
          have hm' := msg_len L mc h m hm
          unfold romSignAt
          exact isQueryBoundP_bind_zero _ _ (query_ok S base L (Nat.not_lt.mpr hm'))
            (fun R => sign_ok S base L _ R _ hm')
      · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

private theorem bytes_verify_ok (pk : List SLHDSA.Byte) (mc : ByteMessage) (sig : ByteSig)
    (h : mc.1.length + mc.2.length + 2 ≤ L) : IsQueryBoundP ((A).verify pk mc sig) p 0 := by
  dsimp only [pureBytesRomScheme]
  split
  · split
    · dsimp only [pureRomScheme,E2E.GuardedRom.scheme]
      cases hm : pureEncode mc with
      | error e => exact isQueryBoundP_pure _ _ _
      | ok m => exact verify_ok S base L _ _ m (msg_len L mc h m hm)
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

private theorem run_congr {ι α : Type} {sp : OracleSpec ι} (P : OracleComp sp α) {bad : ι → Prop}
    [DecidablePred bad] (hP : IsQueryBoundP P bad 0) (f g : QueryImpl sp ProbComp)
    (hg : ∀ t, ¬ bad t → f t = g t) : simulateQ f P = simulateQ g P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    have ht := hP.1.resolve_right (by decide)
    simp only [simulateQ_bind,simulateQ_spec_query,hg t ht]
    exact bind_congr fun x => ih x (by simpa only [if_neg ht] using hP.2 x)

variable (N : ℕ) (cap : ShakeApi.rawCap S 67 L ≤ N)
local notation "H" => ShakeApi.restrict S N base
open Compression.SkGame (answerImpl)

include cap in
private theorem close_step (t : (ROM).Domain) (h : ¬ p t) :
    (answerImpl H ∘ₛ rawImpl S N base) t = unifFwdAnswerImpl (romAnswer P₀) t := by
  have lenBound (xs : List S.Node) (hx : OkLen S.vp xs) : xs.length ≤ 67 := by
    rcases hx with h|h|h|h
    · omega
    · omega
    · rw [h]; cases S <;> decide
    · rw [h]; cases S <;> decide
  obtain ⟨ht,_,hpm,hh⟩ := ShakeApi.in_range S 67 L N cap
  rcases t with u | (q|q)
  · exact simulateQ_spec_query _ _
  · cases q with
    | thash pk a xs =>
      have hx : OkLen S.vp xs := Classical.byContradiction h
      simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inr,rawHash,simulateQ_map,runRead,map_pure]
      rw [ShakeApi.extend_restrict _ _ _ _ (ht pk a xs (lenBound xs hx))]
      rfl
    | hmsg r pk root m =>
      simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inr,rawHash]
      rw [runRead S N H,ShakeApi.extend_restrict _ _ _ _ (hh r pk root m (Nat.le_of_not_gt h))]
      rfl
  · simp only [QueryImpl.apply_compose,rawImpl,QueryImpl.add_apply_inr,rawHash,simulateQ_map,runRead,map_pure]
    rw [ShakeApi.extend_restrict _ _ _ _ (hpm q.skPrf q.optRand q.msg (Nat.le_of_not_gt h))]
    rfl

local notation "R" => SignatureAlg.map (simulateQ' (answerImpl (ShakeApi.restrict S N base))) (rawScheme S N base rand seeds)
local notation "B" => ShakeApi.scheme S rand seeds base

include cap in
theorem run_cap :
    (R).keygen = (B).keygen ∧
    (∀ pk sk mc, mc.1.length + mc.2.length + 2 ≤ L → (R).sign pk sk mc = (B).sign pk sk mc) ∧
    (∀ pk mc sig, mc.1.length + mc.2.length + 2 ≤ L → (R).verify pk mc sig = (B).verify pk mc sig) := by
  have h := pureBytesRomScheme_instantiation S base (ShakeApi.signRand S rand base) seeds
  change _ = (ShakeApi.scheme S rand seeds base) at h
  rw [← h]
  refine ⟨?_,?_,?_⟩
  · change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose]
    exact run_congr _ (bytes_key_ok S base L rand seeds) _ _ (close_step S base L N cap)
  · intro pk sk mc hmc
    change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose]
    exact run_congr _ (bytes_sign_ok S base L rand seeds pk sk mc hmc) _ _ (close_step S base L N cap)
  · intro pk mc sig hmc
    change simulateQ _ (simulateQ _ _) = simulateQ _ _
    rw [← QueryImpl.simulateQ_compose]
    exact run_congr _ (bytes_verify_ok S base L rand seeds pk mc sig hmc) _ _ (close_step S base L N cap)

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.run_cap
