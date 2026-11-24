import Integration.SlhDsaShakePermutationClassicalByteGame
import Integration.SlhDsaShakeSetPrecision

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp MLink SLHDSA Classical PQ.Interactive PQ.QROM Quantum
open Honest (ByteMessage ByteSig RawSpec)
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxRecDepth 8192

def publicRead {X Y : Type} : (Compression.ClassicalPort.Reads X Y SignSpec).Domain → Bool
  | .inl _ => true
  | _ => false
def signRead {X Y : Type} : (Compression.ClassicalPort.Reads X Y SignSpec).Domain → Bool
  | .inr (.inr _) => true
  | _ => false
def readCap {X Y : Type} (c : Caps) : (Compression.ClassicalPort.Reads X Y SignSpec).Domain → Prop
  | .inr (.inr m) => m.1.length+m.2.length+2 ≤ c.ml
  | _ => True

private theorem recast {ι Z : Type} {sp : OracleSpec ι} {p q : ι → Prop} [d : DecidablePred p] [e : DecidablePred q]
    (eq : p = q) {P : OracleComp sp Z} {n : ℕ} (hp : CountBound p P n) : CountBound q P n := by
  subst q; cases Subsingleton.elim d e; exact hp

theorem lift_bounds {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (x : X) (F : CForger X Y) (pk : List SLHDSA.Byte) (q s : ℕ) (c : Caps)
    (hp : CountBound (fun i => publicRead (X := X) (Y := Y) i = true) (F pk) q)
    (hs : CountBound (fun i => signRead (X := X) (Y := Y) i = true) (F pk) s)
    (hc : AllQueries (readCap (X := X) (Y := Y) c) (capOut c) (F pk)) :
    CountBound isPort ((liftClassical x F).main pk) q ∧ CountBound isSign ((liftClassical x F).main pk) s ∧
    AllQueries (capIdx c) (capOut c) ((liftClassical x F).main pk) := by
  have change (p : Bool) : (fun i => Compression.ClassicalPort.countPort (X := X) (Y := Y) (sp := SignSpec) p
      (fun j => !p && j.isRight) i = true) = (if p then isPort else isSign) := by
    funext i; cases p <;> rcases i with _|_|_|_ <;> simp [isPort,isSign,Compression.ClassicalPort.countPort]
  have cc (p : Bool) : (fun i => Compression.ClassicalPort.countClass (X := X) (Y := Y) (sp := SignSpec) p
      (fun j => !p && j.isRight) i = true) = (fun i => (if p then publicRead (X := X) (Y := Y) i else signRead i) = true) := by
    funext i; cases p <;> rcases i with _|_|_ <;> rfl
  have pbound := Compression.ClassicalPort.program_count (sp := SignSpec) true (fun j => !true && j.isRight) (F pk) q
    (recast (cc true).symm hp)
  have sbound := Compression.ClassicalPort.program_count (sp := SignSpec) false (fun j => !false && j.isRight) (F pk) s
    (recast (cc false).symm hs)
  refine ⟨?_,?_,?_⟩
  · apply recast (q := isPort) _ pbound
    simpa only [ite_true] using change true
  · apply recast (q := isSign) _ sbound
    simpa only [Bool.false_eq_true,ite_false] using change false
  · let ok : SignSpec.Domain → Prop := fun i => match i with | .inl _ => True | .inr m => m.1.length+m.2.length+2 ≤ c.ml
    have ca := Compression.ClassicalPort.program_cap ok (capOut c) (F pk) (by
      apply QMsg.allQ_mono _ (fun z h => h) hc
      rintro (x|n|m) h <;> exact h)
    apply QMsg.allQ_mono _ (fun z h => h) ca
    rintro (a|u|n|m) h <;> exact h

theorem cost_scale {ι Z : Type} {sp : OracleSpec ι} (w : ι → ℕ) (B : ℕ) (P : OracleComp sp Z) (q : ℕ)
    (hq : WCount w P q) : WCount (fun i => B*w i) P (B*q) := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure => trivial
  | query_bind i k ih =>
    rw [wCount_query_bind] at hq ⊢
    exact ⟨Nat.mul_le_mul_left _ hq.1,fun u => by rw [← Nat.mul_sub]; exact ih _ _ (hq.2 u)⟩

theorem routed_cost (S : Sha2Set) (N B : ℕ) (cap : Completion.blockCap N ≤ B)
    {Z : Type} (P : OracleComp (RawSpec S N) Z) (q : ℕ) (hq : WCount Honest.hashWeight P q) :
    WCount (charge S N) (simulateQ (liftRaw S N) P) (B*q) := by
  refine WCount.simulateQ (w := fun i => B*Honest.hashWeight i) _ ?_ (cost_scale _ B P q hq)
  rintro (n|x)
  · exact wCount_liftM_query _ _ (by simp [charge,Honest.hashWeight])
  · exact wCount_liftM_query _ _ (by simpa only [charge,Honest.hashWeight,Sum.elim_inr,Nat.mul_one,cost] using blocksOf_length N B cap x)

def fee (sign : ℕ) : (Compression.ClassicalPort.Reads Port Words SignSpec).Domain → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 0
  | .inr (.inr _) => sign

variable (S : Sha2Set) (N : ℕ) (fixed : ShakeApi.Xof S) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
local notation "A" => Honest.rawScheme S N fixed r seeds

theorem drive_cost (B : ℕ) (cap : Completion.blockCap N ≤ B) (pk sk : List SLHDSA.Byte) (fresh : Fresh)
    (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Claim) (q : ℕ)
    (budget : WCount (fee (B*Honest.signCharge S)) P q) (log : Log) :
    WCount (charge S N) (drive S N A pk sk fresh P log) (q+B*Honest.verifyCharge S) := by
  induction P using OracleComp.inductionOn generalizing q log with
  | pure c =>
    have raw := Honest.raw_count S N fixed (Honest.verify_bound S fixed r seeds pk c.1 c.2)
    exact (WCount.bind (routed_cost S N B cap _ _ raw) (m := 0) (fun _ => wCount_pure _ _ 0)).mono (by omega)
  | query_bind i k ih =>
    rcases i with x|n|msg
    · change WCount _ (liftM ((Outer S N).query (.inr (.inl x))) >>= _) _
      rw [wCount_query_bind]
      have c : 1 ≤ q := budget.1
      exact ⟨by change 1 ≤ _; omega,fun y => (ih y _ (budget.2 y) _).mono (by change q-1+_≤(q+_)-1; omega)⟩
    · change WCount _ (liftM ((Outer S N).query (.inl n)) >>= _) _
      rw [wCount_query_bind]
      exact ⟨Nat.zero_le _,fun y => ih y q (budget.2 y) log⟩
    · have raw := Honest.raw_count S N fixed (Honest.sign_bound S fixed r seeds pk sk msg)
      have enough : B*Honest.signCharge S ≤ q := budget.1
      exact (WCount.bind (routed_cost S N B cap _ _ raw) (fun y => ih y _ (budget.2 y) _)).mono (by
        change B*Honest.signCharge S + (q-B*Honest.signCharge S + _) ≤ q+_; omega)

theorem byte_budget (B : ℕ) (cap : Completion.blockCap N ≤ B) (F : CForger Port Words) (fresh : Fresh) (q s : ℕ)
    (hp : ∀ pk, CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) q)
    (hs : ∀ pk, CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) s) :
    WCount (charge S N) (byteGame S N A F fresh) (q+B*Honest.honestCharge S s) := by
  have raw := Honest.raw_count S N fixed (Honest.keygen_bound S fixed r seeds)
  have run (ks : List SLHDSA.Byte × List SLHDSA.Byte) := drive_cost S N fixed r seeds B cap ks.1 ks.2 fresh (F ks.1)
    (q+s*(B*Honest.signCharge S)) (wCount_of_countBound _ _ _ _ (by rintro (x|n|m) <;> simp [fee,publicRead,signRead])
        (F ks.1) q s (hp _) (hs _)) []
  exact (WCount.bind (routed_cost S N B cap _ _ raw) run).mono (by unfold Honest.honestCharge; ring_nf; rfl)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.byte_budget
