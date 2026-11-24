import Integration.SlhDsaCompressionClassicalPort

namespace Reduction.Compression.ClassicalPort
open PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec ENNReal Matrix
open scoped ComplexOrder Kronecker
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {ι α β σ : Type} {sp : OracleSpec ι}
local notation "B" => Reg X Y
local notation "Work" => WS X Y Unit
local notation "Prog" => QOC B (portSpec + sp)
abbrev Reads (X Y : Type) {ι : Type} (sp : OracleSpec ι) := (X →ₒ Y) + sp

noncomputable def translate : QueryImpl (Reads X Y sp) Prog
  | .inl x => readBasis x
  | .inr i => (instrSpec B + (portSpec + sp)).query (.inr (.inr i))

def answers (H : X → Y) : QueryImpl (Reads X Y sp) (OracleComp sp)
  | .inl x => pure (H x)
  | .inr i => sp.query i

theorem basis_step (H : X → Y) (impl : QueryImpl sp (StateT σ ProbComp)) (u : X)
    (s : σ) (r : B) (k : Y → Prog α) (K : α × σ → Closed Work β) (ev : β → Prop) [DecidablePred ev] :
    qWeight ev (close impl (compileQ H (readBasis u >>= k)) s >>= K) (Matrix.single (r,()) (r,()) 1) =
      qWeight ev (close impl (compileQ H (k (H u))) s >>= K)
        (Matrix.single (((u,0),()),()) (((u,0),()),()) 1) := by
  unfold compileQ
  rw [simulateQ_bind,close_bind,bind_assoc]
  exact read_weight H impl u r s (fun z => close impl (simulateQ (compileImplQ H) (k z.1)) z.2 >>= K) ev

theorem program_weight (H : X → Y) (impl : QueryImpl sp (StateT σ ProbComp))
    (P : OracleComp (Reads X Y sp) α) (s : σ) (r : B) (K : α × σ → Closed Work β) (k : α × σ → ProbComp β)
    (ev : β → Prop) [DecidablePred ev]
    (hk : ∀ z (r : B), qWeight ev (K z) (Matrix.single (r,()) (r,()) 1) = prob (k z) ev) :
    qWeight ev (close impl (compileQ H (simulateQ translate P)) s >>= K) (Matrix.single (r,()) (r,()) 1) =
      prob ((simulateQ impl (simulateQ (answers H) P)).run s >>= k) ev := by
  induction P using OracleComp.inductionOn generalizing s r with
  | pure x => simpa [compileQ] using hk (x,s) r
  | query_bind i f ih =>
    cases i with
    | inl u =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate,answers,pure_bind]
      exact (basis_step H impl u s r (fun v => simulateQ translate (f v)) K ev).trans (ih (H u) s ((u,0),()))
    | inr i =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate,answers,
        StateT.run_bind,bind_assoc]
      erw [compileQ_query_bind H i (fun v => simulateQ translate (f v)),close_query_bind,bind_assoc]
      have e := qWeight_liftU_bind ev ((impl i).run s)
        (fun z => close impl (compileQ H (simulateQ translate (f z.1))) z.2 >>= K)
        (fun z => (simulateQ impl (simulateQ (answers H) (f z.1))).run z.2 >>= k) 1
        (Matrix.single (r,()) (r,()) 1) (fun z => (ih z.1 z.2 r).trans (one_mul _).symm)
      rw [one_mul] at e
      exact e

def countClass (read : Bool) (cost : ι → Bool) : (Reads X Y sp).Domain → Bool
  | .inl _ => read
  | .inr i => cost i

def countPort (read : Bool) (cost : ι → Bool) : (instrSpec B + (portSpec + sp)).Domain → Bool
  | .inl _ => false
  | .inr (.inl _) => read
  | .inr (.inr i) => cost i

theorem program_count (read : Bool) (cost : ι → Bool) (P : OracleComp (Reads X Y sp) α)
    (q : ℕ) (hp : CountBound (fun i => countClass (X := X) (Y := Y) (sp := sp) read cost i = true) P q) :
    CountBound (fun i => countPort (X := X) (Y := Y) (sp := sp) read cost i = true) (simulateQ translate P) q := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure x => exact trivial
  | query_bind i f ih =>
    rw [countBound_query_bind] at hp
    cases i with
    | inl u =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate,readBasis,bind_assoc,pure_bind]
      cases read <;> simp only [countClass,countPort,Bool.false_eq_true,↓reduceIte] at hp ⊢
      · exact fun _ _ k => ih _ q (hp _)
      · exact fun _ => ⟨hp.1,fun _ _ => ih _ _ (hp.2 _)⟩
    | inr i =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate]
      rw [countBound_query_bind]
      cases h : cost i <;> simp only [countClass,countPort,h,Bool.false_eq_true,↓reduceIte] at hp ⊢
      · exact fun v => ih v _ (hp v)
      · exact ⟨hp.1,fun v => ih v _ (hp.2 v)⟩

theorem program_cap (ok : ι → Prop) (out : α → Prop) (P : OracleComp (Reads X Y sp) α)
    (hp : AllQueries (fun i => match i with | .inl _ => True | .inr j => ok j) out P) :
    AllQueries (fun i => match i with | .inr (.inr j) => ok j | _ => True) out (simulateQ translate P) := by
  induction P using OracleComp.inductionOn with
  | pure x => exact hp
  | query_bind i f ih =>
    rw [QMsg.allQ_query_bind] at hp
    cases i with
    | inl u =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate,readBasis,bind_assoc,pure_bind,QMsg.allQ_query_bind,
        true_and]
      exact fun _ _ k => ih _ (hp.2 _)
    | inr i =>
      simp only [simulateQ_bind,simulateQ_spec_query,translate,QMsg.allQ_query_bind]
      exact ⟨hp.1,fun v => ih v (hp.2 v)⟩

end Reduction.Compression.ClassicalPort
#print axioms Reduction.Compression.ClassicalPort.program_weight

#print axioms Reduction.Compression.ClassicalPort.program_count
#print axioms Reduction.Compression.ClassicalPort.program_cap
