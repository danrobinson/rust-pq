import Integration.SlhDsaCompressionLeftTables
import Integration.SlhDsaCompressionCompileResponseNative

namespace Reduction.Compression.Recording.Compile.LeftPort
open MLink Ideal MIdeal.Sha512 SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped Kronecker ComplexOrder

private theorem fraction {T : Type} [DecidableEq T] (p : St → T) (B : Finset T) :
    ((Finset.univ.filter fun y => p (halves y).1 ∈ B).card : ℝ) / Fintype.card Chain512 =
      ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card St := by
  let s := Finset.univ.filter fun y => p y ∈ B
  have h : (Finset.univ.filter fun y => p (halves y).1 ∈ B).card = (s ×ˢ (Finset.univ : Finset St)).card := by
    apply Finset.card_equiv halves
    simp [s]
  rw [h,Finset.card_product,Finset.card_univ,Fintype.card_congr halves,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  have hs : (Fintype.card St : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact mul_div_mul_right _ _ hs

def tagged : Option (Left × Left) → Option (Input × Input) :=
  Option.map fun uv => (.inl uv.1,.inl uv.2)

def wins {T : Type} (p : St → T) (g : CompressionTables) : Option (Left × Left) → Prop
  | none => False
  | some (x,y) => x ≠ y ∧ p (g.1 x) = p (g.1 y)

private theorem event {T : Type} (p : St → T) (h : Full) (b : CF Chain512 Block512) (z : Option (Left × Left)) :
    Database.reports (fun y => p (halves y).1) (tagged z) h ↔ wins p (projectTable h,b) z := by
  rcases z with _|⟨i,j⟩
  · simp [tagged,Database.reports,wins]
  constructor
  · rintro ⟨l,r,hh,hd,he⟩
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hh)
    subst l
    subst r
    exact ⟨fun e => hd (congrArg Sum.inl e),he⟩
  · rintro ⟨hd,he⟩
    exact ⟨.inl i,.inl j,rfl,fun e => hd (Sum.inl.inj e),he⟩

private theorem tables (f : CompressionTables → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ b, unifW _ b * ∑ a, unifW _ a * f (a,b) := by
  simp only [Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

variable {E α T : Type} [Fintype E] [DecidableEq E] [DecidableEq T]

/-- SHA-256 prefix collisions under superposition access to both shared tables. -/
theorem shared_collision (p : St → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card St ≤ (B.card:ℝ)/N)
    (M : (Input → Output) → Closed (WS Input Output E) α)
    (pick : α → Option (Left × Left)) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    (∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins p g (pick z)) (M (oracle g)) ρ₀) ≤
      ENNReal.ofReal (16*((q:ℝ)+1)^3/N) := by
  obtain ⟨x,hx,he⟩ := hq.exists_prog_qprob
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) ρ₀ pos tr
  let C := 16*((q:ℝ)+1)^3/N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [tables]
  calc _ ≤ ∑ b : CF Chain512 Block512, unifW _ b * ENNReal.ofReal C := by
         apply Finset.sum_le_sum
         intro b _
         apply mul_le_mul' le_rfl
         rw [← mean (fun a => qWeight (fun z => wins p (a,b) (pick z)) (M (oracle (a,b))) ρ₀)]
         let ev := fun h : Full => fun z : α => Database.reports (fun y => p (halves y).1) (tagged (pick z)) h
         calc _ = ∑ h : Full, unifW _ h * qprob LocalSig.Interp.instruments (Response.project (mapping b) h) x ρ (fun t => ev h t.2) := by
               apply Finset.sum_congr rfl
               intro h _
               apply congrArg (unifW _ h * ·)
               rw [he (ev h) _ ρ,port,← hρ]
               exact qWeight_congr_ev (fun z => (event p h b (pick z)).symm) _ _
              _ ≤ _ := mixed_mean_over LocalSig.Interp.instruments x ρ q hx
                (Response.project (mapping b)) (fun h t => ev h t.2) C hC (fun u =>
                  Response.pure_mean (fun y => p (halves y).1) N hN (fun B => (fraction p B).le.trans (uniform B))
                    LocalSig.Interp.instruments (mapping b) (fun z => tagged (pick z)) x q hx u)
       _ = _ := by rw [← Finset.sum_mul,sum_unifW,one_mul]
end Reduction.Compression.Recording.Compile.LeftPort
#print axioms Reduction.Compression.Recording.Compile.LeftPort.shared_collision
