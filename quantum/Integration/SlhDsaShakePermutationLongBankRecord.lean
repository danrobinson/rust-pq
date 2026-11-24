import Integration.SlhDsaShakePermutationLongBank

namespace Reduction.ShakePermutation.Long.BankRun
open Classical ItsrLabel OracleSpec OracleComp PQ.Interactive ENNReal SetOracle
noncomputable section
set_option maxRecDepth 8192
variable {A B : Type}

def Pins (D : Bank) (H : Table) := ∀ i y, D i = some y → H i=y

def Ext (D D' : Bank) := ∀ i y, D i=some y → D' i=some y

theorem fill_pins (D : Bank) (H : Table) : Pins D (Classic.fill D H) := fun i y e => by simp [Classic.fill,e]

theorem ext_trans {D E F : Bank} (de : Ext D E) (ef : Ext E F) : Ext D F := fun i y h => ef i y (de i y h)

def write (D : Bank) (H : Table) (x : Addr) := Function.update D x (some (H x))

theorem write_ext {D : Bank} {H : Table} (pin : Pins D H) (x : Addr) : Ext D (write D H x) := by
  intro i y e; by_cases h : i=x
  · subst i; simp [write,pin x y e]
  · simp [write,Function.update_of_ne h,e]

theorem write_pins {D : Bank} {H : Table} (pin : Pins D H) (x : Addr) : Pins (write D H x) H := by
  intro i y e; by_cases h : i=x
  · subst i; exact Option.some.inj (by simpa [write] using e)
  · exact pin i y (by simpa [write,Function.update_of_ne h] using e)

def fixedAll (H : Table) (p : OracleComp Spec A) (D : Bank) (post : A → Bank → Prop) :=
  OracleComp.construct (C:=fun _ => Bank → Prop) post (fun i _ k d => match i with
  | .inl _ => ∀ r, k r d
  | .inr x => k (H x) (write d H x)) p D

theorem fixed_bind (H : Table) (p : OracleComp Spec A) (k : A → OracleComp Spec B) (D : Bank)
    (mid : A → Bank → Prop) (post : B → Bank → Prop) (first : fixedAll H p D mid)
    (next : ∀ a u, mid a u → fixedAll H (k a) u post) : fixedAll H (p >>= k) D post := by
  induction p using OracleComp.inductionOn generalizing D with
  | pure a => simpa only [pure_bind] using next a D first
  | query_bind i f ih =>
    rw [bind_assoc]; rcases i with n|x
    · exact fun r => ih r D (first r)
    · exact ih _ _ first

theorem deferred (p : OracleComp Spec A) (D : Bank) (post : Table → A → Bank → Prop)
    (good : ∀ H, Pins D H → fixedAll H p D (post H)) : all p D (fun z u => ∀ H, Pins u H → post H z u) := by
  induction p using OracleComp.inductionOn generalizing D with
  | pure a => exact good
  | query_bind i k ih =>
    rcases i with n|x
    · exact fun r => ih r D (fun H h => good H h r)
    · change match D x with | some v => _ | none => _
      cases hx : D x with
      | some v =>
        apply ih v D; intro H pin
        have value := pin x v hx
        have eq : write D H x=D := by
          funext i; by_cases e : i=x <;> simp [write,e,Function.update_of_ne,value,hx]
        have h : fixedAll H (k (H x)) (write D H x) (post H) := good H pin
        simpa only [eq,value] using h
      | none =>
        intro v; apply ih v (Function.update D x (some v)); intro H pin
        have value := pin x v (Function.update_self ..)
        have old : Pins D H := by
          intro i y e; have ne : i ≠ x := by rintro rfl; rw [hx] at e; contradiction
          exact pin i y ((Function.update_of_ne ne ..).trans e)
        have h : fixedAll H (k (H x)) (write D H x) (post H) := good H old
        simpa only [write,value] using h
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.deferred
