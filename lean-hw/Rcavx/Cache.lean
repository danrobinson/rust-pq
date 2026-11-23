import Rcavx.Window
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust
def Cache (W : Words) (g : Nat) (ms : Array Lane 8#usize) :=
  ∀ p, g≤p → p<g+8 → ms.val[p%8]! = weighted W p
def Archive (W : Words) (g : Nat) (ms : Array Lane 40#usize) :=
  ∀ p, p<g → ms.val[p]! = weighted W p

def flat (xs : List Lane) := xs.flatMap (fun x => ([⟨x.1⟩,⟨x.2⟩] : List U64))

theorem flat_length (xs : List Lane) : (flat xs).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [flat,List.flatMap_cons] at ih ⊢; omega

theorem flat_pair (xs : List Lane) (p : Nat) (bound : p<xs.length) :
    ((flat xs)[2*p]!.bv,(flat xs)[2*p+1]!.bv) = xs[p]! := by
  induction xs generalizing p with
  | nil => simp at bound
  | cons h t ih =>
    cases p with
    | zero => cases h; rfl
    | succ p =>
      have hp : p<t.length := by simpa using bound
      simpa only [flat,List.flatMap_cons,List.cons_append,List.nil_append,Nat.mul_succ,
        List.getElem!_cons_succ,Nat.add_assoc] using (ih p hp)

theorem cast_spec {n len : Usize} (a : Array Lane n) (size : 2*n.val = len.val) :
    RcAvxRust.cast a len ⦃ out => ∀ p, p<n.val →
      (out.val[2*p]!.bv,out.val[2*p+1]!.bv) = a.val[p]! ⦄ := by
  have length : (flat a.val).length=len.val := by rw [flat_length]; simpa using size
  unfold RcAvxRust.cast
  change (if h : (flat a.val).length=len.val then ok (Array.from (flat a.val) h) else _) ⦃ _ ⦄
  rw [dif_pos length]
  simp only [step_simps,Array.from_val]
  intro p hp
  exact flat_pair _ p (by simpa using hp)

theorem cache_advance (W : Words) (g : Nat) (ms : Array Lane 8#usize) (i : Usize)
    (cache : Cache W g ms) (idx : i.val=g%8) :
    Cache W (g+1) (ms.set i (weighted W (g+8))) := by
  intro p lo hi
  by_cases eq : p=g+8
  · subst p
    rw [← Array.getElem!_Nat_eq]
    exact Array.getElem!_Nat_set_eq _ _ _ _ ⟨by omega,by simp; omega⟩
  · have old := cache p (by omega) (by omega)
    have distinct : p%8≠i.val := by omega
    rw [← Array.getElem!_Nat_eq,Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm distinct)]
    simpa only [Array.getElem!_Nat_eq] using old

theorem archive_advance (W : Words) (g : Nat) (ms : Array Lane 40#usize) (i : Usize)
    (cache : Archive W g ms) (idx : i.val=g) (bound : g<40) :
    Archive W (g+1) (ms.set i (weighted W g)) := by
  intro p hi
  by_cases eq : p=g
  · subst p
    rw [← Array.getElem!_Nat_eq]
    exact Array.getElem!_Nat_set_eq _ _ _ _ ⟨by omega,by simp; omega⟩
  · have old := cache p (by omega)
    rw [← Array.getElem!_Nat_eq,Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
    simpa only [Array.getElem!_Nat_eq] using old
end slhdsa.X86.RustCrypto512
