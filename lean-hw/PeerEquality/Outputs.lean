import Slhdsa.Proofs.Basic

open Aeneas Aeneas.Std Result

namespace slhdsa.PeerEquality

/-- Both executions succeed and have the same observable output. The projection
keeps the full serialized keys, signature or rejection, or verification decision. -/
def SameOutput {α β : Type} (left right : Result α) (observe : α → β) : Prop :=
  ∃ a b, left = ok a ∧ right = ok b ∧ observe a = observe b

theorem sameOutput {α β : Type} {left right : Result α} {f : α → β} {s : β}
    (lhs : left ⦃ x => f x = s ⦄) (rhs : right ⦃ x => f x = s ⦄) :
    SameOutput left right f := by
  obtain ⟨a,ha,sa⟩ := spec_imp_exists lhs
  obtain ⟨b,hb,sb⟩ := spec_imp_exists rhs
  exact ⟨a,b,ha,hb,sa.trans sb.symm⟩

end slhdsa.PeerEquality
