import Slhdsa.Funs
import Spec
open Aeneas Aeneas.Std Result

/-! Shared definitions relating machine values to the specification's values. -/

namespace slhdsa

/-- A proven specification triple means the program returns a value satisfying
the postcondition: it does not panic and does not diverge. -/
theorem spec_imp_exists {α} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
    ∃ v, m = ok v ∧ p v := by
  cases m <;> simp_all

theorem getElem!_eq {α} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by
  simp [h]

/-- The spec-level view of a list of machine bytes. -/
def bytes (l : List U8) : Spec.Bytes := l.map (·.bv)

@[simp] theorem bytes_length (l : List U8) : (bytes l).length = l.length := by simp [bytes]

@[simp] theorem bytes_append (l l' : List U8) : bytes (l ++ l') = bytes l ++ bytes l' := by
  simp [bytes]

@[simp] theorem bytes_nil : bytes [] = [] := rfl

@[simp] theorem bytes_cons (x : U8) (l : List U8) : bytes (x :: l) = x.bv :: bytes l := rfl

@[simp] theorem bytes_take (l : List U8) (i : Nat) : bytes (l.take i) = (bytes l).take i := by
  simp [bytes, List.map_take]

@[simp] theorem bytes_drop (l : List U8) (i : Nat) : bytes (l.drop i) = (bytes l).drop i := by
  simp [bytes, List.map_drop]

theorem bytes_getElem! (l : List U8) (i : Nat) (h : i < l.length) :
    (bytes l)[i]! = (l[i]'h).bv := by
  simp [bytes, h]

/-- The spec-level view of a list of machine words. -/
def nats (l : List U32) : List Nat := l.map (·.val)

@[simp] theorem nats_length (l : List U32) : (nats l).length = l.length := by simp [nats]

/-- The spec-level view of a hash address. -/
def adrsS (a : address.Adrs) : Spec.Adrs :=
  ⟨a.layer.val, a.tree.val, a.typ.val, a.keypair.val, a.word2.val, a.word3.val⟩

/-- A byte string of length `len` is short enough to be hashed with `slack`
further bytes around it: the buffer fits in memory and its bit length fits
in the 64-bit SHA-256 length field (FIPS 180-4 defines SHA-256 only below
2^61 bytes). No real machine can hold a message that violates it. -/
def Room (len slack : Nat) : Prop := len + slack ≤ Usize.max ∧ len + slack < 2 ^ 61

end slhdsa
