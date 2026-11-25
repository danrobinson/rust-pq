import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

namespace MetalSignatureLayout

structure Geometry where
  n : Nat
  k : Nat
  s1 : Nat
  s2 : Nat
  d : Nat
  wots : Nat
  hp : Nat

/-- Pass 1 writes the secret followed by the first s1 authentication nodes.
Pass 2 writes the remaining s2 authentication nodes, which may be empty. -/
abbrev ForsSlot (g : Geometry) := Fin 1 ⊕ (Fin g.s1 ⊕ Fin g.s2)
abbrev XmssSlot (g : Geometry) := Fin g.wots ⊕ Fin g.hp
abbrev Node (g : Geometry) :=
  Fin 1 ⊕ ((Fin g.k × ForsSlot g) ⊕ (Fin g.d × XmssSlot g))
abbrev Byte (g : Geometry) (count : Nat) := Fin count × Node g × Fin g.n

def forsBytes (g : Geometry) := g.k * (1 + (g.s1 + g.s2)) * g.n
def xmssBytes (g : Geometry) := (g.wots + g.hp) * g.n
def signatureBytes (g : Geometry) := g.n + forsBytes g + g.d * xmssBytes g

/-- The actual host descriptor offsets, plus the shader's node and byte
offsets. The FORS tree offset is relative to the beginning of the signature.
The WOTS and XMSS authentication offsets are relative to the layer. -/
def address (g : Geometry) {count : Nat} (p : Byte g count) : Nat :=
  let base := p.1.val * signatureBytes g
  let byte := p.2.2.val
  match p.2.1 with
  | .inl _ => base + byte
  | .inr (.inl (tree, slot)) =>
    let start := base + g.n + tree.val * (1 + (g.s1 + g.s2)) * g.n
    match slot with
    | .inl _ => start + byte
    | .inr (.inl h) => start + (1 + h.val) * g.n + byte
    | .inr (.inr h) => start + (1 + g.s1 + h.val) * g.n + byte
  | .inr (.inr (layer, slot)) =>
    let start := base + (g.n + forsBytes g + layer.val * xmssBytes g)
    match slot with
    | .inl chain => start + chain.val * g.n + byte
    | .inr height => start + g.wots * g.n + height.val * g.n + byte

private def nodeCount (g : Geometry) :=
  1 + (g.k * (1 + (g.s1 + g.s2)) + g.d * (g.wots + g.hp))

private def nodeEquiv (g : Geometry) : Node g ≃ Fin (nodeCount g) :=
  let fors : ForsSlot g ≃ Fin (1 + (g.s1 + g.s2)) :=
    ((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv
  let forest := ((Equiv.refl (Fin g.k)).prodCongr fors).trans finProdFinEquiv
  let layers := ((Equiv.refl (Fin g.d)).prodCongr finSumFinEquiv).trans finProdFinEquiv
  ((Equiv.refl (Fin 1)).sumCongr ((forest.sumCongr layers).trans finSumFinEquiv)).trans finSumFinEquiv

private def flatten (g : Geometry) (count : Nat) :
    Byte g count ≃ Fin (count * (nodeCount g * g.n)) :=
  ((Equiv.refl (Fin count)).prodCongr
    (((nodeEquiv g).prodCongr (Equiv.refl (Fin g.n))).trans finProdFinEquiv)).trans finProdFinEquiv

private theorem size_eq (g : Geometry) : nodeCount g * g.n = signatureBytes g := by
  unfold nodeCount signatureBytes forsBytes xmssBytes
  ring

private def ordinal (g : Geometry) : Node g → Nat
  | .inl r => r.val
  | .inr (.inl (tree, slot)) =>
    1 + ((match slot with
      | .inl s => s.val
      | .inr (.inl h) => 1 + h.val
      | .inr (.inr h) => 1 + (g.s1 + h.val)) +
      (1 + (g.s1 + g.s2)) * tree.val)
  | .inr (.inr (layer, slot)) =>
    1 + (g.k * (1 + (g.s1 + g.s2)) +
      ((match slot with | .inl c => c.val | .inr h => g.wots + h.val) +
        (g.wots + g.hp) * layer.val))

private theorem node_eq (g : Geometry) (p : Node g) :
    (nodeEquiv g p).val = ordinal g p := by
  rcases p with r | ⟨tree, secret | (lo | hi)⟩ | ⟨layer, wots | auth⟩ <;> rfl

private theorem byte_eq (g : Geometry) {count : Nat} (p : Byte g count) :
    (flatten g count p).val = address g p := by
  rcases p with ⟨i, field, b⟩
  change b.val + g.n * (nodeEquiv g field).val + (nodeCount g * g.n) * i.val = _
  rw [node_eq, size_eq]
  rcases field with r | ⟨tree, secret | (lo | hi)⟩ | ⟨layer, wots | auth⟩
  all_goals
    simp [ordinal, address, signatureBytes, forsBytes, xmssBytes, Fin.fin_one_eq_zero]
    ring

/-- Every valid field byte resolves inside the allocated batch. -/
theorem in_bounds (g : Geometry) {count : Nat} (p : Byte g count) :
    address g p < count * signatureBytes g := by
  simpa [byte_eq, size_eq] using (flatten g count p).isLt

/-- Different signatures, trees, passes, layers, chains, heights or byte
positions have distinct addresses. -/
theorem disjoint (g : Geometry) (count : Nat) : Function.Injective (@address g count) := by
  intro a b h
  apply (flatten g count).injective
  exact Fin.ext (by simpa only [byte_eq] using h)

/-- Every byte of the complete output has exactly one valid field and owner,
including both sides of every FORS and XMSS boundary. -/
theorem cover (g : Geometry) {count pos : Nat} (h : pos < count * signatureBytes g) :
    ∃! p : Byte g count, address g p = pos := by
  let i : Fin (count * (nodeCount g * g.n)) := ⟨pos, by simpa [size_eq]⟩
  let p := (flatten g count).symm i
  have hp : address g p = pos := by
    rw [← byte_eq, Equiv.apply_symm_apply]
  exact ⟨p, hp, fun other ho => disjoint g count (ho.trans hp.symm)⟩

end MetalSignatureLayout
