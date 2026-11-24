import Integration.SlhDsaSetClosed
import HashSig.SLHDSA.Security.ByteModel

/-! A slice of a single raw SHAKE oracle. Replacing a prefix on an injectively
encoded slice keeps all other inputs and the unused suffix of every answer.
This lets a quantum adversary retain unrestricted superposition access to the
raw table while an individual primitive game resamples its selected slice. -/
namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Classical ComplexOrder Kronecker

def head {n m : ℕ} (h : n ≤ m) (v : Bytes m) : Bytes n :=
  Vector.ofFn fun i => v[i.val]'(Nat.lt_of_lt_of_le i.isLt h)

def replaceHead {n m : ℕ} (v : Bytes m) (u : Bytes n) : Bytes m :=
  Vector.ofFn fun i => if h : i.val < n then u[i.val]'h else v[i.val]

theorem head_eq_prefix {n m : ℕ} (h : n ≤ m) (v : Bytes m) :
    head h v = prefixBytes n v := by
  apply Vector.toList_inj.mp
  rw [toList_prefixBytes_of_le h]
  apply List.ext_getElem
  · simp [head,h]
  · intro i hi hj
    simp [head,List.getElem_take]

theorem head_replace {n m : ℕ} (h : n ≤ m) (v : Bytes m) (u : Bytes n) :
    head h (replaceHead v u) = u := by
  ext i hi
  simp [head,replaceHead]

theorem replace_undo {n m : ℕ} (h : n ≤ m) (v : Bytes m) (u : Bytes n) :
    replaceHead (replaceHead v u) (head h v) = v := by
  ext i hi
  by_cases hj : i < n <;> simp [replaceHead,head,hj]

variable {J X : Type} (emb : J ↪ X)
noncomputable def locate (x : X) : Option J :=
  if h : ∃ j, emb j = x then some h.choose else none

theorem locate_emb (j : J) : locate emb (emb j) = some j := by
  classical
  have h : ∃ k, emb k = emb j := ⟨j,rfl⟩
  simp only [locate,dite_eq_left h]
  exact congrArg some (emb.injective h.choose_spec)

theorem located {x : X} {j : J} (h : locate emb x = some j) : emb j = x := by
  classical
  unfold locate at h
  split_ifs at h with he
  · exact Option.some.inj h ▸ he.choose_spec

variable {n m : ℕ}
def read (hn : n ≤ m) (g : X → Bytes m) : J → Bytes n := fun j => head hn (g (emb j))

noncomputable def write (g : X → Bytes m) (r : J → Bytes n) (x : X) : Bytes m :=
  (locate emb x).elim (g x) (fun j => replaceHead (g x) (r j))

theorem read_write (hn : n ≤ m) (g : X → Bytes m) (r : J → Bytes n) :
    read emb hn (write emb g r) = r := by
  funext j
  simp only [read,write,locate_emb,Option.elim_some,head_replace]

theorem row_swap (hn : n ≤ m) : Function.Involutive
    (fun z : (X → Bytes m) × (J → Bytes n) => (write emb z.1 z.2,read emb hn z.1)) := by
  rintro ⟨g,r⟩
  apply Prod.ext _ (read_write emb hn g r)
  funext x
  cases hl : locate emb x with
  | none => simp only [write,hl,Option.elim_none]
  | some j =>
    have hx := located emb hl
    simp only [write,hl,Option.elim_some,read,hx,replace_undo]

theorem local_at (g : X → Bytes m) (r s : J → Bytes n) (x : X)
    (same : ∀ j, locate emb x = some j → r j = s j) : write emb g r x = write emb g s x := by
  unfold write
  cases hl : locate emb x with
  | none => rfl
  | some j => simp only [Option.elim_some,same j hl]

theorem different_at (g : X → Bytes m) (r s : J → Bytes n) (x : X)
    (diff : write emb g r x ≠ write emb g s x) : ∃ j, emb j = x ∧ r j ≠ s j := by
  by_contra! han
  exact diff (local_at emb g r s x (fun j hj => han j (located emb hj)))

variable [Fintype X] [Fintype J] [Nonempty J]
theorem resample (hn : n ≤ m) (f : (X → Bytes m) → ℝ≥0∞) :
    SetOracle.uniformMean f = SetOracle.uniformMean (fun g =>
      SetOracle.uniformMean (fun r : J → Bytes n => f (write emb g r))) :=
  SetOracle.avg_resample (write emb) (read emb hn) (row_swap emb hn) f

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.resample
