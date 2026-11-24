import Integration.SlhDsaShakeApi

namespace Reduction.ShakeApi
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal

abbrev Input (N : ℕ) := BList SLHDSA.Byte N
abbrev RawTable (S : Sha2Set) (N : ℕ) := Input N → Bytes S.vp.params.m

def extend {S : Sha2Set} {N : ℕ} (H : RawTable S N) : Xof S :=
  fun xs => if h : xs.length ≤ N then H (BList.ofList xs h) else default

theorem extend_apply {S : Sha2Set} {N : ℕ} (H : RawTable S N) (xs : List SLHDSA.Byte) (h : xs.length ≤ N) :
    extend H xs = H (BList.ofList xs h) := dite_eq_left h

def restrict (S : Sha2Set) (N : ℕ) (H : Xof S) : RawTable S N :=
  fun x => H (List.ofFn x.2)

theorem extend_restrict (S : Sha2Set) (N : ℕ) (H : Xof S) (xs : List SLHDSA.Byte) (h : xs.length ≤ N) :
    extend (restrict S N H) xs = H xs := by rw [extend_apply _ _ h,restrict,BList.ofFn_ofList]

/-- Maximum raw XOF input needed by the standard hash calls with at most T nodes
per tweakable hash and at most L bytes in the encoded signing message. -/
def rawCap (S : Sha2Set) (T L : ℕ) :=
  max (S.vp.params.n + 32 + S.vp.params.n * max 1 T) (3*S.vp.params.n + L)

private theorem node_length {n : ℕ} (xs : List (Bytes n)) :
    (xs.map Vector.toList).flatten.length = n * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add,Nat.add_comm]

theorem in_range (S : Sha2Set) (T L : ℕ) (N : ℕ) (b : rawCap S T L ≤ N) :
    (∀ (k : S.Node) (a : Bytes 32) (xs : List S.Node), xs.length ≤ T →
      (k.toList ++ a.toList ++ (xs.map Vector.toList).flatten).length ≤ N) ∧
    (∀ (k s : S.Node) (a : Adrs), (k.toList ++ a.toVector.toList ++ s.toList).length ≤ N) ∧
    (∀ (k r : S.Node) (m : List SLHDSA.Byte), m.length ≤ L → (k.toList ++ r.toList ++ m).length ≤ N) ∧
    (∀ (r pk root : S.Node) (m : List SLHDSA.Byte), m.length ≤ L → (r.toList ++ pk.toList ++ root.toList ++ m).length ≤ N) := by
  have h := (Nat.le_max_left ..).trans b
  have g := (Nat.le_max_right ..).trans b
  refine ⟨?_,?_,?_,?_⟩
  · intro k a xs hx
    simp only [List.length_append,Vector.length_toList,node_length]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hx.trans (Nat.le_max_right ..))) _).trans h
  · intro k s a
    simp only [List.length_append,Vector.length_toList]
    have hh := Nat.mul_le_mul_left S.vp.params.n (Nat.le_max_left 1 T)
    simp only [Nat.mul_one] at hh
    omega
  · intro k r m hm; simp only [List.length_append,Vector.length_toList]; omega
  · intro r pk root m hm; simp only [List.length_append,Vector.length_toList]; omega

variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)

noncomputable abbrev rawForger (H : RawTable S N) := forgerAt S rand seeds F (extend H) H

/-- One probability space for both the forger's coherent XOF calls and every
query made by the classical signature algorithms. -/
theorem raw_reduction :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (rawForger S N rand seeds F H)) ≤
      SetOracle.uniformMean (fun H => qBetaSufMemoG (qPureBytesToInternal (rawForger S N rand seeds F H))) ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (rawForger S N rand seeds F H)) ≤
      SetOracle.uniformMean (fun H => qBetaEufMemoG (qPureBytesToInternal (rawForger S N rand seeds F H))) := by
  constructor
  · exact Finset.sum_le_sum fun H _ => mul_le_mul' le_rfl (signature_reduction S rand seeds F (extend H) H).1
  · exact Finset.sum_le_sum fun H _ => mul_le_mul' le_rfl (signature_reduction S rand seeds F (extend H) H).2

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.in_range
#print axioms Reduction.ShakeApi.raw_reduction
