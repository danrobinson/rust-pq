import Shakebatch.Sibling
import Shakebatch.ClimbStep

namespace slhdsa.PeerFors

/-- FORS signing expressed using the global tree indices passed by RustCrypto. -/
def sign (p : Spec.Params) (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) : Spec.Bytes :=
  (List.range p.k).flatMap fun t =>
    let leaf := t * 2 ^ p.a + (Spec.base2b md p.a p.k)[t]!
    Spec.forsSkGen p sk pk adrs leaf ++ (List.range p.a).flatMap fun j =>
      Spec.forsNode p sk ((leaf / 2 ^ j) ^^^ 1) j pk adrs

theorem sign_eq (p : Spec.Params) (md sk pk : Spec.Bytes) (adrs : Spec.Adrs) :
    sign p md sk pk adrs = Spec.forsSign p md sk pk adrs := by
  unfold sign Spec.forsSign
  apply List.flatMap_congr
  intro t ht
  dsimp only
  apply congrArg (List.append _)
  apply List.flatMap_congr
  intro j hj
  rw [ShakeBatch.sibling_eq _ _ _ _ (List.mem_range.mp hj)]

/-- Each upward step reads one signature block, then orders it with the preceding
    node according to the parity of the global index. -/
def path (p : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs) (t leaf : Nat) :
    Nat → Spec.Bytes × Nat
  | 0 => (Spec.F p pk {adrs with word2 := 0, word3 := leaf}
      (Spec.block p sig (t * (p.a + 1))), leaf)
  | j+1 =>
    let (child, index) := path p sig pk adrs t leaf j
    let sibling := Spec.block p sig (t * (p.a + 1) + 1 + j)
    (Spec.H p pk {adrs with word2 := j + 1, word3 := index / 2}
      (pairMsg child sibling index), index / 2)

theorem path_correct (p : Spec.Params) (sig pk : Spec.Bytes) (adrs : Spec.Adrs)
    (digits : List Nat) (t j : Nat) (hj : j ≤ p.a) :
    let s := path p sig pk adrs t (t * 2 ^ p.a + digits[t]!) j
    ShakeBatch.AtLevel p sig pk adrs digits t j s.2 s.1 := by
  induction j with
  | zero => simp [path, ShakeBatch.AtLevel, forsClimbAt, forsLeaf]
  | succ j ih =>
    exact ShakeBatch.climb_step _ _ _ _ _ _ _ _ _ (by omega) (ih (by omega))

/-- The final hash receives the roots in signature row order. -/
def recover (p : Spec.Params) (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) : Spec.Bytes :=
  Spec.T p pk {adrs.setTypeAndClear Spec.FORS_ROOTS with keypair := adrs.keypair}
    ((List.range p.k).flatMap fun t =>
      (path p sig pk adrs t (t * 2 ^ p.a + (Spec.base2b md p.a p.k)[t]!) p.a).1)

theorem recover_eq (p : Spec.Params) (sig md pk : Spec.Bytes) (adrs : Spec.Adrs) :
    recover p sig md pk adrs = Spec.forsPkFromSig p sig md pk adrs := by
  rw [forsPkFromSig_eq, recover]
  congr 1
  apply List.flatMap_congr
  intro t ht
  rw [forsRoot_eq]
  exact (path_correct _ _ _ _ _ _ _ (Nat.le_refl _)).1

end slhdsa.PeerFors

#print axioms slhdsa.PeerFors.sign_eq
#print axioms slhdsa.PeerFors.recover_eq
