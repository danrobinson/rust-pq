import Spec.ShakeWords
namespace Spec.Keccak
set_option maxHeartbeats 1200000

def messageWord (m : Bytes) (k : Nat) : Lane := laneBytes 0 ((m.drop (8*k)).take 8)


theorem messageWord_append (x y : Bytes) (n k : Nat) (len : x.length = 8*n) :
    messageWord (x++y) k = if k < n then messageWord x k else messageWord y (k-n) := by
  unfold messageWord
  by_cases small : k < n
  · rw [if_pos small,List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by simp;omega)]
  · rw [if_neg small,List.drop_append,List.drop_eq_nil_of_le (by omega : x.length ≤ 8*k), List.nil_append]
    rw [show 8*k-x.length=8*(k-n) by omega]

def prefixState (m : Bytes) (n : Nat) : State :=
  Array.ofFn fun k : Fin 25 => if k.val < n then messageWord m k.val else 0

theorem setAt (s : State) (i k : Nat) (w : Lane) (valid : k < s.size) :
    (s.setIfInBounds i w)[k]! = if i=k then w else s[k]! := by
  rw [getElem!_pos _ k (by simpa using valid),Array.getElem_setIfInBounds valid,getElem!_pos _ k valid]

/-- The byte-oriented FIPS 202 sponge after n complete words before the first permutation. -/
theorem aligned_prefix (m : Bytes) (n : Nat) (rate : n ≤ 16) (fits : 8*n ≤ m.length) :
    (m.take (8*n)).foldl feed initial = (prefixState m n,8*n) := by
  induction n with
  | zero =>
    simp only [Nat.mul_zero,List.take_zero,List.foldl_nil,initial,Prod.mk.injEq,and_true]
    apply ext25 _ _ (by simp) (by simp [prefixState])
    intro k hk
    rw [prefixState,ofFnAt _ _ hk]
    simp [hk]
  | succ n ih =>
    let block := (m.drop (8*n)).take 8
    have eight : block.length=8 := by simp [block]; omega
    have step := feedWord (prefixState m n) n block eight (by simp [prefixState];omega) (by omega)
    rw [if_neg (by omega : n≠16)] at step
    rw [show 8*(n+1)=8*n+8 by omega,List.take_add,List.foldl_append,ih (by omega) (by omega),step]
    apply congrArg (fun a : State => (a,8*n+8))
    apply ext25 _ _ (by simp [prefixState]) (by simp [prefixState])
    intro k hk
    rw [setAt _ _ _ _ (by simpa [prefixState] using hk)]
    simp only [prefixState,ofFnAt _ _ hk,ofFnAt _ n (by omega : n < 25)]
    by_cases eq : n=k
    · subst k
      simp [messageWord,block]
    · have below : k < n+1 ↔ k < n := by omega
      simp [eq,below]

def paddedWord (m : Bytes) (k : Nat) : Lane :=
  let data := if k=m.length/8 then 31 else if k < m.length/8 then messageWord m k else 0
  if k=16 then data ||| 0x8000000000000000 else data

def padded (m : Bytes) : State := Array.ofFn fun k : Fin 25 => paddedWord m k.val

/-- The one-permutation SHAKE input for aligned messages of at most 128 bytes. -/
theorem padded_fips (m : Bytes) (limit : m.length ≤ 128) (aligned : m.length%8=0) :
    finalize (m.foldl feed initial) = permute (padded m) := by
  have size : 8*(m.length/8)=m.length := by omega
  have absorbed := aligned_prefix m (m.length/8) (by omega) (by omega)
  rw [size,List.take_length] at absorbed
  rw [absorbed,finalize]
  apply congrArg permute
  apply ext25 _ _ (by simp [xorByte,prefixState]) (by simp [padded])
  intro k hk
  have kl : k < (prefixState m (m.length/8)).size := by simpa [prefixState] using hk
  have pos : m.length/8 < 25 := by omega
  have sixteen : 16 < (prefixState m (m.length/8)).size := by simp [prefixState]
  simp only [xorByte,show 135/8=16 by decide,show 135%8=7 by decide,aligned,Nat.mul_zero,
    BitVec.shiftLeft_zero]
  rw [setAt _ _ k _ (by simpa using kl),setAt _ _ 16 _ sixteen,setAt _ _ k _ kl]
  simp only [padded,paddedWord,prefixState,ofFnAt _ _ hk,ofFnAt _ _ (by decide : 16 < 25),ofFnAt _ _ pos]
  by_cases last : k=16
  · subst k
    by_cases equal : m.length/8=16
    · simp [equal]
    · have lt : m.length/8 < 16 := by omega
      simp [lt,Ne.symm equal,equal,Nat.not_lt_of_ge (Nat.le_of_lt lt)]
  · by_cases dom : k=m.length/8
    · subst k; simp [last,Ne.symm last]
    · simp [last,Ne.symm last,dom,Ne.symm dom]


/-- Read the requested prefix of one rate block in FIPS 202 order. -/
theorem squeeze_short (a : State) (p n : Nat) (fit : p+n ≤ 136) :
    squeeze a p n = (List.range n).map (fun i => extractByte a (p+i)) := by
  induction n generalizing p with
  | zero => simp [squeeze]
  | succ n ih =>
    have before : p ≠ 136 := by omega
    rw [squeeze,if_neg before]
    change extractByte a p :: squeeze a (p+1) n = _
    rw [ih (p+1) (by omega),List.range_succ_eq_map]
    simp [List.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end Spec.Keccak
