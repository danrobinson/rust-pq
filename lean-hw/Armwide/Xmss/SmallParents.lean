import Armwide.Xmss.SmallHash
import Armwide.Xmss.PhysicalParents

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss

def smallPass (state : List Spec.SHA256.Word) (a : Spec.Adrs) (first count : Nat)
    (input : Nat → Spec.Bytes) (n : Nat) :=
  (List.range n).foldl (fun vals j => Function.update vals j
    (smallHash (j<count/4*4) state a (first+j) (vals (2*j)) (vals (2*j+1)))) input

/-- Each store reads both original children. All later child rows remain available
across every prefix of the native 4/2/1 lane schedule. -/
theorem smallPass_fips (p : Spec.Params) [Fact (p.family=.sha2)] (width : p.n=16)
    (pk : Spec.Bytes) (seedLength : pk.length=16) (a : Spec.Adrs) (height : a.word2<65536)
    (first count : Nat) (input : Nat → Spec.Bytes) (lens : ∀ j<2*count,(input j).length=16)
    (n : Nat) (bound : n≤count) :
    let out := smallPass (slhdsa.seedState 16 pk) a first count input n
    (∀ j<n, out j=Spec.H p pk {a with word3:=first+j} (input (2*j)++input (2*j+1))) ∧
    (∀ j, n≤j → out j=input j) := by
  induction n with
  | zero => simp [smallPass]
  | succ n ih =>
    obtain ⟨earlier,later⟩ := ih (by omega)
    simp only [smallPass,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    constructor
    · intro j hj
      by_cases here : n=j
      · subst j
        rw [Function.update_self]
        change smallHash _ _ _ _ (smallPass _ _ _ _ _ _ _) (smallPass _ _ _ _ _ _ _) = _
        rw [later _ (by omega),later _ (by omega)]
        exact smallHash_fips p width pk seedLength a height _ _ _ (lens _ (by omega)) (lens _ (by omega)) _
      · rw [Function.update_of_ne (Ne.symm here)]
        exact earlier _ (by omega)
    · intro j hj
      rw [Function.update_of_ne (by omega : j≠n)]
      exact later _ (by omega)

def rowsBuffer (cap N : Usize) (vals : Nat → Spec.Bytes) : Nodes N cap :=
  .from (List.ofFn (fun i : Fin cap.val => row N (vals i.val))) (by simp)

theorem read_row (cap N : Usize) (vals : Nat → Spec.Bytes) (j : Nat) (bound : j<cap.val)
    (size : (vals j).length=N.val) :
    bytes (rowsBuffer cap N vals).val[j]!.val=vals j := by
  simp only [rowsBuffer,Array.from_val]
  rw [getElem!_pos _ j (by simpa using bound),List.getElem_ofFn,row_eq _ _ size]

def smallBuffer {cap : Usize} (state : Array U32 8#usize) (a : address.Adrs) (first : U32)
    (roots : Nodes 16#usize cap) (count : Usize) : Nodes 16#usize cap :=
  let vals := smallPass (wv state.val) (adrsS a) first.val count.val (old roots) count.val
  rowsBuffer cap 16#usize vals

theorem small_level {cap : Usize} (p : params.Params) (hp : PN p 16#usize) (seed : hash.Seed 16#usize)
    (hs : SeedOk seed) (a : address.Adrs) (height : (adrsS a).word2<65536)
    (first : U32) (roots : Nodes 16#usize cap) (count : Usize) (size : count.val≤cap.val) :
    ∀ j<count.val, bytes (smallBuffer seed.state a first roots count).val[j]!.val =
      parent p seed a first roots j := by
  have width : (paramsS p).n=16 := congrArg UScalar.val hp.n_eq
  have eqst : wv seed.state.val = seedState 16 (bytes seed.pk_seed.val) := hs.1
  have pairs := (smallPass_fips (paramsS p) width (bytes seed.pk_seed.val) (by simp)
    (adrsS a) height first.val count.val (old roots) (by intro j _;simp [old])
    count.val (by omega)).1
  intro j hj
  unfold smallBuffer
  rw [eqst]
  have val := pairs j hj
  have len := congrArg List.length val
  rw [Spec.H_length _ hp.valid,width] at len
  exact (read_row cap 16#usize _ j (by omega) len).trans val

end slhdsa.ArmXmss
