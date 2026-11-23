import Shakebatch.PeerHashProof
import Mathlib.Data.List.Induction

open Spec Spec.Keccak
namespace PeerShake.Buffer

def xorNext (s : State × Nat) (b : Byte) : State × Nat := (xorByte s.1 s.2 b,s.2+1)

private theorem position (a : State) (p : Nat) (bs : Bytes) :
    (bs.foldl xorNext (a,p)).2 = p+bs.length := by
  induction bs generalizing a p with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons,xorNext,List.length_cons]
    rw [ih]; omega

private theorem partialBlock (a : State) (p : Nat) (bs : Bytes) (h : p+bs.length<136) :
    bs.foldl feed (a,p) = bs.foldl xorNext (a,p) := by
  induction bs generalizing a p with
  | nil => rfl
  | cons b bs ih =>
    have q : p+1 ≠ 136 := by simp only [List.length_cons] at h; omega
    simp only [List.foldl_cons,feed,xorNext,if_neg q]
    apply ih
    simp only [List.length_cons] at h
    omega

/-- The block kernel accumulates the little-endian XORs before applying Keccak-f. -/
def absorbBlock (a : State) (bs : Bytes) : State := permute ((bs.foldl xorNext (a,0)).1)

theorem completeBlock (a : State) (bs : Bytes) (h : bs.length=136) :
    bs.foldl feed (a,0) = (absorbBlock a bs,0) := by
  cases bs using List.reverseRecOn with
  | nil => simp at h
  | append_singleton init last =>
    have size : init.length=135 := by simpa using h
    have pos := position a 0 init
    simp only [Nat.zero_add,size] at pos
    simp only [absorbBlock,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [partialBlock a 0 init (by omega)]
    simp [feed,xorNext,pos]

structure Buffered where
  state : State
  pending : Bytes

def view (s : Buffered) := s.pending.foldl feed (s.state,0)
def initialState : Buffered := ⟨initial.1,[]⟩
def consume (a : State) (blocks : List Bytes) := blocks.foldl absorbBlock a

theorem consumeBlocks (a : State) (blocks : List Bytes) (h : ∀ b ∈ blocks,b.length=136) :
    blocks.flatten.foldl feed (a,0) = (consume a blocks,0) := by
  induction blocks generalizing a with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.flatten_cons,List.foldl_append,consume,List.foldl_cons]
    rw [completeBlock a b (h _ (by simp))]
    exact ih _ (by intro x hx; exact h x (by simp [hx]))

/-- Semantic contract checked for every normal-return LLVM path through digest_blocks.
    Full blocks may be reported in one or two callback invocations. -/
structure Split (all : Bytes) where
  blocks : List Bytes
  rest : Bytes
  blockSizes : ∀ b ∈ blocks,b.length=136
  bound : rest.length<136
  content : all=blocks.flatten++rest

def split (xs : Bytes) : Split xs :=
  if h : xs.length<136 then ⟨[],xs,(by simp),h,rfl⟩
  else
    let t := split (xs.drop 136)
    { blocks := xs.take 136 :: t.blocks
      rest := t.rest
      blockSizes := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        · simp [List.length_take,Nat.min_eq_left (by omega : 136≤xs.length)]
        · exact t.blockSizes b hb
      bound := t.bound
      content := by
        calc xs = xs.take 136 ++ xs.drop 136 := (List.take_append_drop _ _).symm
          _ = _ := by simpa only [List.flatten_cons,List.append_assoc] using congrArg (xs.take 136 ++ ·) t.content }
termination_by xs.length
decreasing_by simp; omega

def updateUsing (s : Buffered) (part : Bytes) (f : Split (s.pending++part)) : Buffered :=
  ⟨consume s.state f.blocks,f.rest⟩

theorem updateView (s : Buffered) (part : Bytes) (f : Split (s.pending++part)) :
    view (updateUsing s part f) = part.foldl feed (view s) := by
  have h := congrArg (fun data : Bytes => data.foldl feed (s.state,0)) f.content
  simpa only [List.foldl_append,consumeBlocks _ _ f.blockSizes,view,updateUsing] using h.symm

def padded (s : Buffered) : State :=
  let absorbed := (s.pending.foldl xorNext (s.state,0)).1
  permute (xorByte (xorByte absorbed s.pending.length 0x1f) 135 0x80)

theorem padView (s : Buffered) (h : s.pending.length<136) : padded s = finalize (view s) := by
  unfold padded view finalize
  rw [partialBlock _ 0 _ (by omega),position,Nat.zero_add]

/-- State returned by the i-th call to the block producer. -/
def afterBlocks (a : State) : Nat → State
  | 0 => a
  | n+1 => afterBlocks (permute a) n

def readBytes (a : State) (n : Nat) : Bytes := List.ofFn fun i : Fin n =>
  extractByte (afterBlocks a (i.val/136)) (i.val%136)

attribute [local irreducible] Spec.Keccak.permute Spec.Keccak.extractByte
set_option maxHeartbeats 1600000 in
private theorem squeezeByte (a : State) (p n i : Nat) (hp : p ≤ 136) (hi : i < n) :
    (squeeze a p n)[i]? = some (extractByte (afterBlocks a ((p+i)/136)) ((p+i)%136)) := by
  induction n generalizing a p i with
  | zero => omega
  | succ n ih =>
    by_cases endPos : p=136
    · subst p
      cases i with
      | zero => simp [squeeze,afterBlocks]
      | succ i =>
        simp only [squeeze,ite_true,List.getElem?_cons_succ]
        rw [ih _ 1 i (by decide) (by omega)]
        rw [show (136+(i+1))/136=(1+i)/136+1 by omega,
            show (136+(i+1))%136=(1+i)%136 by omega]
        rw [afterBlocks]
    · cases i with
      | zero =>
        simp [squeeze,endPos,Nat.div_eq_of_lt (by omega : p<136),
              Nat.mod_eq_of_lt (by omega : p<136),afterBlocks]
      | succ i =>
        simp only [squeeze,if_neg endPos,List.getElem?_cons_succ]
        rw [ih a (p+1) i (by omega) (by omega)]
        rw [show p+(i+1)=p+1+i by omega]

theorem readView (a : State) (n : Nat) : readBytes a n = squeeze a 0 n := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<n
  · rw [squeezeByte _ 0 _ i (by decide) hi]
    simp [readBytes,List.getElem?_eq_getElem,hi]
  · simp [readBytes,List.getElem?_eq_none_iff.mpr, Nat.le_of_not_gt hi]

def provider : PeerShake.Xof Buffered where
  empty := initialState
  update s xs := updateUsing s xs (split (s.pending++xs))
  finish s n := readBytes (padded s) n

def providerCorrect : PeerShake.Correct provider where
  consumed s xs := s.pending.length<136 ∧ view s=xs.foldl feed initial
  empty := by exact ⟨by decide,rfl⟩
  update s pre part h := by
    refine ⟨(split (s.pending ++ part)).bound,?_⟩
    rw [List.foldl_append,← h.2]
    exact updateView _ _ _
  finish s pre n h := by
    change readBytes (padded s) n = squeeze (finalize _) 0 n
    rw [readView,padView s h.1,h.2]

#print axioms providerCorrect
end PeerShake.Buffer
