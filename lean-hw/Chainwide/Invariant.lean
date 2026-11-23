import Chainwide.Reference
import Leaf256.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open Spec.SHA256
abbrev Words := Array Reg 16#usize
abbrev lanes (w : Words) (j : Fin 16) := fun k : Nat => w.val[k]! j

def Ready (p : Fin 16 → Lane) (n t : Nat) (start stop fixed : Reg) (w : Words) :=
  ∀ j : Fin 16, Live start stop t j → ∀ ctr k, k < 16 →
    addressWord (lanes w j) (fixed j) ctr k = word (packet (p j).head ctr ((p j).value n t) (p j).tail) (4*k)

def lastHash (p : Lane) (n : Nat) (stop : Word) := p.hash n (stop.toNat-1-p.first)

def Kept (p : Fin 16 → Lane) (n t : Nat) (start stop : Reg) (orig : U16) (saved : Hash) :=
  ∀ j : Fin 16, orig.bv.getLsbD j.val → ¬ Live start stop t j → ∀ k < n/4,
    saved.val[k]! j = (lastHash (p j) n (stop j))[k]!

def blockAtStep (w : Words) (fixed current : Reg) (j : Fin 16) :=
  Leaf.blockOf (addressWord (lanes w j) (fixed j) (current j))

theorem hash_active (p : Fin 16 → Lane) (n t : Nat) (start stop current fixed : Reg)
    (iv h : Hash) (w : Words) (ready : Ready p n t start stop fixed w)
    (length : ∀ j, (p j).head.length = 18 ∧ ((p j).value n t).length = n ∧
      22+n+(p j).tail.length = 64)
    (first : ∀ j, (p j).first = (start j).toNat)
    (state : ∀ j, (p j).state = stateWords (laneState iv j))
    (ctr : ∀ j, Live start stop t j → (current j).toNat = (start j).toNat+t)
    (hh : ∀ j, stateWords (laneState h j) = compress (stateWords (laneState iv j)) (blockAtStep w fixed current j)) :
    ∀ j, Live start stop t j → ∀ k < 8, h.val[k]! j = ((p j).hash n t)[k]! := by
  intro j live k hk
  let block := packet (p j).head (current j) ((p j).value n t) (p j).tail
  obtain ⟨hlen,vlen,tlen⟩ := length j
  have blen : block.length = 64 := by simp [block,packet,Spec.toByte,hlen,vlen]; omega
  have eq : blockAtStep w fixed current j = block := by
    apply Eq.trans _ (Leaf.block_words_inverse block blen)
    exact Leaf.block_congr _ _ (ready j live (current j))
  have heq : current j = BitVec.ofNat 32 ((p j).first+t) := by
    rw [first,← ctr j live]; simp
  rw [show h.val[k]! j = (stateWords (laneState h j))[k]! from Leaf.lane_lookup h j k hk,hh j,eq]
  simp only [Lane.hash,state,block,heq]

private theorem value_congr (a b h g : Nat → Word) (n k : Nat)
    (ha : ∀ i < 16, a i = b i) (hh : ∀ i < 8, h i = g i)
    (shape : n=16 ∨ n=24 ∨ n=32) (hk : k < 16) :
    valueWord a h n k = valueWord b g n k := by
  unfold valueWord
  split_ifs <;> simp (disch := omega) only [hh,ha]

theorem ready_next (p : Fin 16 → Lane) (n t : Nat) (start stop current fixed : Reg)
    (w addressed out : Words) (hash : Hash) (shape : n=16 ∨ n=24 ∨ n=32)
    (ready : Ready p n t start stop fixed w)
    (hl : ∀ j, (p j).head.length = 18 ∧ ((p j).value n t).length = n)
    (aw : ∀ k < 16, ∀ j, addressed.val[k]! j = addressWord (lanes w j) (fixed j) (current j) k)
    (hw : ∀ j, Live start stop t j → ∀ k < 8, hash.val[k]! j = ((p j).hash n t)[k]!)
    (nw : ∀ k < 16, ∀ j, out.val[k]! j = valueWord (lanes addressed j) (fun i => hash.val[i]! j) n k) :
    Ready p n (t+1) start stop fixed out := by
  intro j live next k hk
  have old : Live start stop t j := by unfold Live at *; omega
  let packed := addressWord (lanes w j) (fixed j) (current j)
  let vals := fun (i : Nat) => ((p j).hash n t)[i]!
  have h k (hk : k<16) : out.val[k]! j = valueWord packed vals n k :=
    (nw k hk j).trans (value_congr _ _ _ _ _ k (fun i hi => aw i hi j) (hw j old) shape hk)
  have heq : addressWord (lanes out j) (fixed j) next k =
      addressWord (valueWord packed vals n) (fixed j) next k := by
    simp only [addressWord,lanes,h _ hk,h 5 (by decide)]
  rw [heq]
  exact next_layout _ ((p j).hash n t) _ _ _ _ _ _ n k (hl j).1 (hl j).2
    (sha_compress_length _ _) shape hk (ready j old)

theorem kept_next (p : Fin 16 → Lane) (n t : Nat) (start stop : Reg) (orig finished : U16)
    (saved hash result : Hash) (shape : n ≤ 32) (first : ∀ j, (p j).first = (start j).toNat)
    (old : Kept p n t start stop orig saved)
    (hw : ∀ j, Live start stop t j → ∀ k < 8, hash.val[k]! j = ((p j).hash n t)[k]!)
    (last : ∀ j : Fin 16, finished.bv.getLsbD j.val =
      decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat))
    (kept : ∀ k < n/4, ∀ j : Fin 16, orig.bv.getLsbD j.val →
      result.val[k]! j = if finished.bv.getLsbD j.val then hash.val[k]! j else saved.val[k]! j) :
    Kept p n (t+1) start stop orig result := by
  intro j set ended k hk
  rw [kept k hk j set,last j]
  by_cases live : Live start stop t j
  · have endEq : (start j).toNat+t+1 = (stop j).toNat := by unfold Live at *; omega
    simp only [live,endEq,and_self,decide_true,ite_true]
    rw [hw j live k (by omega)]
    unfold lastHash
    rw [first j,show (stop j).toNat-1-(start j).toNat = t by omega]
  · simpa only [live,false_and,decide_false,Bool.false_eq_true,ite_false] using old j set live k hk

end slhdsa.X86.Chain
