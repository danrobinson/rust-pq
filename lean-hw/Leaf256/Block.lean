import Leaf256.Prefix
import Leaf256.Pack
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

def blockOf (f : Nat → Word) : Spec.Bytes :=
  List.ofFn fun i : Fin 64 => (f (i.val / 4)).extractLsb' (8*(3 - i.val%4)) 8

theorem word_blockOf (f : Nat → Word) (k : Nat) (hk : k < 16) :
    word (blockOf f) (4*k) = f k := by
  have byte (i : Nat) (hi : i < 64) : (blockOf f)[i]! = (f (i/4)).extractLsb' (8*(3-i%4)) 8 := by
    unfold blockOf
    rw [getElem!_pos _ _ (by simpa using hi),List.getElem_ofFn]
  unfold word
  simp (disch := omega) only [byte]
  simp (disch := omega) only [show 4*k/4 = k by omega,show (4*k+1)/4 = k by omega,
    show (4*k+2)/4 = k by omega,show (4*k+3)/4 = k by omega,
    show 4*k%4 = 0 by omega,show (4*k+1)%4 = 1 by omega,show (4*k+2)%4 = 2 by omega,
    show (4*k+3)%4 = 3 by omega]
  generalize f k = w
  bv_decide

def prfWords (base : Nat → Word) (idx : Word) (k : Nat) : Word :=
  if k = 4 then base 4 ||| (idx >>> 16)
  else if k = 5 then (idx <<< 16) ||| (base 5 &&& 0xffff)
  else base k

def leafWords (base prf : Nat → Word) (idx change : Word) (n k : Nat) : Word :=
  if k = 2 then base 2 ^^^ change
  else if k = 5 then (idx <<< 16) ||| (prf 0 >>> 16)
  else if k = 5+n/4 then (prf (n/4-1) <<< 16) ||| (base k &&& 0xffff)
  else if 6 ≤ k ∧ k < 5+n/4 then interior (prf (k-6)) (prf (k-5))
  else prfWords base idx k

private theorem equal_round (W V : List Word) (s : State) (i : Nat) (h : W[i]! = V[i]!) :
    round W s i = round V s i := by
  rcases s with ⟨a,b,c,d,e,f,g,k⟩
  simp only [round,h]

private theorem equal_prefix (W V : List Word) (s : State) (t : Nat) (h : ∀ k < t, W[k]! = V[k]!) :
    (List.range t).foldl (round W) s = (List.range t).foldl (round V) s := by
  induction t with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih (fun k hk => h k (by omega))]
    exact equal_round _ _ _ _ (h _ (by omega))

theorem transfer_prefix {state : Array Reg 8#usize} {iv : Fin 16 → State}
    {a b : Fin 16 → Spec.Bytes} {t : Nat} (small : t ≤ 16)
    (h : ∀ j k, k < t → word (a j) (4*k) = word (b j) (4*k))
    (ht : Trace state (fun j => schedule (a j)) iv t) :
    Trace state (fun j => schedule (b j)) iv t := by
  intro j
  rw [ht j]
  apply equal_prefix
  intro k hk
  rw [slhdsa.schedule_lt16 _ _ (by omega),slhdsa.schedule_lt16 _ _ (by omega),h j k hk]

end slhdsa.X86.Leaf
