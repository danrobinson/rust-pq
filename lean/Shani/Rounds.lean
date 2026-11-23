import Shani.Funs
import Spec.Sha256
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open core.core_arch.x86

theorem round_eq (w : List Word) (s : State) (i : Nat) :
    intelRound s (w[i]! + Spec.SHA256.K[i]!) = Spec.SHA256.round w s i := by
  rcases s with ⟨a,b,c,d,e,f,g,h⟩
  simp only [intelRound, Spec.SHA256.round]
  change ((ch e f g + bsig1 e + (w[i]!+Spec.SHA256.K[i]!) + h) + maj a b c + bsig0 a,a,b,c,
    (ch e f g + bsig1 e + (w[i]!+Spec.SHA256.K[i]!) + h)+d,e,f,g) =
    ((h+bsig1 e+ch e f g+Spec.SHA256.K[i]!+w[i]!) + (bsig0 a+maj a b c),a,b,c,
      d+(h+bsig1 e+ch e f g+Spec.SHA256.K[i]!+w[i]!),e,f,g)
  generalize ch e f g = ch
  generalize maj a b c = m
  generalize bsig0 a = s0
  generalize bsig1 e = s1
  generalize w[i]! = wi
  generalize Spec.SHA256.K[i]! = ki
  simp only [Prod.mk.injEq, true_and, and_true]
  constructor <;> ac_rfl

def cdgh (s : State) : Reg :=
  let (_,_,c,d,_,_,g,h) := s
  ⟨h,g,d,c⟩

theorem decode_pair (s : State) : decode (abef s) (cdgh s) = s := by
  rcases s with ⟨a,b,c,d,e,f,g,h⟩; rfl

theorem cdgh_two (s : State) (x y : Word) :
    cdgh (intelRound (intelRound s x) y) = abef s := by
  rcases s with ⟨a,b,c,d,e,f,g,h⟩; rfl

def group (W : List Word) (i : Nat) : Reg := ⟨W[i]!, W[i+1]!, W[i+2]!, W[i+3]!⟩

theorem shuffle14 (x : Reg) : sse2._mm_shuffle_epi32 14#i32 x =
    ok ⟨x.w2,x.w3,x.w0,x.w0⟩ := rfl

theorem align4 (a b : Reg) : ssse3._mm_alignr_epi8 4#i32 a b = ok ⟨b.w1,b.w2,b.w3,a.w0⟩ := by
  simp [ssse3._mm_alignr_epi8, get, show (4#i32).bv.toNat % 256 = 4 by decide]

def after (W : List Word) (initial : State) (i : Nat) := (List.range i).foldl (Spec.SHA256.round W) initial

theorem after_succ (W : List Word) (s : State) (i : Nat) :
    after W s (i+1) = intelRound (after W s i) (W[i]!+Spec.SHA256.K[i]!) := by
  rw [round_eq]
  simp [after, List.range_succ, List.foldl_append]

theorem two (s : State) (x y z u : Word) :
    sha._mm_sha256rnds2_epu32 (cdgh s) (abef s) ⟨x,y,z,u⟩ =
      ok (abef (intelRound (intelRound s x) y)) := by
  simp [sha._mm_sha256rnds2_epu32, decode_pair]

theorem abef_rounds {α} (f : Reg → Reg → Result α) (W : List Word) (s : State) (i : Nat) :
    (do
      let wk ← sse2._mm_add_epi32 (group W i) (group Spec.SHA256.K i)
      let h ← sha._mm_sha256rnds2_epu32 (cdgh (after W s i)) (abef (after W s i)) wk
      let hi ← sse2._mm_shuffle_epi32 14#i32 wk
      let l ← sha._mm_sha256rnds2_epu32 (abef (after W s i)) h hi
      f l h) = f (abef (after W s (i+4))) (cdgh (after W s (i+4))) := by
  simp only [sse2._mm_add_epi32, group, bind_ok, shuffle14, two]
  rw [← after_succ, ← after_succ]
  have eq2 : cdgh (after W s (i+2)) = abef (after W s i) := by
    rw [show i+2 = (i+1)+1 by omega, after_succ, after_succ, cdgh_two]
  rw [← eq2, two, ← after_succ, ← after_succ]
  have eq4 : cdgh (after W s (i+4)) = abef (after W s (i+2)) := by
    rw [show i+4 = ((i+2)+1)+1 by omega, after_succ, after_succ, cdgh_two]
  rw [eq4]
  simp only [bind_ok, Nat.add_assoc, Nat.reduceAdd]

#print axioms round_eq
end slhdsa.Intel
