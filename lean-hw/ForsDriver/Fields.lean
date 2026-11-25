import ForsDriver.Program
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch
set_option maxHeartbeats 800000

def Fields (n trees levels stride : Nat) (value : Nat → Nat → Spec.Bytes)
    (present : Nat → Nat → Prop) (sig : Buffer) : Prop :=
  sig.length=trees*stride ∧ ∀ t<trees, ∀ z<levels, ∀ b<n, present t z →
    sigByte sig stride n t z b=(value t z)[b]!

theorem Fields.mono {n trees levels stride value present required sig}
    (old : Fields n trees levels stride value present sig)
    (covers : ∀ t z, t<trees → z<levels → required t z → present t z) :
    Fields n trees levels stride value required sig :=
  ⟨old.1,fun t ht z hz b hb h => old.2 t ht z hz b hb (covers t z ht hz h)⟩

theorem Fields.store {N : Usize} {trees levels stride : Nat} (value : Nat → Nat → Spec.Bytes)
    (present required : Nat → Nat → Prop) (before after : Buffer) (row : Array U8 N) (tree level : Nat)
    (ht : tree<trees) (hz : level<levels) (shape : stride=levels*N.val)
    (old : Fields N.val trees levels stride value present before)
    (write : after.val=before.val.setSlice! (tree*stride+level*N.val) row.val)
    (correct : bytes row.val=value tree level)
    (covers : ∀ t z, t<trees → z<levels → required t z → (t=tree ∧ z=level) ∨ present t z) :
    Fields N.val trees levels stride value required after := by
  have len : before.val.length=trees*stride := old.1
  refine ⟨by change after.val.length=_;rw [write]; simpa using len,?_⟩
  intro t tOk z zOk b byte h
  have off (u : Nat) (hu : u<levels) : u*N.val+N.val≤stride := by
    rw [shape,←Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have fits (t : Nat) (inside : t<trees) : t*stride+stride≤before.val.length := by
    rw [len,←Nat.succ_mul]; exact Nat.mul_le_mul_right _ inside
  by_cases eq : t=tree ∧ z=level
  · rcases eq with ⟨rfl,rfl⟩
    have h1 := off z zOk
    have h2 := fits t tOk
    rw [sigByte,write,List.getElem!_setSlice!_middle _ _ _ _ (by simp;omega)]
    rw [show t*stride+(z*N.val+b)-(t*stride+z*N.val)=b by omega,←correct]
    rw [bytes_getElem! _ b (by simpa using byte)]
    have hb : b < row.val.length := by simpa using byte
    simp [List.getElem?_eq_getElem hb]
  · have original := old.2 t tOk z zOk b byte ((covers t z tOk zOk h).resolve_left eq)
    rw [←original,sigByte,sigByte,write]
    have zOff := off z zOk
    have levelOff := off level hz
    by_cases earlier : t<tree
    · have diff := Nat.mul_le_mul_right stride earlier
      rw [Nat.succ_mul] at diff
      rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    · by_cases later : tree<t
      · have diff := Nat.mul_le_mul_right stride later
        rw [Nat.succ_mul] at diff
        rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp; omega)]
      · have same : t=tree := by omega
        subst t
        by_cases beforeLevel : z<level
        · have diff := Nat.mul_le_mul_right N.val beforeLevel
          rw [Nat.succ_mul] at diff
          rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
        · have diff := Nat.mul_le_mul_right N.val (show level+1≤z by omega)
          rw [Nat.succ_mul] at diff
          rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp; omega)]

theorem auth_block {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : Slice U32) (t h : Nat) (inside : h<p.a.val) :
    treeBlock p sk seed a choices t (h+1)=Spec.forsNode (Shake.params p) (bytes sk.val)
      (((t*2^p.a.val+choices.val[t]!.val)/2^h) ^^^ 1) h (bytes seed.val) (adrsS a) := by
  simp only [treeBlock,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,forsAuth,
    sibling_eq t choices.val[t]!.val p.a.val h inside]
  rfl

end slhdsa.ForsDriver
