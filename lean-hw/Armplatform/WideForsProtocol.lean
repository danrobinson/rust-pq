import Armplatform.WideForsTail

namespace slhdsa.WideFors
set_option maxHeartbeats 1600000

/-- Active rows contain a node and an absolute index. All rows at a level
read the old row before writing its parent. -/
def rows (p : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) :
    Nat → Nat → Spec.Bytes × Nat
  | 0, t =>
    let pos := t * 2^p.a + digits[t]!
    (Spec.F p pk {a with word2 := 0,word3 := pos} (Spec.block p sig (t*(p.a+1))), pos)
  | h+1,t =>
    let (node,pos) := rows p sig pk a digits h t
    let sibling := Spec.block p sig (t*(p.a+1)+1+h)
    (Spec.H p pk {a with word2 := h+1,word3 := pos/2} (pairMsg node sibling pos), pos/2)

theorem level (p : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat)
    (t h : Nat) (hh : h ≤ p.a) :
    rows p sig pk a digits h t = forsClimbAt p sig pk a digits t h ∧
    (rows p sig pk a digits h t).2 = t*2^(p.a-h) + digits[t]! / 2^h := by
  induction h with
  | zero => simp [rows,forsClimbAt,forsLeaf]
  | succ h ih =>
    have lt : h < p.a := by omega
    obtain ⟨atRow,index⟩ := ih (by omega)
    let old := rows p sig pk a digits h t
    have pow : 2^(p.a-h) = 2*2^(p.a-(h+1)) := by rw [← pow_succ']; congr 1; omega
    have pos : old.2 = 2*(t*2^(p.a-(h+1))) + digits[t]!/2^h := by
      change (rows ..).2 = _
      rw [index,pow]; ring
    have par : old.2%2 = (digits[t]! / 2^h)%2 := by omega
    have half : old.2/2 = t*2^(p.a-(h+1)) + digits[t]!/2^(h+1) := by
      rw [pos,pow_succ,← Nat.div_div_eq_div_mul]; omega
    have next : forsClimbAt p sig pk a digits t (h+1) =
        forsClimbStep p digits[t]! (forsAuthPath p sig t) pk a old h := by
      simp only [old,atRow,forsClimbAt,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    refine ⟨?_,half⟩
    change (Spec.H p pk {a with word2 := h+1,word3 := old.2/2}
      (pairMsg old.1 (Spec.block p sig (t*(p.a+1)+1+h)) old.2),old.2/2) = _
    rw [next]
    rcases e : (digits[t]!/2^h)%2 with _ | x
    · simp only [forsClimbStep,pairMsg,par,e,↓reduceIte,fors_block_auth _ _ _ _ lt]
    · have ne : (digits[t]!/2^h)%2 ≠ 0 := by omega
      have sub : (old.2-1)/2=old.2/2 := by omega
      simp only [forsClimbStep,pairMsg,par,ne,↓reduceIte,sub,fors_block_auth _ _ _ _ lt]

def recover (p : Spec.Params) (sig md pk : Spec.Bytes) (a : Spec.Adrs) :=
  let dig := Spec.base2b md p.a p.k
  let roots := (List.range p.k).flatMap (fun t => (rows p sig pk a dig p.a t).1)
  Spec.T p pk {a.setTypeAndClear Spec.FORS_ROOTS with keypair := a.keypair} roots

theorem recover_fips (p : Spec.Params) (sig md pk : Spec.Bytes) (a : Spec.Adrs) :
    recover p sig md pk a = Spec.forsPkFromSig p sig md pk a := by
  rw [forsPkFromSig_eq]
  unfold recover
  apply congrArg (Spec.T p pk _)
  apply List.flatMap_congr
  intro t _
  rw [forsRoot_eq, (level p sig pk a _ t p.a (by omega)).1]

end slhdsa.WideFors
