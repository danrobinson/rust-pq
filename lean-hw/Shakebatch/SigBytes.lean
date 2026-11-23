import Shakebatch.SigPrefix
import Spec.Correctness
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

private theorem validShake {N} {p : slhdsa.params.Params} (hp : PN p N) : (Shake.params p).Valid := by
  obtain ⟨hn,w,dg,dl,hp',hl,h,tree,ap,al,kp,kl,m⟩ := hp.valid
  constructor <;> assumption

private theorem flat_byte (f : Nat → Spec.Bytes) (n m t b : Nat)
    (len : ∀ i, (f i).length=n) (tr : t < m) (pos : b < n) :
    ((List.range m).flatMap f)[t*n+b]! = (f t)[b]! := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    by_cases before : t < m
    · have endOfTree := Nat.mul_le_mul_right n (show t+1 ≤ m by omega)
      rw [Nat.add_mul,Nat.one_mul] at endOfTree
      rw [List.getElem!_append_left _ _ _ (by rw [Spec.length_flatMap_const f n len];omega),ih before]
    · have eq : t=m := by omega
      subst t
      rw [List.getElem!_append_right _ _ _ (by rw [Spec.length_flatMap_const f n len];omega),
        Spec.length_flatMap_const f n len,Nat.add_sub_cancel_left]

theorem prefix_bytes {N} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (choices : Slice U32) (out : Buffer) (count : choices.length=p.k.val)
    (post : SigPrefix p sk seed a choices ((p.a.val+1)*N.val) choices.length out) :
    bytes out.val = (List.range p.k.val).flatMap
      (forsSignTree (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) := by
  let P := Shake.params p
  let secret := fun t => Spec.forsSkGen P (bytes sk.val) (bytes seed.val) (adrsS a)
    (t*2^P.a+(nats choices.val)[t]!)
  let auth := fun t => forsAuth P (bytes sk.val) (bytes seed.val) (adrsS a) t (nats choices.val)[t]!
  let tree := forsSignTree P (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)
  let st := (p.a.val+1)*N.val
  have nv : P.n=N.val := hp.n
  have av : P.a=p.a.val := rfl
  have sLen (t : Nat) : (secret t).length=N.val := by dsimp only [secret]; rw [Spec.forsSkGen,Spec.PRF_length P (validShake hp),nv]
  have aLen (t z : Nat) : (auth t z).length=N.val := by dsimp only [auth]; rw [forsAuth,Spec.forsNode_length P (validShake hp),nv]
  have tLen (t : Nat) : (tree t).length=st := by
    change (secret t ++ (List.range P.a).flatMap (auth t)).length=_
    simp only [List.length_append,sLen,Spec.length_flatMap_const _ _ (aLen t),av,st,Nat.add_mul,Nat.one_mul]
    omega
  have mn := hp.nok.ge16
  have sPos : 0 < st := Nat.mul_pos (by omega) (by omega)
  apply List.ext_getElem
  · rw [bytes_length,show out.val.length=choices.length*st from post.1,count,Spec.length_flatMap_const tree st tLen]
  · intro n left right
    have bound : n < choices.length*st := by rw [bytes_length] at left; change n < out.length at left; rw [post.1] at left;exact left
    let t := n/st
    let o := n%st
    let z := o/N.val
    let b := o%N.val
    have tr : t < choices.length := (Nat.div_lt_iff_lt_mul sPos).2 bound
    have within : o < st := Nat.mod_lt _ sPos
    have nr : 0 < N.val := by omega
    have lev : z ≤ p.a.val := by
      have := (Nat.div_lt_iff_lt_mul nr).2 within
      exact Nat.le_of_lt_succ this
    have byte : b < N.val := Nat.mod_lt _ nr
    have inner : z*N.val+b=o := by simpa [z,b,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div o N.val
    have whole : t*st+o=n := by simpa [t,o,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div n st
    have field := post.2 t tr z lev b byte
    rw [← getElem!_pos,← getElem!_pos]
    change (bytes out.val)[n]! = ((List.range p.k.val).flatMap tree)[n]!
    rw [← whole,flat_byte tree st _ t o tLen (count ▸ tr) within]
    conv => lhs; rw [← inner]
    rw [bytes_getElem! _ _ (by rw [inner,whole];simpa using left),← getElem!_pos]
    change sigByte out st N.val t z b = _
    rw [field]
    have ind := fors_nats_getElem! choices.val t tr
    rw [← getElem!_pos] at ind
    change (treeBlock p sk seed a choices t z)[b]! = (secret t ++ (List.range P.a).flatMap (auth t))[o]!
    cases eq : z with
    | zero =>
      have ob : o=b := by rw [eq,Nat.zero_mul,Nat.zero_add] at inner;exact inner.symm
      rw [List.getElem!_append_left _ _ _ (by rw [sLen,ob];exact byte),ob]
      simp only [treeBlock,ite_true,secret,ind];rfl
    | succ h =>
      have loc : o-N.val=h*N.val+b := by rw [eq,Nat.succ_mul] at inner;omega
      have nle : N.val ≤ o := by rw [eq,Nat.succ_mul] at inner;omega
      rw [List.getElem!_append_right _ _ _ (by rw [sLen];exact nle),
        sLen,loc,flat_byte (auth t) N.val P.a h b (aLen t) (by omega) byte]
      simp only [treeBlock,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,auth,ind];rfl
end slhdsa.ShakeBatch
