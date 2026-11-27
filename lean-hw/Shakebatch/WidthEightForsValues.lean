import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
import Cachepath.NativeVerify.HostedRecovery
import Shakeopt.ForsWideSignature
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Fors
open ShakeBatch NativeVerify

section
unseal Result
/-- Extract a value from a modeled kernel. The proofs below establish success
for every invocation used by the signing projection. -/
def value {α : Type} [Inhabited α] (result : Result α) : α :=
  match Aeneas.Data.Coinductive.ITree.unfold result with
  | .ret out => out
  | _ => default

@[simp] theorem value_ok {α : Type} [Inhabited α] (x : α) : value (ok x)=x := by simp [value, Result.ok, Aeneas.Data.Coinductive.ITree.ret, Aeneas.Data.Coinductive.ITree.unfold, Aeneas.Data.Coinductive.ITree.fold]

end

variable [machine : Machine]

def word (i : Nat) : U32 := ⟨BitVec.ofNat 32 i⟩

private theorem word_bytes (i : Nat) : Spec.toByte (word i).val 4 = Spec.toByte i 4 := by
  unfold Spec.toByte
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  change BitVec.ofNat 8 ((i % 2^32) >>> (8*(4-1-j))) = BitVec.ofNat 8 (i >>> (8*(4-1-j)))
  interval_cases j <;> apply BitVec.eq_of_toNat_eq <;> simp [Nat.shiftRight_eq_div_pow] <;> omega

def addr (a : address.Adrs) (h i : Nat) : address.Adrs :=
  {a with word2:=word h,word3:=word i}

private theorem addr_bytes (a : address.Adrs) (h i : Nat) :
    (adrsS (addr a h i)).bytes = ({adrsS a with word2:=h,word3:=i} : Spec.Adrs).bytes := by
  simp [Spec.Adrs.bytes,adrsS,addr,word_bytes]

def prfAddr (a : address.Adrs) : address.Adrs := {a with typ:=address.FORS_PRF,word2:=0#u32,word3:=0#u32}

def secret (perm : Active machine) {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) (i : Nat) : Array U8 N :=
  (value (ActiveHash.short_active perm seed (Array.repeat machine.width (addr (prfAddr a) 0 i))
    (Array.repeat machine.width sk) machine.width)).val[0]!

def leaf (perm : Active machine) {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) (i : Nat) : Array U8 N :=
  (value (ForsFused.fused perm sk seed a (Array.repeat machine.width (word i)) machine.width)).val[0]!

def parent (perm : Active machine) {N : Usize} (seed : Array U8 N) (a : address.Adrs)
    (packed : Bool) (h i : Nat) (l r : Array U8 N) : Array U8 N :=
  let ad := addr a h i
  if packed then
    (value (ActiveHash.pair_active perm seed (Array.repeat machine.width ad) (Array.repeat machine.width l)
       (Array.repeat machine.width r) machine.width)).val[0]!
  else value (shake.xmss.hash2 seed ad l r)

theorem secret_fips (perm : Active machine) (correct : ActiveCorrect machine perm) (pos : 0<machine.width.val)
    {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs) (i : Nat) :
    bytes (secret perm sk seed a i).val = Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) i := by
  obtain ⟨rows,run,out⟩ := spec_imp_exists (ActiveHash.short_correct perm correct p hp seed
    (Array.repeat machine.width (addr (prfAddr a) 0 i)) (Array.repeat machine.width sk) machine.width (by omega))
  specialize out 0 pos
  simp only [Array.repeat_val,List.getElem!_replicate _ pos,addr_bytes] at out
  unfold secret
  dsimp only at run
  rw [run,value_ok]
  simpa [Spec.forsSkGen,Spec.PRF,Shake.params,Spec.Adrs.setTypeAndClear,prfAddr,adrsS,
    address.FORS_PRF,Spec.FORS_PRF,←hp.n,List.append_assoc] using out

theorem leaf_fips (perm : Active machine) (correct : ActiveCorrect machine perm) (pos : 0<machine.width.val)
    {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) (i : Nat) :
    bytes (leaf perm sk seed a i).val = Spec.forsNode (Shake.params p) (bytes sk.val) i 0 (bytes seed.val) (adrsS a) := by
  obtain ⟨rows,run,out⟩ := spec_imp_exists (ForsFused.leaf_correct perm correct p hp sk seed a
    (Array.repeat machine.width (word i)) machine.width domain (by omega))
  specialize out 0 pos
  simp only [Array.repeat_val,List.getElem!_replicate _ pos] at out
  unfold leaf
  dsimp only at run
  rw [run,value_ok]
  simpa [Spec.forsNode,Spec.forsSkGen,Spec.F,Spec.PRF,Shake.params,Spec.Adrs.bytes,word_bytes] using out

theorem parent_fips (perm : Active machine) (correct : ActiveCorrect machine perm) (pos : 0<machine.width.val)
    {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N) (a : address.Adrs)
    (packed : Bool) (h i : Nat) (l r : Array U8 N) :
    bytes (parent perm seed a packed h i l r).val = Spec.H (Shake.params p) (bytes seed.val)
      {adrsS a with word2:=h,word3:=i} (bytes l.val ++ bytes r.val) := by
  cases packed
  · obtain ⟨row,run,out⟩ := spec_imp_exists (Shake.hash2_spec p hp seed (addr a h i) l r)
    simp only [parent,Bool.false_eq_true,ite_false,run,value_ok]
    simpa [Spec.H,Shake.params,addr_bytes] using out
  · obtain ⟨rows,run,out⟩ := spec_imp_exists (ActiveHash.pair_correct perm correct p hp seed
      (Array.repeat machine.width (addr a h i)) (Array.repeat machine.width l) (Array.repeat machine.width r) machine.width (by omega))
    specialize out 0 pos
    simp only [Array.repeat_val,List.getElem!_replicate _ pos,addr_bytes] at out
    dsimp only at run
    simp only [parent,ite_true,run,value_ok]
    simpa [Spec.H,Shake.params,←hp.n,List.append_assoc] using out

/-- Equality with a selected lane of the original mixed batch, including its
actual active count and arbitrary data in all the other lanes. -/
theorem secret_lane (perm : Active machine) (correct : ActiveCorrect machine perm)
    {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs) (i : Nat)
    (addrs : Array address.Adrs machine.width) (rows : Array (Array U8 N) machine.width) (n : Usize)
    (width : n.val ≤ machine.width.val) (j : Nat) (active : j<n.val)
    (atAddr : addrs.val[j]! = addr (prfAddr a) 0 i) (atValue : rows.val[j]! = sk) :
    ActiveHash.short_active perm seed addrs rows n ⦃ out => bytes out.val[j]!.val = bytes (secret perm sk seed a i).val ⦄ := by
  apply WP.spec_mono (ActiveHash.short_correct perm correct p hp seed addrs rows n width)
  intro out batch
  rw [batch j active,atAddr,atValue,addr_bytes,secret_fips perm correct (by omega) p hp]
  simp [Spec.forsSkGen,Spec.PRF,Shake.params,Spec.Adrs.setTypeAndClear,prfAddr,adrsS,
    address.FORS_PRF,Spec.FORS_PRF,←hp.n,List.append_assoc]

theorem fused_lane (perm : Active machine) (correct : ActiveCorrect machine perm)
    {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (ids : Array U32 machine.width) (n : Usize) (width : n.val ≤ machine.width.val)
    (j : Nat) (active : j<n.val) (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    ForsFused.fused perm sk seed a ids n ⦃ out => bytes out.val[j]!.val = bytes (leaf perm sk seed a ids.val[j]!.val).val ⦄ := by
  apply WP.spec_mono (ForsFused.leaf_correct perm correct p hp sk seed a ids n domain width)
  intro out batch
  exact (batch j active).trans (leaf_fips perm correct (by omega) p hp sk seed a domain _).symm

theorem packed_lane (perm : Active machine) (correct : ActiveCorrect machine perm)
    {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N) (a : address.Adrs) (h i : Nat)
    (addrs : Array address.Adrs machine.width) (l r : Array (Array U8 N) machine.width)
    (n : Usize) (width : n.val ≤ machine.width.val) (j : Nat) (active : j<n.val)
    (atAddr : addrs.val[j]! = addr a h i) :
    ActiveHash.pair_active perm seed addrs l r n ⦃ out => bytes out.val[j]!.val =
      bytes (parent perm seed a true h i l.val[j]! r.val[j]!).val ⦄ := by
  apply WP.spec_mono (ActiveHash.pair_correct perm correct p hp seed addrs l r n width)
  intro out batch
  rw [batch j active,atAddr,addr_bytes,parent_fips perm correct (by omega) p hp]
  simp [Spec.H,Shake.params,←hp.n,List.append_assoc]

end slhdsa.WidthEight.Fors
