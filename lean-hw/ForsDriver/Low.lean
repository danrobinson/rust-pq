import ForsDriver.LowRows
import ForsDriver.ForsIndices
import ForsDriver.Columns
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option maxHeartbeats 1800000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]

def LowFields {N : Usize} (p : params.Params) (choices : Slice U32) (sk seed : Array U8 N)
    (addr : address.Adrs) (stride : Usize) (col : Nat) (sig : Buffer) :=
  Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed addr choices) (fun _ z => z≤col) sig

private theorem block {N : Usize} (p : params.Params) (choices : Slice U32) (sk seed : Array U8 N)
    (addr : address.Adrs) (h t : Nat) (range : h < p.a.val) :
    nodeValue p sk seed addr h (sibling choices p.a t h) = treeBlock p sk seed addr choices t (h+1) :=
  (auth_block p sk seed addr choices t h range).symm

theorem low0_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (addr : address.Adrs) (stride : Usize) (sig : Buffer)
    (size : choices.length ≤ 35) (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (shape : stride.val=(p.a.val+1)*N.val) (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (h : 0 < p.a.val) (old : LowFields p choices sk seed addr stride 0 sig) :
    low0 p choices sk seed addr stride sig ⦃ out => LowFields p choices sk seed addr stride 1 out ⦄ := by
  unfold low0
  step with level_zero choices p.a _ hp.valid.a_le size digits as ⟨ids,values⟩
  step with leaf_prefix p hp sk seed addr ids choices.len size domain perm as ⟨rows,computed⟩
  apply column1 choices.len stride sig rows (treeBlock p sk seed addr choices) (p.a.val+1) size shape (by omega)
      (old.mono (by intros;omega))
  intro t ht
  rw [computed t ht,values t ht]
  exact block p choices sk seed addr 0 t h

theorem low1_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (addr tree : address.Adrs) (stride : Usize) (sig : Buffer)
    (size : choices.length ≤ 35) (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (eqTree : adrsS tree=adrsS addr)
    (shape : stride.val=(p.a.val+1)*N.val) (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (h : 1 < p.a.val) (old : LowFields p choices sk seed addr stride 1 sig) :
    low1 p choices sk seed addr tree stride sig ⦃ out => LowFields p choices sk seed addr stride 2 out ⦄ := by
  unfold low1
  step with level_one choices p.a _ _ hp.valid.a_le size digits as ⟨q,leaves,nodes⟩
  obtain ⟨li,ni⟩ := q
  dsimp only at leaves nodes ⊢
  step as ⟨two,tv⟩
  change two.val=2*choices.length at tv
  step with leaf_prefix p hp sk seed addr li two (by change two.val ≤ 70;omega) domain perm as ⟨rows,computed⟩
  have child (t c : Nat) (ht : t < choices.length) (hc : c < 2) :
      bytes rows.val[2*t+c]!.val=nodeValue p sk seed addr 0 (2*ni.val[t]!.val+c) := by
    rw [computed _ (by omega),leaves t ht c hc,nodes t ht]
  step with pair_prefix p hp sk seed addr tree 1#u32 0 ni rows choices.len two size (by change two.val ≤ 70;omega)
    (by change 2*choices.length ≤ two.val;omega) eqTree rfl
    (fun t ht => by simpa only [Nat.add_zero] using child t 0 ht (by decide))
    (fun t ht => child t 1 ht (by decide)) perm as ⟨roots,hashed⟩
  apply column2 choices.len stride sig roots (treeBlock p sk seed addr choices) (p.a.val+1) size shape (by omega)
      (old.mono (by intros;omega))
  intro t ht
  rw [hashed t ht,nodes t ht]
  exact block p choices sk seed addr 1 t h

theorem low2_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (addr tree : address.Adrs) (stride : Usize) (sig : Buffer)
    (size : choices.length ≤ 35) (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (eqTree : adrsS tree=adrsS addr) (shape : stride.val=(p.a.val+1)*N.val)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (h : 2 < p.a.val) (old : LowFields p choices sk seed addr stride 2 sig) :
    low2 p choices sk seed addr tree stride sig ⦃ out => LowFields p choices sk seed addr stride 3 out ⦄ := by
  unfold low2
  step with level_two choices p.a _ _ _ hp.valid.a_le size digits as ⟨q,leaves,mids,nodes⟩
  obtain ⟨li,mid,ni⟩ := q
  dsimp only at leaves mids nodes ⊢
  step as ⟨four,fv⟩
  change four.val=4*choices.length at fv
  step with leaf_prefix p hp sk seed addr li four (by change four.val ≤ 140;omega) domain perm as ⟨rows,computed⟩
  step as ⟨two,tv⟩
  change two.val=2*choices.length at tv
  have child (j c : Nat) (hj : j < two.val) (hc : c < 2) :
      bytes rows.val[2*j+c]!.val=nodeValue p sk seed addr 0 (2*mid.val[j]!.val+c) := by
    let t := j/2
    let b := j%2
    have ht : t<choices.length := by change j/2 < choices.length;omega
    have hb : b<2 := Nat.mod_lt _ (by decide)
    have index : 2*t+b=j := by dsimp [t,b];omega
    have eq : 2*j+c=4*t+(2*b+c) := by omega
    have m := mids t ht b hb
    rw [index] at m
    rw [computed _ (by omega),eq,leaves t ht (2*b+c) (by omega),m]
    congr 1;omega
  step with pair_prefix p hp sk seed addr tree 1#u32 0 mid rows two four (by change two.val ≤ 70;omega)
    (by change four.val ≤ 140;omega) (by omega) eqTree rfl
    (fun j hj => by simpa only [Nat.add_zero] using child j 0 hj (by decide))
    (fun j hj => child j 1 hj (by decide)) perm as ⟨parents,half⟩
  have second (t c : Nat) (ht : t < choices.length) (hc : c < 2) :
      bytes parents.val[2*t+c]!.val=nodeValue p sk seed addr 1 (2*ni.val[t]!.val+c) := by
    rw [half _ (by omega),mids t ht c hc,nodes t ht]
  step with pair_prefix p hp sk seed addr tree 2#u32 1 ni parents choices.len two size (by change two.val ≤ 70;omega)
    (by change 2*choices.length ≤ two.val;omega) eqTree rfl
    (fun t ht => by simpa only [Nat.add_zero] using second t 0 ht (by decide))
    (fun t ht => second t 1 ht (by decide)) perm as ⟨roots,hashed⟩
  apply column3 choices.len stride sig roots (treeBlock p sk seed addr choices) (p.a.val+1) size shape (by omega)
      (old.mono (by intros;omega))
  intro t ht
  rw [hashed t ht,nodes t ht]
  exact block p choices sk seed addr 2 t h
end slhdsa.ForsDriver
