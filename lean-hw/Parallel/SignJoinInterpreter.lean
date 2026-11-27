import Parallel.SignJoin
import Parallel.SignJoinPlan
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignJoin
open Spec ParallelSigning ParallelFused
noncomputable section
/-- Embed semantic results in the bounded Rust carriers used by the join replay. -/
def boxed {α : Type} (l : List α) := alloc.vec.Vec.from (l.take Usize.max) (by simp)
def raw (b : Bytes) : List U8 := b.map (fun v => ⟨v⟩)
private theorem unbox {α : Type} (l : List α) (h : l.length≤Usize.max) : (boxed l).val=l := by
  simp [boxed,List.take_of_length_le h]
private theorem raw_bytes (b : Bytes) : bytes (raw b)=b := by simp [raw,bytes,Function.comp_def]

def fixed (N : Usize) (b : Bytes) : Array U8 N :=
  if h : b.length=N.val then Array.from (raw b) (by simpa [raw] using h) else Array.repeat N 0#u8
private theorem fixed_bytes (N : Usize) (b : Bytes) (h : b.length=N.val) : bytes (fixed N b).val=b := by
  simpa [fixed,h] using raw_bytes b

def authValue (p : Spec.Params) (sk pk : Bytes) (tree leaf i : Nat) :=
  let j := i/p.hp
  let pos := loc p.hp tree leaf j
  xmssNode p sk ((pos.2/2^(i%p.hp)) ^^^ 1) (i%p.hp) pk (addr j pos.1)

def wotsValue (p : Spec.Params) (sk pk first : Bytes) (tree leaf j : Nat) :=
  let pos := loc p.hp tree leaf j
  wotsSign p (ParallelFused.message p first sk pk tree leaf j) sk pk
    {(addr j pos.1).setTypeAndClear WOTS_HASH with keypair:=pos.2}

/-- Interpret the recorded primitive-call identities for each physical cell.
The Rust replay compares the entire symbolic byte strings, before the final copy.
The values here are FIPS interpretations of those primitive calls. -/
def interpreted (plan : PhysicalRows) : Join := fun {N} p md sk seed a _ tree leaf _ => do
  let P := Shake.params p
  let forest := ParallelCached.forsRows P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
  let forestBytes := (expand plan.forest).flatMap (fun i => forest[i]!)
  let first := forsPkFromSig P forestBytes (bytes md.val) (bytes seed.val) (adrsS a)
  let auth := (expand plan.auth).map (fun i => fixed N (authValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val i))
  let wots := (expand plan.wots).map (fun j => some (boxed (raw
    (wotsValue P (bytes sk.val) (bytes seed.val) first tree.val leaf.val j))))
  ok (some (boxed (raw forestBytes)),some (boxed auth),boxed wots)

private theorem gather (rows : List Bytes) : (List.range rows.length).flatMap (fun i => rows[i]!) = rows.flatten := by
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem <;> simp
  intro i h
  rw [List.getElem?_eq_getElem h]
  rfl

theorem interpreted_ready {N : Usize} (p : params.Params) (hp : PN p N) (plan : PhysicalRows)
    (found : lookup (Shake.params p)=some plan) : JoinLawAt (interpreted plan) N p := by
  intro md sk seed a r tree leaf threads _ _ _ _ _
  let P := Shake.params p
  let rows := ParallelCached.forsRows P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
  let first := forsPkFromSig P rows.flatten (bytes md.val) (bytes seed.val) (adrsS a)
  let au := authValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val
  let wo := wotsValue P (bytes sk.val) (bytes seed.val) first tree.val leaf.val
  let forest := boxed (raw rows.flatten)
  let auth := boxed ((List.range (P.d*P.hp)).map (fun i => fixed N (au i)))
  let sigs := boxed ((List.range P.d).map (fun i => some (boxed (raw (wo i)))))
  have valid : P.Valid := by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hp.valid;constructor <;> assumption
  have dSize := valid.d_le
  have hSize := valid.hp_le
  have countMax : P.d*P.hp≤Usize.max := (Nat.mul_le_mul dSize hSize).trans (by scalar_tac)
  have dMax : P.d≤Usize.max := dSize.trans (by scalar_tac)
  have nEq : P.n=N.val := by simp [P,Shake.params,paramsS_n,hp.n_eq]
  have maxN : P.n≤32 := nEq ▸ hp.le32
  have fSize : P.forsSigBytes≤Usize.max := by
    unfold Spec.Params.forsSigBytes
    exact (Nat.mul_le_mul (Nat.mul_le_mul valid.k_le (Nat.add_le_add_left valid.a_le 1)) maxN).trans (by scalar_tac)
  obtain ⟨cap,_,_,cs⟩ := spec_imp_exists (sig_bytes_spec p hp.valid)
  have wSize : P.len*P.n ≤ Usize.max := by
    have up : cap.val≤Usize.max := by scalar_tac
    rw [cs] at up
    change P.n+P.forsSigBytes+P.d*P.xmssSigBytes≤Usize.max at up
    have l1 : P.len*P.n≤P.xmssSigBytes := Nat.mul_le_mul_right _ (Nat.le_add_right ..)
    have l2 : P.xmssSigBytes≤P.d*P.xmssSigBytes := by
      simpa using Nat.mul_le_mul_right P.xmssSigBytes (show 1≤P.d by have:=valid.d_ge; omega)
    omega
  have fVal : bytes forest.val=rows.flatten := by
    rw [show forest=boxed (raw rows.flatten) by rfl,unbox _ (by
      simp only [raw,List.length_map,rows,ParallelCached.fors_bytes,Spec.forsSign_length P valid];exact fSize),raw_bytes]
  have authEq : auth.val=(List.range (P.d*P.hp)).map (fun i => fixed N (au i)) := unbox _ (by simpa using countMax)
  have wotsEq : sigs.val=(List.range P.d).map (fun i => some (boxed (raw (wo i)))) := unbox _ (by simpa using dMax)
  have order := read_order found
  have fRead : (expand plan.forest).flatMap (fun i => rows[i]!)=rows.flatten := by
    rw [order.1,← ParallelCached.fors_length P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)]
    exact gather rows
  unfold interpreted
  change (ok (some (boxed (raw ((expand plan.forest).flatMap (fun i => rows[i]!)))),_,_)) ⦃ _ => _ ⦄
  rw [fRead,order.2.1,order.2.2]
  simp only [step_simps]
  change Joined N P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) tree.val leaf.val (some forest,some auth,sigs)
  refine ⟨forest,auth,rfl,rfl,fVal,?_,?_,?_,?_⟩
  · change _ ≤ auth.val.length
    simp [authEq]
  · change _ ≤ sigs.val.length
    simp [wotsEq]
  · intro j jl h hh
    have pos : j*P.hp+h<P.d*P.hp := by
      have upper := Nat.mul_le_mul_right P.hp (Nat.succ_le_of_lt jl)
      rw [Nat.succ_mul] at upper
      omega
    have layer : (j*P.hp+h)/P.hp=j := by rw [Nat.mul_comm j, Nat.mul_add_div valid.hp_pos,Nat.div_eq_of_lt hh,Nat.add_zero]
    have word := fixed_bytes N (au (j*P.hp+h)) ((Spec.xmssNode_length P valid ..).trans nEq)
    simpa [authRows,authEq,pos,au,authValue,layer,Nat.mod_eq_of_lt hh] using word
  · intro j jl
    refine ⟨boxed (raw (wo j)),?_,?_⟩
    · simp [wotsEq,jl]
    · have size : (raw (wo j)).length ≤ Usize.max := by
        simpa only [raw,List.length_map,wo,wotsValue,Spec.wotsSign_length P valid] using wSize
      rw [unbox (raw (wo j)) size,raw_bytes,fVal]
      rfl

end
end slhdsa.ParallelSignJoin
