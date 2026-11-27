import Parallel.PhaseTwoRoots
import Parallel.SignJoinInterpreter

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket
open ParallelFused ParallelSignJoin ParallelSigning

/-- A normal counter execution, including its final out-of-range fetch. -/
structure Schedule (n : Nat) where
  issued : Nat
  completed : List Nat
  trace : Trace n issued [] completed
  drained : n < issued

private theorem chronological (n i : Nat) (le : i≤n) :
    Trace n i [] (List.range i).reverse := by
  induction i with
  | zero => exact .start
  | succ i ih => simpa [List.range_succ] using
      (Trace.publish (Trace.claim (ih (by omega)) (by omega)) (List.Perm.refl [i]))

def inOrder (n : Nat) : Schedule n :=
  ⟨n+1,(List.range n).reverse,.stop (chronological n n (by omega)) (by omega),by omega⟩

def leafValue (p : Spec.Params) (sk pk : Spec.Bytes) (tree leaf i : Nat) :=
  let pos := loc p.hp tree leaf i
  Spec.xmssNode p sk pos.2 0 pk (addr i pos.1)

/-- The three physical inputs observed immediately before the root walk. -/
noncomputable def observedInputs (plan : PhysicalRows) (schedule : ∀ d, Schedule d) : ForestWorker :=
  fun {N} p md sk seed a _ tree leaf _ => do
    let P := Shake.params p
    let rows := ParallelCached.forsRows P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
    let forest := boxed (raw ((expand plan.forest).flatMap (fun i => rows[i]!)))
    let auth := boxed ((expand plan.auth).map (fun i =>
      fixed N (authValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val i)))
    let count := core.num.Usize.saturating_sub (UScalar.cast .Usize p.d) 1#usize
    let leaves := boxed ((List.range count.val).map (fun i => some (fixed N
      (leafValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val i))))
    ok ⟨forest,auth,leaves,count,(schedule p.d.val).issued,(schedule p.d.val).completed⟩

theorem observed_law (schedule : ∀ d, Schedule d) {N : Usize} (p : params.Params) (hp : PN p N)
    (plan : PhysicalRows) (found : lookup (Shake.params p)=some plan) :
    ForestLaw (observedInputs plan schedule) N p := by
  intro md sk seed a r tree leaf threads enabled size bounded leafBound address
  have joined := interpreted_ready p hp plan found md sk seed a r tree leaf threads enabled size bounded leafBound address
  simp only [interpreted,step_simps] at joined
  obtain ⟨forest,auth,fg,ag,ready⟩ := joined
  simp only [Option.some.injEq] at fg ag
  subst forest auth
  simp only [observedInputs,step_simps]
  let P := Shake.params p
  let count := core.num.Usize.saturating_sub (UScalar.cast .Usize p.d) 1#usize
  have d := hp.valid.d_ge
  change 2≤p.d.val at d
  have number : count.val+1=p.d.val := by
    have cast : (UScalar.cast .Usize p.d).val=p.d.val := by scalar_tac
    change (0 ⊔ ((UScalar.cast .Usize p.d).val-1)) % 2^UScalarTy.Usize.numBits + 1 = _
    rw [Nat.max_eq_right (Nat.zero_le _),Nat.mod_eq_of_lt (by
      have bound := (UScalar.cast .Usize p.d).bv.isLt
      change (UScalar.cast .Usize p.d).val < 2^UScalarTy.Usize.numBits at bound
      omega),cast];omega
  refine ⟨ready.forestRows,⟨ready.authSize,ready.authRow⟩,?_,number,(schedule _).trace,(schedule _).drained⟩
  let values := (List.range count.val).map (fun i => some (fixed N (leafValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val i)))
  have full : (boxed values).val=values := by
    have fits : values.length≤Usize.max := by simpa only [values,List.length_map,List.length_range] using (show count.val≤Usize.max by scalar_tac)
    simp [boxed,List.take_of_length_le fits]
  refine ⟨by change count.val≤(boxed values).val.length;rw [full];simp [values],?_⟩
  intro j hj
  let v := leafValue P (bytes sk.val) (bytes seed.val) tree.val leaf.val j
  refine ⟨fixed N v,?_,?_⟩
  · change (boxed values).val[j]! = (some (fixed N v))
    change j<count.val at hj
    rw [full]
    simp [values,hj,v]
  · have len : v.length=N.val := (Spec.xmssNode_length P (Suite.valid .shake hp) ..).trans hp.n
    change bytes (fixed N v).val=v
    simp [fixed,len,raw,bytes,Function.comp_def]

end slhdsa.WidthEight.Ticket
