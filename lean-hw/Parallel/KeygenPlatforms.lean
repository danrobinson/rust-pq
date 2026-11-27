import Parallel.KeygenShake
import Parallel.KeygenSha2
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost.ShNode
open slhdsa.ShakeBatch
noncomputable section
variable [machine : Machine] [stream : Stream]

/-- The lane contract used by the compiled subtree symbolic executor. The
eight-lane fold evaluates PRF, the 15 chain hashes and sequential absorption of
each endpoint. Two/four-key groups select the corresponding live lane. -/
def grouped (p : params.Params) {N : Usize} (lanes : Nat) (sk seed : Array U8 N)
    (a : address.Adrs) (key : U32) : Result (Array U8 N) :=
  let lane := key.val % (min 8 (max 1 lanes))
  let start := key.val-lane
  let addrs := fun (x : Fin 8) => { (adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=start+x.val }
  pack (ParallelSubtree.leaves (Shake.params p) (bytes sk.val) (bytes seed.val) addrs ⟨lane%8,Nat.mod_lt _ (by decide)⟩)

private theorem grouped_correct {N : Usize} (p : params.Params) (hp : PN p N)
    (k : Nat) (sk seed : Array U8 N) (a : address.Adrs) (i : U32) :
    grouped p k sk seed a i ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p) (bytes sk.val) i.val 0 (bytes seed.val) (adrsS a) ⦄ := by
  let span := min 8 (max 1 k)
  have size : 0<span ∧ span≤8 := by dsimp [span]; omega
  have lane : i.val%span<8 := (Nat.mod_lt _ size.1).trans_le size.2
  have room : i.val % span ≤ i.val := Nat.mod_le _ _
  have len : (Shake.params p).len=2*(Shake.params p).n+3 := len_eq p hp.valid
  obtain ⟨ref,_,shape⟩ := spec_imp_exists (Shake.xmss_node_spec p hp sk i 0#u32 seed a (by scalar_tac))
  unfold grouped
  change pack (ParallelSubtree.leaves _ _ _ (fun x => { (adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=i.val-i.val%span+x.val })
    ⟨(i.val%span)%8,_⟩) ⦃ _ => _ ⦄
  rw [ParallelSubtree.leaves_eq _ _ _ _ len rfl]
  simp only [Nat.mod_eq_of_lt lane,Nat.sub_add_cancel room]
  change pack (Spec.xmssNode (Shake.params p) (bytes sk.val) i.val 0 (bytes seed.val) (adrsS a)) ⦃ _ => _ ⦄
  change bytes ref.val = Spec.xmssNode _ _ _ 0 _ _ at shape
  rw [←shape,pack_bytes]; simp

/-- A single projected lane of the native packed pair. The lane theorem applies
    with arbitrary addresses and child bytes in all other active lanes. -/
def packedPair {N : Usize} (seed : Array U8 N) (a : address.Adrs) (l r : Array U8 N) : Result (Array U8 N) := do
  let all ← ShakeBatch.shake.batch.pair seed (Array.repeat machine.width a)
    (Array.repeat machine.width l) (Array.repeat machine.width r)
  ok all.val[0]!

private theorem packedPair_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (positive : 0<machine.width.val) (permutes : PermutationCorrect) (seed : Array U8 N)
    (a : address.Adrs) (l r : Array U8 N) : packedPair seed a l r ⦃ out =>
    bytes out.val=Spec.H (Shake.params p) (bytes seed.val) (adrsS a) (bytes l.val++bytes r.val) ⦄ := by
  unfold packedPair
  step with pair_fips seed _ _ _ permutes hp.le32 (aligned_hash hp) as ⟨all,lanes⟩
  simpa only [Array.repeat_val,List.getElem!_replicate _ positive,Spec.H,Shake.params,paramsS_n,hp.n_eq,
    List.append_assoc] using lanes 0 positive

/-- The CPU executes the single-key program for width three. At width eight
the grouped leaf and per-lane pair contracts are the symbolic execution
boundary checked against the optimized Rust instructions. -/
def primitives (p : params.Params) (wide : Bool) : TreeOps where
  wide := wide
  leaf k sk seed a i := if wide then grouped p k sk seed a i else do
    let a ← address.Adrs.with_type a address.WOTS_HASH
    let a ← address.Adrs.with_keypair a i
    ShakeBatch.shake.batch.keygen sk seed a
  pair packed seed a l r := if packed then packedPair seed a l r else slhdsa.shake.xmss.hash2 seed a l r

theorem primitives_correct [StreamCorrect] {N : Usize} (p : params.Params) (hp : PN p N)
    (wide : Bool) (positive : 0<machine.width.val) (width : machine.width.val≤8) (perms : PermutationCorrect) :
    TreeOpsCorrect (primitives p wide) p N := by
  constructor
  · intro k sk seed a i
    cases wide
    · change (do let adr ← address.Adrs.with_type a address.WOTS_HASH
                 let adr ← address.Adrs.with_keypair adr i
                 ShakeBatch.shake.batch.keygen sk seed adr) ⦃ _ => _ ⦄
      simp only [address.Adrs.with_type,address.Adrs.with_keypair,bind_ok]
      apply WP.spec_mono (ShakeBatch.keygen_spec p hp sk seed _ positive width perms)
      intro v post
      simpa only [Spec.xmssNode,adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_HASH,address.WOTS_HASH,show (0#u32).val=0 from rfl] using post
    · exact grouped_correct p hp k sk seed a i
  · intro b seed a l r
    cases b
    · exact Shake.hash2_spec p hp seed a l r
    · exact packedPair_spec p hp positive perms seed a l r

def detector (probe : Result Bool) : Detector := ⟨ShakeBatch.shake.batch.available probe⟩

private theorem platform [StreamCorrect] {N : Usize} (p : params.Params) (hp : PN p N)
    (wide x86 : Bool) (probe : Result Bool) (flag : Bool) (value : probe=ok flag)
    (perms : flag=true → PermutationCorrect) (positive : 0<machine.width.val) (width : machine.width.val≤8)
    (threads : Nat) (pool : PoolOutcome) :
    KeyPair (@engine machine stream (primitives p wide) (detector probe)) x86 threads pool (N:=N) p := by
  apply @host_keys machine stream (primitives p wide) (detector probe) _ N p hp flag
    ((available_for_fips probe p hp).trans value) perms (fun _ => positive) (fun _ => width)
  exact fun on => primitives_correct p hp wide positive width (perms on)

end

noncomputable section
theorem linux_keys {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome) :
    KeyPair (@engine Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream
      (@primitives Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream p false)
      (detector KldispRust.shake256.parallel.available)) false threads pool (N:=N) p :=
  @platform Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect N p hp false false KldispRust.shake256.parallel.available true rfl
    (fun _ => Kldisp.permutation_correct) (by decide) (by decide) threads pool

theorem apple_keys (sha3 : Bool) {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome) :
    KeyPair (@engine (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream
      (@primitives (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream p true)
      (detector (ok true))) false threads pool (N:=N) p :=
  @platform (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream
    ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect N p hp true false (ok true) true rfl
    (fun _ => AppleHybrid.permutation_correct sha3) (by change 0<8; decide) (by change 8≤8; decide) threads pool

theorem x86_keys {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome) :
    KeyPair (@engine Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream
      (@primitives Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream p true)
      (detector KxdispatchRust.shake256.parallel.available)) true threads pool (N:=N) p :=
  @platform Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream
    ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect N p hp true true KxdispatchRust.shake256.parallel.available
    GatherRust.avx512Available rfl Kxdispatch.permutation_correct (by decide) (by decide) threads pool
end
end slhdsa.ParallelKeygenHost.ShNode
