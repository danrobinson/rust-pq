import Armwide.HashRoutes
import Armwide.SignBlocks

namespace slhdsa.Armwide.Transitions
open Spec.SHA256

structure WotsRegisters where
  address : Nat → Spec.Adrs
  chain : Nat → Nat
  counter : Nat → Nat
  digest : Nat → Arm.V × Arm.V

private def addressed (r : WotsRegisters) (op : HashCall) : Spec.Adrs :=
  { r.address op.head with word2 := r.chain op.chain, word3 := r.counter op.counter+op.increment }

private def execute (n : Nat) (st : List Word) (r : WotsRegisters) (op : HashCall) (v : Arm.V × Arm.V) :=
  hashRegisters n st (r.address op.head) (r.chain op.chain)
    (r.counter op.counter+op.increment) v.1 v.2

def runRegisterHashes (n : Nat) (st : List Word) (r : WotsRegisters) (mode : Mode) (j : Fin (lanes mode)) :=
  let trace := hashRoute mode j
  trace.calls.foldl (fun v op => execute n st r op v) (r.digest trace.origin)

def content (n : Nat) (v : Arm.V × Arm.V) := Kernel.storeN n v.1 v.2

private theorem run_ops (p : Spec.Params) [Fact (p.family = .sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (hpk : pk.length = p.n) (r : WotsRegisters) (ops : List HashCall)
    (small : ∀ op ∈ ops, r.chain op.chain < 65536) (v : Arm.V × Arm.V) :
    content p.n (ops.foldl (fun v op => execute p.n (seedState p.n pk) r op v) v) =
      ops.foldl (fun x op => Spec.F p pk (addressed r op) x) (content p.n v) := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons,ih (fun i hi => small i (by simp [hi]))]
    congr 1
    rw [F_eq]
    have eq := native_tweakable_hash p.n valid.n_cases pk hpk (r.address op.head)
      (r.chain op.chain) (r.counter op.counter+op.increment) (small op (by simp)) v.1 v.2
    simpa only [content, execute, addressed, stored_eq p.n valid.n_cases] using eq

/-- For one, two, three, and four distinct-head lanes, the native digest equals FIPS F.
WOTS PRF uses the same SHA-256 operation at its separate PRF address. -/
theorem native_mixed (p : Spec.Params) [Fact (p.family = .sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (hpk : pk.length = p.n) (r : WotsRegisters) (count : Fin 4)
    (j : Fin (lanes (.mixed count))) (small : r.chain j < 65536) :
    content p.n (runRegisterHashes p.n (seedState p.n pk) r (.mixed count) j) =
      Spec.F p pk { r.address j with word2 := r.chain j, word3 := r.counter j } (content p.n (r.digest j)) := by
  unfold runRegisterHashes
  rw [routed]
  apply run_ops p valid pk hpk r [⟨j,j,j,0⟩]
  intro op h
  obtain rfl := List.mem_singleton.mp h
  exact small

theorem native_mixed_prf (p : Spec.Params) [Fact (p.family = .sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (hpk : pk.length = p.n) (r : WotsRegisters) (count : Fin 4)
    (j : Fin (lanes (.mixed count))) (small : r.chain j < 65536) :
    content p.n (runRegisterHashes p.n (seedState p.n pk) r (.mixed count) j) =
      Spec.PRF p pk (content p.n (r.digest j))
        { r.address j with word2 := r.chain j, word3 := r.counter j } := by
  rw [native_mixed p valid pk hpk r count j small,F_eq,PRF_eq]

/-- The shared-head fast branch on four live chains advances the selected lane from
its actual counter by the requested 1–15 hash steps, using the same FIPS address at each step. -/
theorem native_shared_chain (p : Spec.Params) [Fact (p.family = .sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (hpk : pk.length = p.n) (r : WotsRegisters) (steps : Fin 15)
    (j : Fin (lanes (.shared steps))) (small : r.chain j < 65536) :
    content p.n (runRegisterHashes p.n (seedState p.n pk) r (.shared steps) j) =
      Spec.chain p (content p.n (r.digest j)) (r.counter j) (steps.val+1) pk
        { r.address 4 with word2 := r.chain j } := by
  unfold runRegisterHashes
  rw [routed]
  simp only [expected]
  rw [run_ops p valid pk hpk r _ (by
    intro op h
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
    exact small)]
  rw [List.foldl_map]
  rfl

/-- Reconstituting a digest from its n stored bytes between iterations preserves
the next output for any original register pair, including unused high words. -/
theorem equal_visible_digest (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (plen : pk.length=p.n) (r : WotsRegisters)
    (replacement : Nat → Arm.V × Arm.V) (mode : Mode) (j : Fin (lanes mode))
    (same : content p.n (replacement j) = content p.n (r.digest j)) (small : r.chain j < 65536) :
    content p.n (runRegisterHashes p.n (seedState p.n pk) {r with digest := replacement} mode j) =
      content p.n (runRegisterHashes p.n (seedState p.n pk) r mode j) := by
  cases mode with
  | mixed count =>
    rw [native_mixed p valid pk plen {r with digest := replacement} count j small,native_mixed p valid pk plen r count j small]
    simp only [same]
  | shared steps =>
    rw [native_shared_chain p valid pk plen {r with digest := replacement} steps j small,native_shared_chain p valid pk plen r steps j small]
    simp only [same]

end slhdsa.Armwide.Transitions
