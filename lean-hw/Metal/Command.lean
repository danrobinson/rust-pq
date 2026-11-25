import Std

namespace MetalCommand

/-- Regions of pooled buffers. Signature pieces denote disjoint byte ranges
within each tree/layer, even though they share the output allocation. -/
inductive Region where
  | keys | xmss_trees | wots_layers | fors_jobs | chain_tips | xmss_leaves
  | xmss_roots | fors_sub_roots | fors_roots | pk_fors
  | randomizer | forsLow | forsHigh | xmssAuth | wots
  deriving DecidableEq, Repr

structure Access where
  epoch : Nat
  reads : List Region
  writes : List Region
  deriving DecidableEq, Repr

/-- For every access, each read has an earlier producer. No two accesses may
write the same logical output, including those issued in the same GPU epoch.
An initial host write and a final host read are ordinary entries. -/
def safe (trace : List Access) : Bool :=
  trace.all fun a =>
    (a.reads.all fun r => trace.any fun b => b.epoch < a.epoch && b.writes.contains r) &&
    (a.writes.all fun r => (trace.filter fun b => b.writes.contains r).length == 1)

theorem produced {trace : List Access} (ok : safe trace = true) {a : Access}
    (ha : a ∈ trace) {r : Region} (hr : r ∈ a.reads) :
    ∃ b ∈ trace, b.epoch < a.epoch ∧ r ∈ b.writes := by
  have h := (List.all_eq_true.mp ok) a ha
  simp only [Bool.and_eq_true] at h
  simpa using List.any_eq_true.mp ((List.all_eq_true.mp h.1) r hr)

theorem unique_writer {trace : List Access} (ok : safe trace = true) {a : Access}
    (ha : a ∈ trace) {r : Region} (hr : r ∈ a.writes) :
    (trace.filter fun b => b.writes.contains r).length = 1 := by
  have h := (List.all_eq_true.mp ok) a ha
  simp only [Bool.and_eq_true] at h
  simpa using (List.all_eq_true.mp h.2) r hr

private theorem one_mem {xs : List α} (h : xs.length = 1) (ha : a ∈ xs) (hb : b ∈ xs) : a = b := by
  cases xs with
  | nil => simp at ha
  | cons c tail =>
    have : tail = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst tail
    exact (List.eq_of_mem_singleton ha).trans (List.eq_of_mem_singleton hb).symm

/-- A concurrent reader cannot observe an unfinished writer. The unique
producer belongs to a strictly preceding encoder epoch, even for shared
resources read by several kernels. -/
theorem ordered {trace : List Access} (ok : safe trace = true) {a b : Access}
    (ha : a ∈ trace) (hb : b ∈ trace) {r : Region} (read : r ∈ a.reads)
    (write : r ∈ b.writes) : b.epoch < a.epoch := by
  obtain ⟨c, hc, lt, wc⟩ := produced ok ha read
  have eq : b = c := one_mem (unique_writer ok hb write)
    (by simp [hb, write]) (by simp [hc, wc])
  exact eq ▸ lt

/-- Splitting signature nodes into the randomizer, FORS trees, XMSS layers
and then FORS passes or WOTS/authentication is repeated fixed-stride
partitioning and splitting adjacent intervals. -/
theorem separate_items {i j stride x y : Nat} (ij : i < j) (hx : x < stride) :
    i * stride + x < j * stride + y := by
  have h := Nat.mul_le_mul_right stride ij
  rw [Nat.succ_mul] at h
  omega

theorem separate_parts {base x left y : Nat} (hx : x < left) :
    base + x < base + left + y := by omega

/-- Resource actions executed at an exceptional return. A pending command is
submitted and drained by its destructor, even when only a prefix was encoded.
A failed command publishes no CPU-readable result. Pool cleanup still wipes. -/
inductive Phase where | noCommand | encoding | succeeded | failed
  deriving DecidableEq, Repr
inductive Exit where
  | setupError
  | encodingUnwind (issued : Nat) (completed : Bool)
  | commandFailure (issued : Nat)
  | success (issued resultReads : Nat)
  deriving DecidableEq, Repr

inductive Action where
  | beginCmd | dispatch | waitOk | waitFailed | cpuRead | wipe | unlock
  deriving DecidableEq, Repr

def actions : Exit → List Action
  | .setupError => [.wipe, .unlock]
  | .encodingUnwind n success => [.beginCmd] ++ List.replicate n .dispatch ++
      [if success then .waitOk else .waitFailed, .wipe, .unlock]
  | .commandFailure n =>
      [.beginCmd] ++ List.replicate n .dispatch ++ [.waitFailed, .wipe, .unlock]
  | .success n reads =>
      [.beginCmd] ++ List.replicate n .dispatch ++ (.waitOk :: List.replicate reads .cpuRead ++ [.wipe, .unlock])

/-- A failing or unwinding command may have modified only part of its outputs.
Only successful completion permits a CPU result read. Both terminal statuses
permit wiping the secret pool buffer. Unlock follows wiping. -/
def accepts : Phase → List Action → Bool
  | .noCommand, .beginCmd :: rest => accepts .encoding rest
  | .encoding, .dispatch :: rest => accepts .encoding rest
  | .encoding, .waitOk :: rest => accepts .succeeded rest
  | .encoding, .waitFailed :: rest => accepts .failed rest
  | .succeeded, .cpuRead :: rest => accepts .succeeded rest
  | p, [.wipe, .unlock] => p != .encoding
  | _, _ => false

private theorem encoded (n : Nat) (endings : List Action) :
    accepts .encoding (List.replicate n .dispatch ++ endings) = accepts .encoding endings := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, accepts] using ih

private theorem result_reads (n : Nat) :
    accepts .succeeded (List.replicate n .cpuRead ++ [.wipe, .unlock]) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, accepts] using ih

theorem exit_safe (e : Exit) : accepts .noCommand (actions e) = true := by
  cases e with
  | setupError => rfl
  | encodingUnwind n completed =>
    change accepts .encoding (List.replicate n .dispatch ++ _) = true
    rw [encoded]
    cases completed <;> rfl
  | commandFailure n =>
    change accepts .encoding (List.replicate n .dispatch ++ _) = true
    rw [encoded]
    rfl
  | success n reads =>
    change accepts .encoding (List.replicate n .dispatch ++ _) = true
    rw [encoded]
    exact result_reads reads

end MetalCommand
