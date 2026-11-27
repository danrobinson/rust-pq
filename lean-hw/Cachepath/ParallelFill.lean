import Cachepath.BuilderParallel
import Cachepath.Subtree
import Parallel.CacheCompletion

open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.workers.fill
open nativeShake

/-- The allocation and ticket geometry shared by both constructor workers. -/
def plan (n threads : Nat) : Option (Nat × Nat) :=
  if n < 16 then none else
  let workers := min threads (n/4)
  if workers < 2 then none else
  let chunk := max (n/(workers*4)) 4
  some (chunk,(n+chunk-1)/chunk)

theorem bounds {n t c k : Nat} (selected : plan n t = some (c,k)) :
    0<c ∧ k=(n+c-1)/c ∧ n≤k*c ∧ ∀ i<k, i*c<n := by
  unfold plan at selected
  split at selected <;> simp_all only [reduceCtorEq]
  split at selected <;> simp_all only [reduceCtorEq,Option.some.injEq,Prod.mk.injEq]
  obtain ⟨rfl,rfl⟩ := selected
  generalize hc : max _ 4 = c
  have pos : 0<c := by omega
  refine ⟨pos,rfl,?_,?_⟩
  · have := Nat.mod_lt (n+c-1) pos
    have := Nat.div_add_mod (n+c-1) c
    rw [Nat.mul_comm c] at this
    omega
  · intro i hi
    have h := (Nat.le_div_iff_mul_le pos).mp (show i+1 ≤ (n+c-1)/c by omega)
    rw [Nat.add_mul] at h
    simp at h
    omega

/-- The normal join has exactly the payload of each claimed ticket, for every
publication order, even when the payloads have equal values. -/
theorem slot {α : Type} {k : Nat} (payload : Nat → α) {cells}
    (run : ParallelCached.Run k (fun id => [(id,payload id)]) k [] cells)
    (id : Nat) (live : id < k) : cells id = some (payload id) := by
  apply (ParallelCached.joined run _ _).mpr
  exact ⟨id,live,by simp⟩

def assemble {N : Usize} (c : Nat) (job : Nat → Result (List (Array U8 N)))
    (out : Rows N) : Nat → Result (Rows N)
  | 0 => ok out
  | k+1 => do
    let prior ← assemble c job out k
    let batch ← job k
    ok (prior.setSlice! (k*c) batch)

/-- Any drained pool yields the same ordered copies as evaluating the per-ticket
payloads. A missing or duplicated completed batch cannot pass this statement. -/
theorem assemble_join {N : Usize} (c k : Nat) (job : Nat → Result (List (Array U8 N)))
    (payload : Nat → List (Array U8 N)) (out : Rows N) {cells}
    (finished : ParallelCached.Run k (fun id => [(id,payload id)]) k [] cells)
    (values : ∀ i<k, job i=ok (payload i)) :
    assemble c (fun i => match cells i with | some v => ok v | none => fail .panic) out k =
      assemble c job out k := by
  have same (i : Nat) (lt : i<k) := slot payload finished i lt
  have copies (z : Nat) (le : z≤k) :
      assemble c (fun i => match cells i with | some v => ok v | none => fail .panic) out z =
        assemble c job out z := by
    induction z with
    | zero => rfl
    | succ z ih =>
      simp only [assemble,ih (by omega),same z (by omega),values z (by omega)]
  exact copies k (by omega)

/-- A partial execution with one OnceLock per ticket always has a finite
continuation to a drained state. Runtime scheduling fairness is separate. -/
theorem can_join {α : Type} (k : Nat) (payload : Nat → α) {t pending cells}
    (run : ParallelCached.Run k (fun id => [(id,payload id)]) t pending cells) (issued : t≤k) :
    ∃ final, ParallelCached.Completion k (fun id => [(id,payload id)]) t pending cells final := by
  apply ParallelCached.can_join run _ issued
  simpa [List.map_flatMap,Function.comp_def] using List.nodup_range (n:=k)

theorem assemble_rows {N : Usize} (c k : Nat) (job : Nat → Result (List (Array U8 N)))
    (out : Rows N) (f : Nat → Spec.Bytes)
    (correct : ∀ id<k, job id ⦃ batch => batch.length=min (id*c+c) out.length - id*c ∧
      ∀ j<batch.length, bytes batch[j]!.val=f (id*c+j) ⦄) :
    assemble c job out k ⦃ rows => rows.length=out.length ∧
      ∀ j<min (k*c) out.length, bytes rows.val[j]!.val=f j ⦄ := by
  induction k with
  | zero => simp [assemble,WP.spec_ok]
  | succ k ih =>
    unfold assemble
    apply WP.spec_bind (ih (fun id lt => correct id (by omega)))
    intro r prior
    apply WP.spec_bind (correct k (by omega))
    intro batch bs
    rw [WP.spec_ok]
    refine ⟨by simp [prior.1],?_⟩
    intro j hj
    rw [Slice.setSlice!_val]
    by_cases before : j<k*c
    · rw [List.getElem!_setSlice!_prefix _ _ _ _ before]
      exact prior.2 j (by omega)
    · rw [Nat.succ_mul] at hj
      rw [List.getElem!_setSlice!_middle _ _ _ _ (by rw [bs.1]; change _ ∧ _ ∧ j<r.length; omega),
        bs.2 _ (by omega)]
      congr 1
      omega

/-- Sequential representative of the post-join slot reads. Workers compute
disjoint batches. A declined attempt returns the original destination. -/
def attempt {N : Usize} (threads n : Nat) (out : Rows N)
    (batch : Nat → Nat → Result (List (Array U8 N))) : Result (Bool × Rows N) := do
  match plan n threads with
  | none => ok (false,out)
  | some (c,k) =>
    let rows ← assemble c (fun id => batch (id*c) (min (id*c+c) n - id*c)) out k
    ok (true,rows)

theorem attempt_spec {N : Usize} (threads n : Nat) (out : Rows N) (size : out.length=n)
    (batch : Nat → Nat → Result (List (Array U8 N))) (f : Nat → Spec.Bytes)
    (good : ∀ start len, start+len≤n → batch start len ⦃ b =>
      b.length=len ∧ ∀ j<len, bytes b[j]!.val=f (start+j) ⦄) :
    attempt threads n out batch ⦃ r => r.2.length=out.length ∧
      (r.1=true → ∀ j<out.length, bytes r.2.val[j]!.val=f j) ⦄ := by
  unfold attempt
  cases hp : plan n threads with
  | none => simp [WP.spec_ok]
  | some pair =>
    obtain ⟨c,k⟩ := pair
    obtain ⟨_,_,cover,starts⟩ := bounds hp
    apply WP.spec_bind (assemble_rows c k _ out f ?_)
    · intro r h
      simp only [WP.spec_ok,true_implies]
      exact ⟨h.1,fun j hj => h.2 j (by omega)⟩
    · intro id hi
      have lt := starts id hi
      apply WP.spec_mono (good (id*c) (min (id*c+c) n-id*c) (by omega))
      intro b h
      exact ⟨by simpa [size] using h.1,fun j hj => h.2 j (h.1 ▸ hj)⟩

theorem shake_offset {N : Usize} [b : Backend] (s : Subtree.Single) (p : params.Params)
    (hp : PN p N) (detector : ∃ x, b.available N=ok x)
    (simd : b.available N=ok true → Subtree.Ops b s (N:=N) p)
    (sk pk : Array U8 N) (a : address.Adrs) (base : Usize) (rows : Rows N)
    (fits : base.val+rows.length≤512) :
    fill_leaves_chunk sk pk a base rows ⦃ out => Row out rows.length (fun j => Value p sk pk a 0 (base.val+j)) ⦄ := by
  obtain ⟨enabled,he⟩ := detector
  unfold fill_leaves_chunk
  cases enabled
  · simp only [he,bind_ok,Bool.false_eq_true,↓reduceIte,core.slice.Slice.iter_mut,
      XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_eq]
    obtain ⟨final,run,post⟩ := spec_imp_exists (fill_loop_offset p hp sk pk a base rows fits)
    change (do let e ← fill_leaves_chunk_loop ⟨⟨rows,0⟩,0#usize⟩ (fun x => x) sk pk a base; ok e.iter.slice) ⦃ _ => _ ⦄
    rw [run,bind_ok,WP.spec_ok]
    exact post
  · simpa only [he,bind_ok,↓reduceIte] using (simd he).leaves sk pk a base rows fits

end slhdsa.cache.builder.workers.fill
