import Armwide.WotsRegisterHash
import Armwide.SignLoad
import Armwide.TailNative
import Armwide.InitProgram
import Spec.Correctness

namespace slhdsa.Armwide.Transitions
open WotsRefill Spec.SHA256
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

private instance : Inhabited SignLane := ⟨⟨[],0,0,0,false⟩⟩

private def inputs (n : Nat) (base : Spec.Adrs) (active : List SignLane) : WotsRegisters where
  address := fun j => if j=4 then base else if active[j]!.isPrf then Spec.wotsSkAdrs base else base
  chain := fun j => active[j]!.chain
  counter := fun j => active[j]!.curT
  digest := fun j => loadDigest n active[j]!.x

def outputDigest (n : Nat) (r : Arm.V × Arm.V) := storedBytes n r.1 r.2

def steps (n : Nat) (st : List Word) (base : Spec.Adrs) (active : List SignLane) (m : Mode) : List Stepping :=
  List.ofFn fun j : Fin (lanes m) => ⟨⟨j.val%4,Nat.mod_lt _ (by decide)⟩,active[j.val]!,
    outputDigest n (runRegisterHashes n st (inputs n base active) m j)⟩

def chooseMixed (n : Nat) : Mode := .mixed ⟨(n-1)%4,Nat.mod_lt _ (by decide)⟩
def chooseShared (bulk : Nat) : Mode := .shared ⟨(bulk-1)%15,Nat.mod_lt _ (by decide)⟩

def fourWith {α : Type} (write : Writer α) (n : Nat) (st : List Word) (sk : Spec.Bytes) (base : Spec.Adrs) (digits : Nat → Nat) : List SignLane → List Nat → α → List SignLane × List Nat × α :=
  fun active queue out =>
    if active.any (·.isPrf) then
      compactWithWriter write sk digits false 1 (steps n st base active (.mixed 3)) queue out
    else
      let k := signMinLeft active
      compactWithWriter write sk digits true k (steps n st base active (chooseShared k)) queue out

abbrev four := fourWith setOut

def tailWith {α : Type} (write : Writer α) (n : Nat) (st : List Word) (base : Spec.Adrs) : List SignLane → α → List SignLane × α :=
  fun active out =>
    tailWithWriter write ⟨(active.length-1)%4,Nat.mod_lt _ (by decide)⟩
      (steps n st base active (chooseMixed active.length)) out

abbrev tail := tailWith setOut

private theorem len_x (p : Spec.Params) (valid : p.Valid) (pk sk : Spec.Bytes)
    (slen : sk.length=p.n) (base : Spec.Adrs) (digits : Nat → Nat) (len : Nat)
    (a : List SignLane) (q : List Nat) (out : Nat → Spec.Bytes) (inv : SignInv p pk sk base digits len a q out)
    (j : Nat) (hj : j<a.length) : a[j]!.x.length = p.n := by
  have v := inv.lanes_valid a[j]! (by rw [getElem!_pos a j hj]; exact List.getElem_mem ..)
  cases phase : a[j]!.isPrf with
  | true => rw [(v.2.2.1 phase).2.2,slen]
  | false =>
    rw [(v.2.2.2 phase).2]
    exact Spec.chain_length p valid _ (Spec.PRF_length p valid ..) _ _ _ _

private theorem mixed_eq (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (pkl : pk.length=p.n) (skl : sk.length=p.n) (base : Spec.Adrs) (digits : Nat → Nat) (len : Nat)
    (a : List SignLane) (q : List Nat) (o : Nat → Spec.Bytes) (inv : SignInv p pk sk base digits len a q o)
    (cap : len ≤ 67) (cnt : Fin 4) (size : lanes (.mixed cnt)=a.length) :
    (steps p.n (seedState p.n pk) base a (.mixed cnt)).map (progressed false 1) = a.map (signStepOneLane p pk base) := by
  apply List.ext_getElem (by simp [steps,size])
  intro i hi hj
  have ha : i<a.length := by simpa using hj
  have h := inv.lanes_valid a[i]! (by rw [getElem!_pos a i ha]; exact List.getElem_mem ..)
  have im : i<lanes (.mixed cnt) := by omega
  have i4 : i≠4 := by have := cnt.isLt; change i<cnt.val+1 at im; omega
  let r := inputs p.n base a
  have hm := native_mixed p valid pk pkl r cnt ⟨i,im⟩ (by change a[i]!.chain < 65536; omega)
  have init : content p.n (r.digest i) = a[i]!.x := load_content p.n valid.n_cases _ (len_x p valid pk sk skl base digits len a q o inv i ha)
  change content p.n _ = Spec.F p pk
    {r.address i with word2 := r.chain i, word3 := r.counter i} (content p.n (r.digest i)) at hm
  rw [init] at hm
  simp only [steps,outputDigest,stored_eq p.n valid.n_cases,List.getElem_map,List.getElem_ofFn,progressed,Bool.false_eq_true,↓reduceIte]
  rw [← getElem!_pos a i ha]
  change _ = signStepOneLane p pk base a[i]!
  unfold signStepOneLane
  rcases phase : a[i]!.isPrf with _|_
  · have addr : r.address i = base := by change (if i=4 then _ else if _ then _ else _)=_; simp only [i4,phase,↓reduceIte,Bool.false_eq_true]
    rw [addr] at hm
    simp only [Bool.false_eq_true,↓reduceIte]
    exact congrArg (fun digest => SignLane.mk digest a[i]!.chain (a[i]!.curT+1) (a[i]!.left-1) false) hm
  · have zero := (h.2.2.1 phase).1
    have addr : r.address i = Spec.wotsSkAdrs base := by change (if i=4 then _ else if _ then _ else _)=_; simp only [i4,phase,↓reduceIte]
    rw [addr] at hm
    change content p.n _ = Spec.F p pk {Spec.wotsSkAdrs base with word2 := a[i]!.chain, word3 := a[i]!.curT} _ at hm
    rw [zero,F_eq] at hm
    simp only [↓reduceIte,PRF_eq]
    exact congrArg (fun digest => SignLane.mk digest a[i]!.chain a[i]!.curT (a[i]!.left-1) false) hm

private theorem shared_eq (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (pkl : pk.length=p.n) (skl : sk.length=p.n) (base : Spec.Adrs) (digits : Nat → Nat) (len : Nat)
    (a : List SignLane) (q : List Nat) (o : Nat → Spec.Bytes) (inv : SignInv p pk sk base digits len a q o)
    (cap : len ≤ 67) (size : a.length=4) (phase : a.any (·.isPrf) = false)
    (hdig : ∀ c < len, digits c ≤ 15) :
    (steps p.n (seedState p.n pk) base a (chooseShared (signMinLeft a))).map (progressed true (signMinLeft a)) =
      a.map (fun l => ⟨Spec.chain p l.x l.curT (signMinLeft a) pk {base with word2 := l.chain},
        l.chain,l.curT+signMinLeft a,l.left-signMinLeft a,false⟩) := by
  let k := signMinLeft a
  have pos : 0 < k := signMinLeft_pos (by intro e; simp [e] at size) (fun l h => (inv.lanes_valid l h).2.1)
  have onlyHash : ∀ l ∈ a, l.isPrf=false := by simpa using List.any_eq_false.mp phase
  apply List.ext_getElem (by simp [steps,chooseShared,lanes,size])
  intro i hi hj
  have ha : i<a.length := by simpa using hj
  have mem : a[i]! ∈ a := by rw [getElem!_pos a i ha]; exact List.getElem_mem ..
  have v := inv.lanes_valid _ mem
  have ph := onlyHash _ mem
  have km := signMinLeft_le mem
  have dl := hdig _ v.1
  have cl := (v.2.2.2 ph).1
  have bound : k ≤ 15 := by dsimp [k]; omega
  have modEq : (k-1)%15+1 = k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  let r := inputs p.n base a
  have im : i<4 := by omega
  have hm := native_shared_chain p valid pk pkl r ⟨(k-1)%15,Nat.mod_lt _ (by decide)⟩ ⟨i,im⟩
    (by change a[i]!.chain < 65536; omega)
  have init : content p.n (r.digest i) = a[i]!.x := load_content p.n valid.n_cases _ (len_x p valid pk sk skl base digits len a q o inv i ha)
  simp only [modEq] at hm
  rw [init] at hm
  simp only [steps,outputDigest,stored_eq p.n valid.n_cases,List.getElem_map,List.getElem_ofFn,progressed,↓reduceIte]
  rw [← getElem!_pos a i ha]
  simp only [ph]
  exact congrArg (fun digest => SignLane.mk digest a[i]!.chain (a[i]!.curT+k) (a[i]!.left-k) false) hm

theorem initial_rows_eq (sk : Spec.Bytes) (digits : Nat → Nat) (order : List Nat) :
    initialRows sk digits order =
      ((order.take 4).map (fun c => (⟨sk,c,0,1+digits c,true⟩ : SignLane)),order.drop 4) := by
  dsimp only [initialRows]
  apply Prod.ext
  · apply List.ext_getElem (by simp)
    intro i h h'
    have hi : i < order.length := by simp at h; omega
    simp only [List.getElem_map,List.getElem_range,List.getElem_take,getElem!_pos order i hi]
  · by_cases four : 4 ≤ order.length
    · rw [Nat.min_eq_left four]
    · rw [Nat.min_eq_right (by omega),List.drop_length,List.drop_eq_nil_of_le (by omega)]

def initializedRun (sk : Spec.Bytes) (digits : Nat → Nat) (order : List Nat)
    (full : FourStep) (drain : TailStep) :=
  let (active,queue) := initialRows sk digits order
  signRunUsing full drain active queue (fun _ => []) (signMeasure active queue+1)

theorem initialized_eq (sk : Spec.Bytes) (digits : Nat → Nat) (order : List Nat)
    (full : FourStep) (drain : TailStep) :
    initializedRun sk digits order full drain = signFusedUsing sk digits order full drain := by
  unfold initializedRun
  rw [initial_rows_eq]
  rfl

/-- For all admissible WOTS lengths and digits, the register-hashing, retire/refill
and compacting scheduler returns the FIPS signature element of every chain. -/
theorem native_sign_scheduler (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (pkl : pk.length=p.n) (skl : sk.length=p.n) (base : Spec.Adrs) (digits : Nat → Nat) (len : Nat)
    (cap : len ≤ 67) (order : List Nat) (hdig : ∀ c < len, digits c ≤ 15) (hn : order.Nodup)
    (hm : ∀ c, c ∈ order ↔ c<len) :
    ∀ c < len, signFusedUsing sk digits order (four p.n (seedState p.n pk) sk base digits)
      (tail p.n (seedState p.n pk) base) c = wotsSignTarget p pk sk base digits c := by
  apply sign_using_scheduler_eq_fips p pk sk base digits len order _ _ _ _ hdig hn hm
  · intro a q o inv size
    unfold four fourWith signStep4
    split <;> rename_i phase
    · rw [compact_four_eq _ _ _ _ _ _ _ (by simp [steps,lanes]),native_updates_eq,mixed_eq p valid pk sk pkl skl base digits len a q o inv cap 3 (by exact size.symm)]
    · rw [compact_four_eq _ _ _ _ _ _ _ (by simp [steps,chooseShared,lanes]),native_updates_eq,shared_eq p valid pk sk pkl skl base digits len a q o inv cap size (by simpa using phase) hdig]
  · intro a o inv pos small
    unfold tail tailWith signStepTail chooseMixed
    have widthEq : width ⟨(a.length-1)%4,Nat.mod_lt _ (by decide)⟩ = a.length := by
      change (a.length-1)%4+1=a.length
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [tail_updates_eq _ (by rwa [widthEq]) _ (by simp [steps,width,lanes]) o,mixed_eq p valid pk sk pkl skl base digits len a [] o inv cap ⟨(a.length-1)%4,Nat.mod_lt _ (by decide)⟩ (by
      change (a.length-1)%4+1=a.length
      rw [Nat.mod_eq_of_lt (by omega)]; omega)]

end slhdsa.Armwide.Transitions
