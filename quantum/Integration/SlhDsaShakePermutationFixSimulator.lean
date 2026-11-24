import Integration.SlhDsaShakePermutationFixQuery

namespace Reduction.ShakePermutation.Fix
open PQ.Interactive Quantum
/-- Public table on short inputs (with arbitrary row selection and output
decoding), and an oracle-independent completion on longer inputs. -/
structure Access (X Y : Type) where
  addr : List Rate → X
  decode : List Rate → Y → Rate
  privateValue : List Rate → Rate

namespace Access
variable {X Y : Type} (A : Access X Y) (L : ℕ)
def value (H : X → Y) (s : List Rate) : Rate :=
  if s.length ≤ L then A.decode s (H (A.addr s)) else A.privateValue s

variable {T : ℕ}
abbrev Data (T : ℕ) := Domain T × Rate
def blocks (z : Data T) := List.ofFn z.1.2

def replace (z : Data T) (s : List Rate) (size : s.length = (blocks z).length) : Data T :=
  (BList.ofList s (by rw [size]; simp [blocks]; omega),z.2)

@[simp] theorem blocks_replace (z : Data T) (s : List Rate) (size) : blocks (replace z s size) = s := by simp [blocks,replace,BList.ofFn_ofList]
@[simp] theorem replace_blocks (z : Data T) : replace z (blocks z) rfl = z := by
  simp [replace,blocks,BList.ofList_ofFn]

def operate (f : List Rate → List Rate) (size : ∀ s, (f s).length = s.length)
    (inv : Function.Involutive f) : Equiv.Perm (Data T) :=
  Function.Involutive.toPerm (fun z => replace z (f (blocks z)) (size _)) (by
    intro z
    apply Prod.ext
    · simp [replace,blocks,BList.ofFn_ofList,inv _,BList.ofList_ofFn]
    · rfl)

def onPrefix (i : ℕ) (get : List Rate → Rate) (s : List Rate) := xorAt (get (s.take i)) i s
def atBlock (i : ℕ) (get : List Rate → Rate) : Equiv.Perm (Data T) :=
  operate (onPrefix i get) (by simp [onPrefix]) (by intro s; simp [onPrefix])

@[simp] theorem blocks_atBlock (i : ℕ) (get : List Rate → Rate) (z : Data T) :
    blocks (atBlock i get z) = onPrefix i get (blocks z) := by
  simp [atBlock,operate,Function.Involutive.toPerm]

variable [DecidableEq X] [AddCommGroup Y]
noncomputable def single (base : X) (i : ℕ) : Circuit X Y (Data T) :=
  if i = 0 then .localOp (Equiv.refl _)
  else if i ≤ L then
    Circuit.lookup base (fun z => A.addr ((blocks z).take i))
      (fun y => atBlock i (fun s => A.decode s y))
  else .localOp ((Equiv.refl (X × Y)).prodCongr (atBlock i A.privateValue))

theorem single_cost (base : X) (i : ℕ) :
    (A.single (T := T) L base i).cost = (if 0 < i ∧ i ≤ L then 2 else 0) := by
  by_cases z : i = 0
  · subst i; simp [single,Circuit.cost]
  · by_cases h : i ≤ L <;> simp [single,z,h,Nat.pos_of_ne_zero z,Circuit.cost]

def fixedData (f : List Rate → Rate) (i : ℕ) (z : Data T) := replace z (gate f i (blocks z)) (gate_length ..)

theorem single_clean (base : X) (H : X → Y) (i : ℕ) (z : Data T) :
    (A.single L base i).run H ((base,0),z) = ((base,0),fixedData (A.value L H) i z) := by
  by_cases zero : i = 0
  · subst i; simp [single,Circuit.run,fixedData,gate]
  by_cases short : i ≤ L
  · rw [single,ite_eq_right zero,ite_eq_left short,Circuit.lookup_clean]
    · simp [atBlock,operate,Function.Involutive.toPerm,fixedData,gate,zero,onPrefix,value,short]
    · intro y w
      simp [onPrefix]
  · rw [single,ite_eq_right zero,ite_eq_right short]
    by_cases past : (blocks z).length ≤ i
    · simp [Circuit.run,atBlock,operate,Function.Involutive.toPerm,fixedData,gate,zero,onPrefix,
        xorAt_past _ _ _ past]
    · have h : ¬ (blocks z).length ≤ L := by omega
      simp [Circuit.run,atBlock,operate,Function.Involutive.toPerm,fixedData,gate,zero,onPrefix,value,short,h]

noncomputable def sweeper (base : X) : ℕ → Circuit X Y (Data T)
  | 0 => .localOp (Equiv.refl _)
  | i+1 => .seq (sweeper base i) (A.single L base i)

theorem sweeper_cost (base : X) (i : ℕ) :
    (A.sweeper (T := T) L base i).cost = 2 * min (i-1) L := by
  induction i with
  | zero => simp [sweeper,Circuit.cost]
  | succ i ih =>
    simp only [sweeper,Circuit.cost,ih,single_cost]
    split <;> omega

theorem sweeper_clean (base : X) (H : X → Y) (i : ℕ) (z : Data T) :
    ∃ w : Data T, (A.sweeper L base i).run H ((base,0),z) = ((base,0),w) ∧
      blocks w = sweep (A.value L H) i (blocks z) ∧ w.2 = z.2 := by
  induction i with
  | zero => exact ⟨z,rfl,rfl,rfl⟩
  | succ i ih =>
    obtain ⟨w,hw,hs,hr⟩ := ih
    refine ⟨fixedData (A.value L H) i w,?_,?_,hr⟩
    · simp only [sweeper,Circuit.run,Equiv.trans_apply,hw,single_clean]
    · simp [fixedData,hs,sweep]

/-- A controlled output update with arbitrary reversible response encoding. -/
def respond (write : Rate → Equiv.Perm Rate) (f : List Rate → Rate) : Equiv.Perm (Data T) where
  toFun z := (z.1,write (f (blocks z)) z.2)
  invFun z := (z.1,(write (f (blocks z))).symm z.2)
  left_inv z := by simp [blocks]
  right_inv z := by simp [blocks]

noncomputable def readOut (base : X) (write : Rate → Equiv.Perm Rate) : Circuit X Y (Data T) :=
  Circuit.lookup base (fun z => A.addr (blocks z))
    (fun y => respond write (fun s => if s.length ≤ L then A.decode s y else A.privateValue s))

theorem readOut_clean (base : X) (write : Rate → Equiv.Perm Rate) (H : X → Y) (z : Data T) :
    (A.readOut L base write).run H ((base,0),z) =
      ((base,0),(z.1,write (A.value L H (blocks z)) z.2)) := by
  unfold readOut
  rw [Circuit.lookup_clean]
  · rfl
  · intros; rfl

noncomputable def simulate (base : X) (write : Rate → Equiv.Perm Rate) : Circuit X Y (Data T) :=
  let c := A.sweeper L base T
  .seq c (.seq (A.readOut L base write) c.reverse)

theorem simulate_cost (base : X) (write : Rate → Equiv.Perm Rate) :
    (A.simulate (T := T) L base write).cost ≤ 4 * L + 2 := by
  simp only [simulate,Circuit.cost,Circuit.reverse_cost,sweeper_cost,readOut,Circuit.lookup_cost]
  omega

private theorem sameBlocks (z w : Data T) (h : blocks z = blocks w) : z.1 = w.1 := by
  calc z.1 = BList.ofList (blocks z) (by simp [blocks]; omega) := (BList.ofList_ofFn z.1 _).symm
       _ = BList.ofList (blocks w) (by simp [blocks]; omega) := by congr
       _ = w.1 := BList.ofList_ofFn w.1 _

/-- The ancillas return to their clean values for every basis input, including
when the input path exceeds the public cap. -/
theorem simulate_clean (base : X) (write : Rate → Equiv.Perm Rate) (H : X → Y) (z : Data T) :
    (A.simulate L base write).run H ((base,0),z) =
      ((base,0),(z.1,write (transform (A.value L H) (blocks z)) z.2)) := by
  let result := write (transform (A.value L H) (blocks z)) z.2
  obtain ⟨w,hw,hs,hr⟩ := A.sweeper_clean L base H T z
  obtain ⟨w',hw',hs',hr'⟩ := A.sweeper_clean L base H T ((z.1,result) : Data T)
  have hb : blocks ((z.1,result) : Data T) = blocks z := rfl
  have hsize : (blocks z).length ≤ T := by simp [blocks]; omega
  rw [hb,← hs] at hs'
  rw [sweep_done _ _ _ hsize] at hs
  have how : (w.1,write (A.value L H (blocks w)) w.2) = w' := by
    apply Prod.ext
    · exact (sameBlocks w' w hs').symm
    · rw [hs,hr,hr']; rfl
  simp only [simulate,Circuit.run,Equiv.trans_apply,hw,readOut_clean,how,Circuit.run_reverse]
  exact ((A.sweeper L base T).run H).symm_apply_eq.mpr hw'.symm

open Classical in
/-- Matrix identity on the clean subspace, hence valid for entangled query
inputs and arbitrary superpositions. -/
theorem simulate_matrix [DecidableEq Y] (base : X) (write : Rate → Equiv.Perm Rate)
    (H : X → Y) (row : Register X Y (Data T)) (z : Data T) :
    basisMatrix ((A.simulate L base write).run H) row ((base,0),z) =
      if row = ((base,0),(z.1,write (transform (A.value L H) (blocks z)) z.2)) then 1 else 0 := by
  simp only [basisMatrix_apply,simulate_clean]

end Access
end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.Access.simulate_matrix
#print axioms Reduction.ShakePermutation.Fix.Access.simulate_cost
