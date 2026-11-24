import Integration.SlhDsaComposed
import Integration.SlhDsaAllGeneral
import MLink.ShakePrimitives

/-! SHAKE256 with its Keccak-f[1600] call exposed. A single 1600-bit
permutation supplies every absorption and squeezing round. The public query
register selects forward or inverse evaluation coherently. -/
namespace Reduction.ShakePermutation
open ENNReal Spec.Keccak SLHDSA MLink OracleSpec OracleComp PQ.Interactive PQ.QROM Quantum

abbrev Words := Fin 25 → UInt64
abbrev Permutation := Equiv.Perm Words
abbrev Port := Bool × Words

def oracle (π : Permutation) (x : Port) : Words :=
  if x.1 then π.symm x.2 else π x.2

@[simp] theorem oracle_forward_inverse (π : Permutation) (s : Words) :
    oracle π (false, oracle π (true, s)) = s := π.apply_symm_apply s

@[simp] theorem oracle_inverse_forward (π : Permutation) (s : Words) :
    oracle π (true, oracle π (false, s)) = s := π.symm_apply_apply s

def pack (a : State) : Words := fun i => UInt64.ofBitVec a[i.val]!
def unpack (a : Words) : State := Array.ofFn (fun i => (a i).toBitVec)

theorem pack_unpack (a : Words) : pack (unpack a) = a := by
  funext i
  simp [pack,unpack,getElem!_pos]

theorem unpack_pack (a : State) (h : a.size = 25) : unpack (pack a) = a := by
  apply Array.ext
  · simp [unpack,h]
  · intro i hi hj
    simp [unpack, pack, getElem!_pos, hj]

def feed (p : State → State) (s : State × Nat) (b : Spec.Byte) : State × Nat :=
  let a := xorByte s.1 s.2 b
  if s.2+1 = 136 then (p a,0) else (a,s.2+1)

def finish (p : State → State) (s : State × Nat) : State :=
  p (xorByte (xorByte s.1 s.2 0x1f) 135 0x80)

def squeeze (p : State → State) (s : State) (pos : Nat) : Nat → Spec.Bytes
  | 0 => []
  | n+1 =>
    let (s',pos') := if pos = 136 then (p s,0) else (s,pos)
    extractByte s' pos' :: squeeze p s' (pos'+1) n

@[simp] theorem squeeze_length (p : State → State) (s : State) (pos n : Nat) :
    (squeeze p s pos n).length = n := by
  induction n generalizing s pos <;> simp [squeeze, *]

def xof (p : State → State) (xs : Spec.Bytes) (n : Nat) : Spec.Bytes :=
  squeeze p (finish p (xs.foldl (feed p) initial)) 0 n

theorem squeeze_concrete (s : State) (pos n : Nat) :
    squeeze permute s pos n = Spec.Keccak.squeeze s pos n := by
  induction n generalizing s pos <;> simp [squeeze,Spec.Keccak.squeeze, *]

theorem xof_concrete (xs : Spec.Bytes) (n : Nat) : xof permute xs n = Spec.shake256 xs n :=
  squeeze_concrete _ _ _

/-- The exact formatted FIPS 205 requests with a caller-supplied 1600-bit round function. -/
def hash (p : State → State) (xs : Spec.Bytes) (n : Nat) : Bytes n :=
  ⟨(cv (xof p xs n)).toArray, by simp [cv,xof]⟩

@[reducible] def primitives (p : State → State) (s : Params) : Primitives s :=
  { PkSeed := Bytes s.n, SkSeed := Bytes s.n, SkPrf := Bytes s.n, Y := Bytes s.n,
    AdrsKey := Bytes 32, adrsToKey := Adrs.toVector, yToBytes := id,
    Thash := fun pk a ys => hash p (nd pk ++ nd a ++ nds ys) s.n
    PRF := fun pk sk a => hash p (nd pk ++ nd a.toVector ++ nd sk) s.n
    PRFmsg := fun sk rand msg => hash p (nd sk ++ nd rand ++ sp msg) s.n
    Hmsg := fun r pk root msg => hash p (nd r ++ nd pk ++ nd root ++ sp msg) s.m }

theorem hash_concrete (xs : Spec.Bytes) (n : Nat) : hash permute xs n = ShakeSecurity.hash xs n := by
  apply Vector.ext
  simp [hash, ShakeSecurity.hash,xof_concrete]

theorem primitives_concrete (s : Params) :
    primitives permute s = ShakeSecurity.primitives s := by
  have h : hash permute = ShakeSecurity.hash := funext fun xs => funext fun n => hash_concrete xs n
  unfold primitives
  rw [h]
  rfl

def lanes (f : Words → Words) (a : State) := unpack (f (pack a))

/-- The concrete 24-round Keccak computation on its fixed-width port. -/
def keccak (a : Words) : Words := pack (permute (unpack a))

private theorem permute_size (a : State) : (permute a).size = 25 := by
  have split : rc = rc.extract 0 23 ++ #[rc[23]!] := by decide
  unfold permute
  rw [split, Array.foldl_append]
  simp [Spec.Keccak.round]

theorem lanes_keccak (a : State) (ha : a.size = 25) : lanes keccak a = permute a := by
  simp only [lanes, keccak, unpack_pack a ha, unpack_pack _ (permute_size _)]

private theorem feed_keccak (a : State × Nat) (ha : a.1.size = 25) (b : Spec.Byte) :
    feed (lanes keccak) a b = feed permute a b ∧ (feed permute a b).1.size = 25 := by
  have hb : (xorByte a.1 a.2 b).size = 25 := by simp [xorByte,ha]
  by_cases hm : a.2+1 = 136 <;> simp [feed, hm, lanes_keccak _ hb, hb, permute_size]

private theorem absorb_keccak (xs : Spec.Bytes) (a : State × Nat) (ha : a.1.size = 25) :
    xs.foldl (feed (lanes keccak)) a = xs.foldl (feed permute) a ∧
    (xs.foldl (feed permute) a).1.size = 25 := by
  induction xs generalizing a with
  | nil => simpa only [List.foldl_nil] using And.intro (Eq.refl a) ha
  | cons b bs ih =>
    obtain ⟨he, hs⟩ := feed_keccak a ha b
    simpa only [List.foldl_cons, he] using ih (feed permute a b) hs

private theorem squeeze_keccak (a : State) (ha : a.size = 25) (pos n : Nat) :
    squeeze (lanes keccak) a pos n = squeeze permute a pos n := by
  induction n generalizing a pos with
  | zero => simp only [squeeze]
  | succ n ih =>
    by_cases hm : pos = 136 <;> simp [squeeze, hm, lanes_keccak a ha, ih a ha,
      ih (permute a) (permute_size _)]

theorem xof_keccak (xs : Spec.Bytes) (n : Nat) :
    xof (lanes keccak) xs n = Spec.shake256 xs n := by
  obtain ⟨he, hs⟩ := absorb_keccak xs initial (by simp [initial])
  rw [← xof_concrete]
  simp only [xof, he, finish]
  rw [lanes_keccak _ (by simp [xorByte,hs])]
  exact squeeze_keccak _ (permute_size _) _ _

def codec (p : State → State) (s : Params) : CoreWireCodec s (primitives p s).core where
  pkSeed := WireCodec.bytes s.n
  skSeed := WireCodec.bytes s.n
  skPrf := WireCodec.bytes s.n
  y := WireCodec.bytes s.n
  y_toBytes := fun _ => rfl

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)

noncomputable abbrev experiment (π : Permutation) :=
  F.at (oracle π) (pureBytesAlg S.vp (primitives (lanes π) S.vp.params)
    (codec (lanes π) S.vp.params) (fun pk => rand pk.pkSeed pk.pkRoot) seeds)

noncomputable def strongAdvantage : ℝ≥0∞ :=
  ∑ π : Permutation, ((Fintype.card Permutation : ℝ≥0∞)⁻¹ *
    qStrongUnforgeableAdvantage (experiment S rand seeds F π))

noncomputable def advantage : ℝ≥0∞ :=
  ∑ π : Permutation, ((Fintype.card Permutation : ℝ≥0∞)⁻¹ *
    qUnforgeableAdvantage (experiment S rand seeds F π))

theorem structural (S : Sha2Set) (p : State → State) : Structural S.vp (primitives p S.vp.params) :=
  ⟨⟨fun _ _ h => h⟩, Concrete.keyInjective_shakePrimitives _,
    (SLHDSA.Security.fipsApprovedAddressBounds S.fips).toCanonicalAddressBounds⟩

theorem signature_reduction :
    strongAdvantage S rand seeds F ≤ ∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ *
      qBetaSufMemoG (qPureBytesToInternal (experiment S rand seeds F π)) ∧
    advantage S rand seeds F ≤ ∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ *
      qBetaEufMemoG (qPureBytesToInternal (experiment S rand seeds F π)) := by
  constructor
  · exact Finset.sum_le_sum fun π _ => mul_le_mul' le_rfl
      (slhdsa_pure_bytes_suf_cma_final_quantum_all_general (structural S (lanes π)) _)
  · exact Finset.sum_le_sum fun π _ => mul_le_mul' le_rfl
      (slhdsa_pure_bytes_euf_cma_final_quantum_all_general (structural S (lanes π)) _)

end Reduction.ShakePermutation

#print axioms Reduction.ShakePermutation.xof_concrete
#print axioms Reduction.ShakePermutation.primitives_concrete

#print axioms Reduction.ShakePermutation.xof_keccak
#print axioms Reduction.ShakePermutation.signature_reduction
