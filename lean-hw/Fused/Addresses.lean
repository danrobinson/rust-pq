import Fused.Program
import Cachepath.NativeShakeWots.KeyUtils
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option maxHeartbeats 1000000

theorem lane_bits (idx : U32) :
    (idx &&& (7#u32)).val = idx.val % 8 ∧
    (idx &&& (~~~ (7#u32))).val = idx.val - idx.val % 8 := by
  have mask (x : BitVec 32) : x &&& (~~~ (7 : BitVec 32)) = (x >>> (3 : Nat)) <<< (3 : Nat) := by
    ext i hi
    interval_cases i <;> simp
  constructor
  · change (idx.val &&& (2^3-1)) = idx.val % 8
    rw [Nat.and_two_pow_sub_one_eq_mod]
  · change (idx.bv &&& (~~~ (7 : BitVec 32))).toNat = _
    rw [mask]
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have size : idx.val < 4294967296 := idx.hBounds
    change (idx.val / 8 * 8) % 4294967296 = idx.val - idx.val % 8
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

def laneAddress (a : address.Adrs) (typ : U32) (base l : Nat) : address.Adrs :=
  {a with typ, keypair := ⟨BitVec.ofNat 32 (base+l)⟩,word2 := 0#u32,word3 := 0#u32}

theorem address_front (a : address.Adrs) (typ : U32) (base l : Nat) :
    addressWord (laneAddress a typ base l) 0 = addressWord a 0 ∧
    addressWord (laneAddress a typ base l) 1 = addressWord a 1 := by exact ⟨rfl,rfl⟩

theorem address_tag (a : address.Adrs) (typ : U32) (base l : Nat) :
    addressWord (laneAddress a typ base l) 2 = addressLow typ ||| wordTag ⟨BitVec.ofNat 32 (base+l)⟩ := by
  exact packed_address a typ ⟨BitVec.ofNat 32 (base+l)⟩ 3 (by decide)

private def packTag (typ base : U32) (lane : Usize) : Result (U64 × U32) := do
  let i ← ShakeBatch.core.num.U32.swap_bytes typ
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (UScalar.cast .U32 lane)
  let i3 ← base + i2
  let i4 ← ShakeBatch.core.num.U32.swap_bytes i3
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i5 <<< 32#i32
  let i7 ← lift (i1 ||| i6)
  ok (i7, base)

private theorem lanes (a : address.Adrs) (base typ : U32) (capacity : base.val + 8 ≤ 2^32)
    (inst : core.ops.function.FnMut U32 Usize U64)
    (body : ∀ b l, inst.call_mut b l = packTag typ b l) :
    core.array.from_fn 8#usize inst base ⦃ words =>
      ∀ l < 8, words.val[l]!.bv = addressWord (laneAddress a typ base.val l) 2 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize inst base
    (fun l w => w.bv=addressWord (laneAddress a typ base.val l) 2) ?_)
  · intro words h j hj; simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  rw [body]
  unfold packTag
  simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
  have small : i.val < 8 := hi
  have cast : (UScalar.cast .U32 i).val=i.val := by scalar_tac
  step as ⟨x,xv⟩ <;> try scalar_tac
  step as ⟨top,_,bits⟩
  have xeq : x.val = base.val + i.val := xv.trans (congrArg (base.val + ·) cast)
  have tag : (⟨BitVec.ofNat 32 (base.val+i.val)⟩ : U32) = x := by
    rw [← xeq]
    cases x
    simp [UScalar.val,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [address_tag,tag]
  exact congrArg (fun z : BitVec 64 => addressLow typ ||| z) bits


theorem pk_lanes (N : Usize) (a : address.Adrs) (base : U32) (fits : base.val + 8 ≤ 2^32) :
    core.array.from_fn 8#usize (xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
      ⦃ w => ∀ l < 8, w.val[l]!.bv = addressWord (laneAddress a address.WOTS_PK base.val l) 2 ⦄ :=
  lanes a base _ fits _ (fun _ _ => rfl)

theorem prf_lanes (N : Usize) (a : address.Adrs) (base : U32) (fits : base.val + 8 ≤ 2^32) :
    core.array.from_fn 8#usize (xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
      ⦃ w => ∀ l < 8, w.val[l]!.bv = addressWord (laneAddress a address.WOTS_PRF base.val l) 2 ⦄ :=
  lanes a base _ fits _ (fun _ _ => rfl)

theorem hash_lanes (N : Usize) (a : address.Adrs) (base : U32) (fits : base.val + 8 ≤ 2^32) :
    core.array.from_fn 8#usize (xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
      ⦃ w => ∀ l < 8, w.val[l]!.bv = addressWord (laneAddress a address.WOTS_HASH base.val l) 2 ⦄ :=
  lanes a base _ fits _ (fun _ _ => rfl)

end slhdsa.Fused
