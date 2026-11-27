import Cachepath.NativeVerify.ActiveHashRows
import Cachepath.NativeVerify.ActiveHashHeader
import Cachepath.NativeVerify.ForsSignNode
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine]
theorem short_fips (permute : Active machine) {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (values : Array (Array U8 N) machine.width) (active : Usize) (width : active.val≤machine.width.val) (permutes : ActiveCorrect machine permute)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) :
    short_active permute seed addresses values active ⦃ out => ∀ j < active.val,
      bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addresses.val[j]!).bytes ++ bytes values.val[j]!.val)) N.val ⦄ := by
  unfold short_active
  step as ⟨a,twice⟩
  step as ⟨size,sz⟩
  step with header_spec seed addresses size active width bound (by omega) as ⟨st,header⟩
  step as ⟨n,nn⟩
  step as ⟨offset,off⟩
  step with put_spec st offset values active width (by omega) as ⟨st1,put⟩
  step with permutes st1 active width as ⟨st2,permuted⟩
  step with read_digest N st2 active width (by omega) aligned as ⟨out,read⟩
  rename_i j hj
  rw [read j hj,permuted j hj,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun a => Spec.Keccak.squeeze (Spec.Keccak.permute a) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [ShakeBatch.lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,put k hk j hj,header k hk j hj,off,nn,sz,twice]
  exact short_layout seed _ _ bound aligned k

theorem pair_fips (permute : Active machine) {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (left right : Array (Array U8 N) machine.width) (active : Usize) (width : active.val≤machine.width.val) (permutes : ActiveCorrect machine permute)
    (bound : N.val ≤ 32) (aligned : N.val%8=0) :
    pair_active permute seed addresses left right active ⦃ out => ∀ j < active.val,
      bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addresses.val[j]!).bytes ++
        (bytes left.val[j]!.val ++ bytes right.val[j]!.val))) N.val ⦄ := by
  unfold pair_active
  step as ⟨a,three⟩
  step as ⟨size,sz⟩
  step with header_spec seed addresses size active width bound (by omega) as ⟨st,header⟩
  step as ⟨n,nn⟩
  step as ⟨offset,off⟩
  step with put_spec st offset left active width (by omega) as ⟨st1,put1⟩
  step as ⟨twice,tw⟩
  step as ⟨n2,nn2⟩
  step as ⟨offset2,off2⟩
  step with put_spec st1 offset2 right active width (by omega) as ⟨st2,put2⟩
  step with permutes st2 active width as ⟨st3,permuted⟩
  step with read_digest N st3 active width (by omega) aligned as ⟨out,read⟩
  rename_i j hj
  rw [read j hj,permuted j hj,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun a => Spec.Keccak.squeeze (Spec.Keccak.permute a) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [ShakeBatch.lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,put2 k hk j hj,
    put1 k hk j hj,header k hk j hj,off,nn,sz,three,off2,nn2,tw]
  exact pair_layout seed _ _ _ bound aligned k


theorem short_correct (permute : Active machine) (valid : ActiveCorrect machine permute) :
    ForsSign.ShortLaw (short_active permute) := by
  intro N p hp seed addrs values active width
  exact short_fips permute seed addrs values active width valid hp.le32 (aligned_hash hp)

theorem pair_correct (permute : Active machine) (valid : ActiveCorrect machine permute) :
    ForsSign.PairLaw (pair_active permute) := by
  intro N p hp seed addrs left right active width
  exact pair_fips permute seed addrs left right active width valid hp.le32 (aligned_hash hp)

/-- The width-three signer now shares the native active permutation between the
    secret hash and both children of every recursive parent. -/
def linuxWithLeaf (leaf : @ForsSign.Leaf Kldisp.machine) (correct : @ForsSign.LeafLaw Kldisp.machine leaf) :
    WidthThree.ForsSigner :=
  let permute := fullActive Kldisp.machine KldispRust.shake256.parallel.available
  @ForsSign.linux (@short_active Kldisp.machine permute)
    (@ForsSign.descend Kldisp.machine leaf (@pair_active Kldisp.machine permute))
    (@short_correct Kldisp.machine permute NativeVerify.linux)
    (@ForsSign.descend_correct Kldisp.machine leaf (@pair_active Kldisp.machine permute) correct
      (@pair_correct Kldisp.machine permute NativeVerify.linux))

end slhdsa.NativeVerify.ActiveHash
