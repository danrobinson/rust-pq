import Wots.Payload
import Digest256.Fips
import Gather512.Fips
import Slhdsa.Proofs.Wots
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
set_option maxRecDepth 8192

def leafAddress (a : WotsX86Rust.address.Adrs) (key : Nat) : Spec.Adrs :=
  {adrsS (WotsRust.addressOf (WotsX86Rust.asKernel a)) with typ:=0, keypair:=key, word2:=0, word3:=0}
def padAddress (a : WotsX86Rust.address.Adrs) : PadRust.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

private theorem key_eq {N} (p : params.Params) (hp : PN p N) (a : WotsX86Rust.address.Adrs)
    (k : Nat) (pk sk : Spec.Bytes) :
    Spec.T (paramsS p) pk (Spec.wotsPkAdrs (leafAddress a k))
      (keyPayload (paramsS p) (adrsS (WotsRust.addressOf (WotsX86Rust.asKernel a))) pk sk k (2*N.val+3)) =
      Spec.wotsPkGen (paramsS p) sk pk (leafAddress a k) := by
  unfold Spec.wotsPkGen
  rw [hp.len,w_eq]
  rfl

/-- Endpoint generation followed by the architecture-specific multi-key hash. -/
def keyBatch {N L : Usize} (seed : hash.Seed N) (sk : Array U8 N) (a : WotsX86Rust.address.Adrs)
    (first : U32) (messages : Rows L) (out : Rows N) := do
  let completed ← WotsX86Rust.sha256.x86.wots_endpoints seed.state sk a first messages
  if N=16#usize then DigestRust.sha256.x86.key_digests seed.state completed out
  else GatherRust.sha512.x86.key_digests seed.state512 completed out

theorem keyBatch_fips {N L} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : WotsX86Rust.address.Adrs) (first : U32) (messages : Rows L) (out : Rows N)
    (size block : Usize) (cpu : GatherRust.avx512Available=true)
    (shape : (N.val=16 ∧ L.val=640 ∧ block.val=64 ∧ messages.length ≤ 16) ∨
      (N.val=24 ∧ L.val=1280 ∧ block.val=128 ∧ messages.length ≤ 8) ∨
      (N.val=32 ∧ L.val=2304 ∧ block.val=128 ∧ messages.length ≤ 8))
    (nonempty : 0<messages.length) (lengths : out.length=messages.length)
    (sizeEq : size.val=22+(2*N.val+3)*N.val) (keys : first.val+messages.length≤2^32)
    (prepared : ∀ j<messages.length, ∃ k : U32, k.val=first.val+j ∧
      PadRust.xmss.wide.prepare_message (Array.repeat L 0#u8) (padAddress a) k size block = ok messages.val[j]!) :
    keyBatch seed sk a first messages out ⦃ final => final.length=out.length ∧ ∀ j<out.length,
      bytes final.val[j]!.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
        (leafAddress a (first.val+j)) ⦄ := by
  let P := paramsS p
  let pk := bytes seed.pk_seed.val
  let payload := fun j => keyPayload P (adrsS (WotsRust.addressOf (WotsX86Rust.asKernel a))) pk (bytes sk.val) (first.val+j) (2*N.val+3)
  let adr := fun j => Spec.wotsPkAdrs (leafAddress a (first.val+j))
  have payloadLen (j : Nat) : (payload j).length=(2*N.val+3)*N.val := by
    unfold payload keyPayload
    apply Spec.length_flatMap_const
    intro i
    rw [← hp.n]
    exact Spec.chain_length P hp.valid _ (Spec.PRF_length P hp.valid _ _ _) _ _ _ _
  have supported : Checked.supported N L := by rcases shape with h|h|h <;> simp_all [Checked.supported]
  have batch : messages.length≤16 := by rcases shape with h|h|h <;> omega
  have pubLen : pk.length=P.n := by simpa [pk,P] using hp.n.symm
  unfold keyBatch
  step with endpoint_payload P hp.valid seed.state sk a first messages pk cpu supported batch hp.n.symm pubLen
    (by rw [hp.n]; exact hs.1) keys as ⟨completed,count,inserted⟩
  have pads (j : Nat) (hj : j<completed.length) :
      bytes completed.val[j]!.val = if block.val=64 then padFrom 64 ((adr j).compress ++ payload j)
        else slhdsa.S512.padFrom 128 ((adr j).compress ++ payload j) := by
    have valid : j<messages.length := count ▸ hj
    obtain ⟨k,key,init⟩ := prepared j valid
    have pad := prepared_payload (padAddress a) k size block (payload j) _ (by
      rw [payloadLen]; rcases shape with ⟨n,l,b,_⟩|⟨n,l,b,_⟩|⟨n,l,b,_⟩ <;> simp [n,l,b])
      (by rw [payloadLen,sizeEq]) init
    rw [inserted j valid]
    have addressEq : adrsS (Keypadding.keyAddress (padAddress a) k) = adr j := by
      unfold adr Spec.wotsPkAdrs leafAddress Keypadding.keyAddress Keypadding.addressOf padAddress adrsS
      simp [Spec.Adrs.setTypeAndClear,Spec.WOTS_PK,key,WotsRust.addressOf,WotsX86Rust.asKernel]
    simpa only [addressEq] using pad
  rcases shape with ⟨n,l,b,cap⟩|other
  · have narrow : N=16#usize := UScalar.eq_of_val_eq n
    rw [if_pos narrow]
    step with Digest.tweakable_digest_spec P _ L seed.state completed out pk (fun j => adr j.val)
      (fun j => payload j.val) cpu n l (by rfl) hp.n pubLen (by omega) (by omega) (by omega)
      (by rw [hp.n,toByte_zero]; exact hs.1) (fun j bound => by simpa only [b,ite_true] using pads j.val bound)
      as ⟨final,len,values⟩
    refine ⟨len,fun j hj => ?_⟩
    exact (values ⟨j,by omega⟩ (show j<completed.length by omega)).trans (key_eq p hp a _ _ _)
  · have wide : N ≠ 16#usize := by rcases other with h|h <;> scalar_tac
    simp only [wide,ite_false]
    have format : (N.val=24 ∧ L.val=1280) ∨ (N.val=32 ∧ L.val=2304) := by rcases other with h|h <;> simp_all
    have cap : completed.length≤8 := by rcases other with h|h <;> omega
    have b : block.val=128 := by rcases other with h|h <;> omega
    step with S512.Gather.tweakable_digest_spec P _ L seed.state512 completed out pk (fun j => adr j.val)
      (fun j => payload j.val) cpu format (by rfl) hp.n pubLen (by omega) cap (by omega)
      (by rw [hp.n,toByte_zero]; exact hs.2 (fun h => wide (UScalar.eq_of_val_eq h)))
      (fun j bound => by simpa [b] using pads j.val bound) as ⟨final,len,values⟩
    refine ⟨len,fun j hj => ?_⟩
    exact (values ⟨j,by omega⟩ (show j<completed.length by omega)).trans (key_eq p hp a _ _ _)
end slhdsa.X86.Wots
