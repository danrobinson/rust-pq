import Slhdsa.Proofs.ShakeHash
import Slhdsa.Proofs.Wots

open Aeneas Aeneas.Std Result
namespace slhdsa.Shake
set_option maxHeartbeats 2000000

@[step] theorem chain_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (v seed : Array U8 N) (a : address.Adrs) (first last : U32) (order : first.val ≤ last.val) :
    shake.wots.chain v seed a first last ⦃ out => bytes out.val =
      Spec.chain (params p) (bytes v.val) first.val (last.val-first.val) (bytes seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  let f := fun j => Spec.chain (params p) (bytes v.val) first.val (j-first.val) (bytes seed.val) (adrsS adrs)
  unfold shake.wots.chain shake.wots.chain_loop
  apply loop.spec_decr_nat (measure := fun (s : Array U8 N × U32) => last.val - s.2.val)
    (inv := fun s => first.val ≤ s.2.val ∧ s.2.val ≤ last.val ∧ bytes s.1.val = f s.2.val)
  · rintro ⟨val,j⟩ ⟨lo,hi,acc⟩
    simp only at lo hi acc
    simp only [shake.wots.chain_loop.body, step_simps]
    spec_split
    · step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [j1_post]
      have succ : j.val+1-first.val = (j.val-first.val)+1 := by omega
      simp only [f, succ, chain_succ]
      have start : first.val + (j.val-first.val) = j.val := by omega
      change bytes val.val = Spec.chain (params p) (bytes v.val) first.val (j.val-first.val) (bytes seed.val) (adrsS adrs) at acc
      rw [start]
      rw [← acc]
      simpa only [Spec.F, params, paramsS_n, hp.n_eq, adrsS, a_post] using value1_post
    · simp only [step_simps]
      have eq : j.val = last.val := by scalar_tac
      simpa [f, eq] using acc
  · exact ⟨le_refl _, order, by simp [f, Spec.chain]⟩

@[step] theorem secret_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (i : Usize) (hi : i.val < 2^32) :
    shake.wots.secret sk seed a i ⦃ out => bytes out.val =
      Spec.PRF (params p) (bytes seed.val) (bytes sk.val) { Spec.wotsSkAdrs (adrsS a) with word2 := i.val } ⦄ := by
  unfold shake.wots.secret
  step*
  simp only [Spec.PRF, params, hp.n_eq, paramsS_n, Spec.wotsSkAdrs, *]
  congr 3
  simp [adrsS, Spec.Adrs.setTypeAndClear, _root_.slhdsa.address.WOTS_PRF, Spec.WOTS_PRF, *, UScalar.cast_val_eq, Nat.mod_eq_of_lt (show i.val < 4294967296 from hi)]

private def pkBlocks (p : _root_.slhdsa.params.Params) {N : Usize}
    (sk seed : Array U8 N) (adrs : address.Adrs) (count : Nat) :=
  (List.range count).flatMap (pkGenStep (params p) (bytes sk.val) (bytes seed.val) (adrsS adrs))

private theorem pk_loop_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (adrs : address.Adrs) (x : Spec.Bytes)
    (s : shake256.Sponge) (i : Usize) (hi : i.val ≤ 2*N.val+3)
    (hs : Absorbed s (x ++ pkBlocks p sk seed adrs i.val)) :
    shake.wots.wots_pk_gen_loop sk seed adrs.layer adrs.tree adrs.typ adrs.keypair
      adrs.word2 adrs.word3 s i ⦃ out => Absorbed out (x ++ pkBlocks p sk seed adrs (2*N.val+3)) ⦄ := by
  unfold shake.wots.wots_pk_gen_loop
  have hN := hp.le32
  apply loop.spec_decr_nat
    (measure := fun (r : shake256.Sponge × Usize) => 2*N.val+3 - r.2.val)
    (inv := fun r => r.2.val ≤ 2*N.val+3 ∧ Absorbed r.1 (x ++ pkBlocks p sk seed adrs r.2.val))
  · rintro ⟨s,k⟩ ⟨hk, inv⟩
    simp only at hk inv
    simp only [shake.wots.wots_pk_gen_loop.body, LEN2_eq]
    let* ⟨two, htwo⟩ ← Usize.mul_spec
    let* ⟨len, hlen⟩ ← Usize.add_spec
    spec_split
    · have small : k.val < 2^32 := by scalar_tac
      let* ⟨start, hstart⟩ ← secret_spec p hp sk seed adrs k small
      simp only [W_eq, lift, bind_ok]
      let* ⟨a1, a1_post⟩ ← with_word2_spec
      let* ⟨lastStep, lastPost⟩ ← U32.sub_spec
      let* ⟨endVal, hend⟩ ← chain_spec p hp start seed a1 0#u32 lastStep (by simp)
      let* ⟨s', hs'⟩ ← append_spec s _ inv
      let* ⟨k', hk'⟩ ← Usize.add_spec
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have digit : (UScalar.cast .U32 k).val = k.val := by
        simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt (show k.val < 4294967296 from small)]
      have last : lastStep.val = 15 := by scalar_tac
      rw [hk', pkBlocks, List.range_succ, List.flatMap_append]
      simpa only [pkBlocks, pkGenStep, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
        Array.val_to_slice, hend, hstart, a1_post, digit, last, adrsS,
        show (params p).w = 16 from w_eq p, Nat.reduceSub, Nat.sub_zero] using hs'
    · simp only [step_simps]
      have doneAt : k.val = 2*N.val+3 := by scalar_tac
      simpa [doneAt] using inv
  · exact ⟨hi, hs⟩

@[step] theorem wots_pk_gen_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (adrs : address.Adrs) :
    shake.wots.wots_pk_gen sk seed adrs ⦃ out =>
      bytes out.val = Spec.wotsPkGen (params p) (bytes sk.val) (bytes seed.val) (adrsS adrs) ⦄ := by
  unfold shake.wots.wots_pk_gen
  let* ⟨a, _, ha⟩ ← with_type_spec
  let* ⟨a1, ha1⟩ ← with_keypair_spec
  let* ⟨s, hs⟩ ← start_spec
  let domainBytes := bytes seed.val ++ (adrsS a1).bytes
  let* ⟨s', hs'⟩ ← pk_loop_spec p hp sk seed adrs domainBytes s 0#usize (by simp)
    (by simpa [domainBytes, pkBlocks] using hs)
  have hlen : (params p).len = 2*N.val+3 := hp.len
  have hn : (params p).n = N.val := hp.n
  have hpk := adrsS_pk adrs a a1 ha ha1
  have result := digest_spec N s' _ hs'
  change shake.hash.digest N s' ⦃ out => bytes out.val =
    Spec.shake256 ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS adrs)).bytes) ++
      pkBlocks p sk seed adrs (params p).len) (params p).n ⦄
  rw [hlen, hn, ← hpk]
  exact result

@[step] theorem wots_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (adrs : address.Adrs) :
    shake.wots.wots_sign m sk seed adrs ⦃ out => bytes out.val =
      Spec.wotsSign (params p) (bytes m.val) (bytes sk.val) (bytes seed.val) (adrsS adrs) ∧
      out.length = N.val * (2*N.val+3) ⦄ := by
  unfold shake.wots.wots_sign
  let* ⟨digits, hd, hl, _⟩ ← wots_digits_spec p hp m
  let blocks := fun k => (List.range k).flatMap
    (signStep (params p) (bytes sk.val) (bytes seed.val) (adrsS adrs) (nats digits.val))
  have hn := hp.le32
  unfold shake.wots.wots_sign_loop
  apply loop.spec_decr_nat (measure := fun (r : alloc.vec.Vec U8 × Usize) => digits.length-r.2.val)
    (inv := fun r => r.2.val ≤ digits.length ∧ r.1.length = N.val*r.2.val ∧ bytes r.1.val = blocks r.2.val)
  · rintro ⟨sig,i⟩ ⟨hi, hlen, hprefix⟩
    simp only at hi hlen hprefix
    simp only [shake.wots.wots_sign_loop.body]
    spec_split
    · have hlt : i.val < digits.length := by scalar_tac
      have small : i.val < 2^32 := by omega
      let* ⟨a, ha⟩ ← secret_spec p hp sk seed adrs i small
      simp only [lift, bind_ok]
      let* ⟨a1, ha1⟩ ← with_word2_spec
      let* ⟨d, hidx⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨v, hv⟩ ← chain_spec p hp a seed a1 0#u32 d (by simp)
      let* ⟨sig', hs⟩ ← extend_from_slice_u8_spec
      let* ⟨next, he⟩ ← Usize.add_spec
      have castEq : (UScalar.cast .U32 i).val = i.val := by
        simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt (show i.val < 4294967296 from small)]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [alloc.vec.Vec.length, hs, List.length_append, Array.val_to_slice, Array.length_eq, he,
          Nat.mul_succ]; exact congrArg (· + N.val) hlen
      · rw [he]
        simp only [blocks, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, hs, bytes_append, Array.val_to_slice, hprefix, signStep, hv, ha, ha1,
          adrsS, castEq, Nat.sub_zero]
        rw [nats_getElem! digits.val i.val hlt, hidx, getElem!_pos digits.val i.val (show i.val < digits.val.length from hlt)]
    · simp only [step_simps]
      have eq : i.val = digits.length := by scalar_tac
      have hpl : (params p).len = digits.length := hp.len.trans hl.symm
      change nats digits.val = Spec.wotsDigits (params p) (bytes m.val) at hd
      change bytes sig.val = (List.range (params p).len).flatMap (signStep (params p) _ _ _ (Spec.wotsDigits (params p) _)) ∧ _
      exact ⟨by simpa only [blocks, hpl, ← hd, eq] using hprefix,
        by simpa only [eq, hl] using hlen⟩
  · simp [blocks, alloc.vec.Vec.new, alloc.vec.Vec.length, bytes]

@[step] theorem wots_pk_from_sig_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (adrs : address.Adrs)
    (hsig : N.val * (2*N.val+3) ≤ sig.length) :
    shake.wots.wots_pk_from_sig sig m seed adrs ⦃ out => bytes out.val =
      Spec.wotsPkFromSig (params p) (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS adrs) ⦄ := by
  unfold shake.wots.wots_pk_from_sig
  let* ⟨digits, hd, hl, hds⟩ ← wots_digits_spec p hp m
  let* ⟨a, _, ha⟩ ← with_type_spec
  let* ⟨a1, ha1⟩ ← with_keypair_spec
  let* ⟨s, hs⟩ ← start_spec
  let x := bytes seed.val ++ (adrsS a1).bytes
  let f := fromSigStep (params p) (bytes sig.val) (bytes seed.val) (adrsS adrs) (nats digits.val)
  have hn := hp.le32
  have body : shake.wots.wots_pk_from_sig_loop sig seed adrs.layer adrs.tree adrs.typ adrs.keypair
      adrs.word2 adrs.word3 digits s 0#usize ⦃ out => Absorbed out (x ++ (List.range digits.length).flatMap f) ⦄ := by
    unfold shake.wots.wots_pk_from_sig_loop
    apply loop.spec_decr_nat (measure := fun (r : shake256.Sponge × Usize) => digits.length-r.2.val)
      (inv := fun r => r.2.val ≤ digits.length ∧ Absorbed r.1 (x ++ (List.range r.2.val).flatMap f))
    · rintro ⟨s,i⟩ ⟨hi, inv⟩
      simp only at hi inv
      simp only [shake.wots.wots_pk_from_sig_loop.body]
      spec_split
      · have hlt : i.val < digits.length := by scalar_tac
        have small : i.val < 2^32 := by omega
        have room : (i.val+1)*N.val ≤ sig.length := by
          rw [Nat.mul_comm] at hsig
          exact le_trans (Nat.mul_le_mul_right _ (by omega)) hsig
        let* ⟨start, hb⟩ ← block_spec N sig i room
        simp only [lift, bind_ok]
        let* ⟨addr, haddr⟩ ← with_word2_spec
        let* ⟨d, hidx⟩ ← alloc.vec.Vec.index_usize_spec
        simp only [W_eq]
        let* ⟨last, hend⟩ ← U32.sub_spec
        have he : last.val = 15 := by scalar_tac
        have hd15 : d.val ≤ last.val := by
          rw [he, hidx]
          have := hds _ (List.getElem_mem (l := digits.val) hlt)
          omega
        let* ⟨v, hv⟩ ← chain_spec p hp start seed addr d last hd15
        let* ⟨s', hs'⟩ ← append_spec s _ inv
        let* ⟨next, hnext⟩ ← Usize.add_spec
        have castEq : (UScalar.cast .U32 i).val = i.val := by
          simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt (show i.val < 4294967296 from small)]
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hnext, List.range_succ, List.flatMap_append]
        simpa only [x, f, fromSigStep, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
          Array.val_to_slice, hv, hb, haddr, adrsS, castEq, he, hidx, nats_getElem! digits.val i.val hlt,
          getElem!_pos digits.val i.val (show i.val < digits.val.length from hlt), show (params p).w = 16 from w_eq p, show (params p).n = N.val from hp.n,
          Spec.block, Nat.reduceSub, bytes_take, bytes_drop] using hs'
      · simp only [step_simps]
        have doneAt : i.val = digits.length := by scalar_tac
        simpa only [doneAt] using inv
    · exact ⟨by simp, by simpa [x] using hs⟩
  let* ⟨s', hs'⟩ ← body
  have hpk := adrsS_pk adrs a a1 ha ha1
  change nats digits.val = Spec.wotsDigits (params p) (bytes m.val) at hd
  change shake.hash.digest N s' ⦃ out => bytes out.val =
    Spec.shake256 ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS adrs)).bytes) ++
      (List.range (params p).len).flatMap (fromSigStep (params p) _ _ _ (Spec.wotsDigits (params p) _))) (params p).n ⦄
  rw [show (params p).len = digits.length from hp.len.trans hl.symm, show (params p).n = N.val from hp.n, ← hd, ← hpk]
  exact digest_spec N s' _ hs'

end slhdsa.Shake

#print axioms slhdsa.Shake.wots_pk_gen_spec
#print axioms slhdsa.Shake.wots_sign_spec
#print axioms slhdsa.Shake.wots_pk_from_sig_spec
