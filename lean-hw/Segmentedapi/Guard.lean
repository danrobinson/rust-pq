import Segmentedapi.Public
import Segmented.Digest
open Aeneas Aeneas.Std Result
namespace slhdsa.SegmentedApi
set_option maxRecDepth 8192

private theorem room_context {N : Usize} (msg ctx : Slice U8) (hc : ctx.length≤255)
    (room : Room msg.length (msgSlack N.val+257)) :
    Room (2+ctx.length+msg.length) (msgSlack N.val) := by
  obtain ⟨a,b⟩ := room
  constructor <;> omega

theorem digest_eq {N : Usize} (p : params.Params) (hp : PN p N) (m ctx mp : Slice U8)
    (hc : ctx.length≤255) (hm : Room (2+ctx.length+m.length) (msgSlack N.val))
    (ml : mp.length=2+ctx.length+m.length) (mb : bytes mp.val=Spec.withContext (bytes m.val) (bytes ctx.val))
    (r ps root : Array U8 N) :
    SegmentedApiRust.slh.message.digest p r ps root ctx m = hash.h_msg p r ps root mp := by
  obtain ⟨x,hx,fx,_⟩ := spec_imp_exists (Segmented.digest_spec p hp.valid hp.n_eq r ps root ctx m hc hm)
  obtain ⟨y,hy,fy,_⟩ := spec_imp_exists (h_msg_spec p hp.valid hp.n_eq r ps root mp (ml ▸ hm))
  rw [hx,hy]
  congr 1
  apply alloc.vec.Vec.ext
  exact (bytes_inj _ _).mp (fx.trans (mb ▸ fy).symm)

theorem verify_eq {N : Usize} (p : params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (room : Room m.length (msgSlack N.val+257)) :
    Program.slh.slh_verify N p m sig ctx pk=slh.slh_verify N p m sig ctx pk := by
  by_cases bad : ctx.len>255#usize
  · simp [Program.slh.slh_verify,slh.slh_verify,bad]
  · have hc : ctx.length≤255 := by scalar_tac
    obtain ⟨mp,ok,encoded,len⟩ := spec_imp_exists (with_context_spec m ctx hc ((Nat.add_le_add_left (Nat.le_add_left 257 (msgSlack N.val)) _).trans room.1))
    have same := message_verify_eq p m ctx (alloc.vec.Vec.deref mp) sig pk
      (digest_eq p hp m ctx _ hc (room_context m ctx hc room)
        (by simpa [vec_deref_length] using len) (by simpa [vec_deref_val] using encoded))
    simp [Program.slh.slh_verify,slh.slh_verify,bad,ok,bind_ok,same]

theorem sign_eq_from_prf {N : Usize} (p : params.Params) (hp : PN p N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (room : Room m.length (msgSlack N.val+257))
    (randomizer : ∀ (key : Array U8 N), ctx.length≤255 →
      SegmentedApiRust.slh.message.randomizer key rnd ctx m ⦃ out => bytes out.val =
        Spec.PRFmsg (paramsS p) (bytes key.val) (bytes rnd.val) (Spec.withContext (bytes m.val) (bytes ctx.val)) ⦄) :
    Program.slh.slh_sign p m ctx sk rnd=slh.slh_sign p m ctx sk rnd := by
  by_cases bad : ctx.len>255#usize
  · simp [Program.slh.slh_sign,slh.slh_sign,bad]
  · have hc : ctx.length≤255 := by scalar_tac
    obtain ⟨mp,ok,encoded,len⟩ := spec_imp_exists (with_context_spec m ctx hc ((Nat.add_le_add_left (Nat.le_add_left 257 (msgSlack N.val)) _).trans room.1))
    let buf := alloc.vec.Vec.deref mp
    have size : buf.length=2+ctx.length+m.length := by simpa [buf,vec_deref_length] using len
    have content : bytes buf.val=Spec.withContext (bytes m.val) (bytes ctx.val) := by simpa [buf,vec_deref_val] using encoded
    have space := room_context m ctx hc room
    have rndEq (key : Array U8 N) : SegmentedApiRust.slh.message.randomizer key rnd ctx m = hash.prf_msg key rnd buf := by
      obtain ⟨a,ha,fa⟩ := spec_imp_exists (randomizer key hc)
      obtain ⟨b,hb,fb⟩ := spec_imp_exists (prf_msg_spec (paramsS p) hp.n hp.nok key rnd buf (size ▸ space))
      rw [ha,hb]
      congr 1
      exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (fa.trans (content ▸ fb).symm))
    have same := message_sign_eq p m ctx buf sk rnd rndEq (digest_eq p hp m ctx buf hc space size content)
    dsimp only [buf] at same
    simp only [Program.slh.slh_sign,slh.slh_sign,if_neg bad,ok,bind_ok,same,ite_self]

theorem verify_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length=2*N.val) (hm : Room m.length (msgSlack N.val+257)) :
    Program.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b=Spec.slhVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  rw [verify_eq p hp m sig ctx pk hm]
  exact slh_verify_spec p hp m sig ctx pk hpk hm

end slhdsa.SegmentedApi
