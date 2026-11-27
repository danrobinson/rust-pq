"""Instantiate each shader/command theorem for the raw-message internal API.

Only the input adapter, exported result, and root composition lemma change.
All source-projected producers and physical buffers are shared.
"""


def claims(stages, label, p):
    text = "\n".join(stages).replace(label+"_", label+"_raw_")
    result = f"rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd)"
    return (text.replace(result, f"rs.map (fun r => Spec.slhSignInternal {p} r.msg r.sk r.addrnd)")
            .replace("rs.any (fun r => decide (r.ctx.length > 255)) = false", "True")
            .replace("MetalCommandValues.public_pooled_batch", "MetalInternalSign.pooled")
            .replace("MetalCommandValues.publicResult", "MetalInternalSign.returned")
            .replace("MetalCommandValues.framed", "id").replace("[requests,id]", "[requests]"))


def outcome(label, p, limit):
    return f"""
private theorem {label}_internal_success (rs : List MetalPipeline.BatchSignReq) (overrideLimit : Option Nat)
    (initial : MetalChainDispatch.Memory) (memory : Nat → Spec.Byte) (exit : MetalCompletion.Exit) (out : List Spec.Bytes) :
    let two := rs.length*{p}.d*2^{p}.hp < overrideLimit.getD {limit}
    let pool := fun () => if two then {label}_1_raw_pool rs initial memory else {label}_0_raw_pool rs initial memory
    MetalInternalSign.api {p} rs exit pool = .ok out →
      out = rs.map (fun r => Spec.slhSignInternal {p} r.msg r.sk r.addrnd) := by
  intro two pool ok
  apply (MetalInternalSign.success {p} rs exit pool out ok).trans
  by_cases h : two
  · simpa only [pool,ite_eq_left h,{label}_1_raw_pool] using {label}_1_raw_canonical_fips rs initial memory
  · simpa only [pool,ite_eq_right h,{label}_0_raw_pool] using {label}_0_raw_canonical_fips rs initial memory

private theorem {label}_wrappers (overrideLimit : Option Nat) (initial : MetalChainDispatch.Memory)
    (memory : Nat → Spec.Byte) (exit : MetalCompletion.Exit) :
    let raw := fun rs : List MetalPipeline.BatchSignReq =>
      let two := rs.length*{p}.d*2^{p}.hp < overrideLimit.getD {limit}
      MetalInternalSign.api {p} rs exit (fun () => if two then {label}_1_raw_pool rs initial memory else {label}_0_raw_pool rs initial memory)
    let outer := fun rs : List MetalPipeline.BatchSignReq =>
      let two := rs.length*{p}.d*2^{p}.hp < overrideLimit.getD {limit}
      MetalCompletion.sign {p} rs exit (fun () => if two then {label}_1_pool rs initial memory else {label}_0_pool rs initial memory)
    MetalPublicSignatures.Correct {p} raw outer := by
  intro raw outer
  exact MetalPublicSignatures.wrappers {p} raw outer
    (fun rs out => {label}_internal_success rs overrideLimit initial memory exit out)
    (fun rs out => {label}_sign_success rs overrideLimit initial memory exit out)
"""


def session(label, p, limit, family, n):
    """Feed the actual completed key/readback and raw signer to the Apple CPU verifier."""
    profile = p.removeprefix("Spec.")
    return f"""
open Aeneas Aeneas.Std in
private theorem {label}_cpu_roundtrip [slhdsa.Armwide.Public.Dispatcher.Cpu] [slhdsa.Armwide.Keygen.Features]
    (sha3 : Bool) (overrideLimit : Option Nat)
    (keyMemory sigMemory : MetalChainDispatch.Memory) (memory : Nat → Spec.Byte)
    (sk prf pub rnd : Spec.Bytes) (ss : sk.length={p}.n) (ps : prf.length={p}.n) (ks : pub.length={p}.n)
    (m ctx : Aeneas.Std.Slice Aeneas.Std.U8) (context : ctx.length≤255)
    (room : slhdsa.Room m.length (slhdsa.msgSlack {n}+257)) :
    let batch : MetalKeygenDispatch.Batch := [(sk,prf,pub)]
    let keyRead := fun () => if batch.length*2^{p}.hp < overrideLimit.getD {limit} then
      {label}_1_kg_batch batch keyMemory else {label}_0_kg_batch batch keyMemory
    let raw := fun rs : List MetalPipeline.BatchSignReq =>
      let read := fun () => if rs.length*{p}.d*2^{p}.hp < overrideLimit.getD {limit} then
        {label}_1_raw_pool rs sigMemory memory else {label}_0_raw_pool rs sigMemory memory
      MetalInternalSign.api {p} rs (.submitted true) read
    MetalVerifiedRoundTrip.Session {p}
      (MetalVerifiedRoundTrip.cpu .{family} sha3 {n}#usize slhdsa.sets.{profile}.params.PARAMS)
      (MetalCompletion.keygen batch (.submitted true) keyRead) raw sk prf pub rnd m ctx := by
  intro batch keyRead raw
  apply MetalVerifiedRoundTrip.roundTrip .{family} sha3 _ slhdsa.{profile}.pn {p} slhdsa.{profile}.hP
    (MetalPipeline.metal_all_12_params_valid _ (by decide)) (Nat.le_trans (m:=50000) (by decide) (by scalar_tac)) (by decide)
    sk prf pub rnd ss ps ks m ctx context room
  · obtain ⟨out,returned⟩ : ∃ out, MetalCompletion.keygen batch (.submitted true) keyRead=.ok out := ⟨_,rfl⟩
    rw [returned,{label}_keygen_success batch overrideLimit keyMemory (.submitted true) out returned]
    rfl
  · intro msg secret r
    let req : MetalPipeline.BatchSignReq := ⟨msg,[],secret,r⟩
    obtain ⟨out,returned⟩ : ∃ out, raw [req]=.ok out := ⟨_,rfl⟩
    have values := {label}_internal_success [req] overrideLimit sigMemory memory (.submitted true) out returned
    unfold MetalPublicSignatures.rawSingle
    change (raw [req]).map List.getLast! = _
    rw [returned,values]
    rfl
"""
