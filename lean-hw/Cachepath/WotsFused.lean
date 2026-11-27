import Cachepath.WotsFusedPrefix
import Cachepath.WotsFusedOuter

open Aeneas Aeneas.Std Result slhdsa.ShakeBatch
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine]

private def grouped {N : Usize} (sk seed : Array U8 N) (addr : address.Adrs) (keys : Array U32 machine.width) := do
  let count ← N / 8#usize
  let offset ← count + 4#usize
  let pkA ← generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N) (keys,addr) address.WOTS_PK
  let size ← N + 32#usize
  let pk ← (do let base ← ShakeBatch.shake.batch.header seed pkA size
               let first ← Array.update base offset (Array.repeat machine.width 0#u64)
               Array.update first 16#usize (Array.repeat machine.width 0#u64))
  let prfA ← generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N) (keys,addr) address.WOTS_PRF
  let twice ← 2#usize * N
  let size1 ← twice + 32#usize
  let prf ← (do let raw ← ShakeBatch.shake.batch.header seed prfA size1
                ShakeBatch.shake.batch.put raw offset (Array.repeat machine.width sk))
  let hashA ← generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N) (keys,addr) address.WOTS_HASH
  let size2 ← twice + 32#usize
  let input ← ShakeBatch.shake.batch.header seed hashA size2
  let last ← twice + params.LEN2
  let (acc,pos) ← generate_loop0 count ⟨0#usize,last⟩ offset pk offset prf input
  let final ← (do let padded ← generate_loop1 ⟨0#usize,machine.width⟩ acc pos
                  machine.permute padded)
  ShakeBatch.shake.batch.read N final

theorem correct {N : Usize} (p : params.Params) (hp : PN p N) (permutes : PermutationCorrect) :
    @Vector.LeavesCorrect machine leaves N p := by
  intro sk seed a keys
  change generate sk seed a keys ⦃ out => _ ⦄
  apply ofProgramEq (g := grouped sk seed a keys)
  · simp only [grouped,generate,uncurry,bind_tc_eq,Std.bind_assoc,bind_ok]
    repeat' congr 1
  have small := hp.le32
  have align := aligned_hash hp
  unfold grouped
  step as ⟨count,c⟩
  step as ⟨offset,o⟩
  step with addresses_spec (N:=N) keys a address.WOTS_PK as ⟨pkA,pkEq⟩
  step as ⟨size,sizeEq⟩
  step with init_pk seed pkA size offset sizeEq (by omega) small align as ⟨pk,seeded⟩
  step with addresses_spec (N:=N) keys a address.WOTS_PRF as ⟨prfA,prfEq⟩
  step as ⟨twice,t⟩
  step as ⟨size1,sizeEq1⟩
  step with init_prf p hp seed sk prfA size1 offset (by omega) (by omega) as ⟨prf,prfGood⟩
  step with addresses_spec (N:=N) keys a address.WOTS_HASH as ⟨hashA,hashEq⟩
  step as ⟨size2,sizeEq2⟩
  step with init_input p hp seed hashA size2 (by omega) as ⟨input,inputGood⟩
  simp only [LEN2_eq]
  step as ⟨last,lastEq⟩
  step with all_chains p hp count offset last c (by omega) (by omega) seed sk prfA hashA pk prf input offset
    (by omega) prfGood inputGood permutes as ⟨result,rate,absorbed⟩
  rcases result with ⟨acc,pos⟩
  step with finish_rows acc pos rate permutes as ⟨final,padded⟩
  apply WP.spec_mono (read_digest N final (by omega) align)
  intro result bytesEq j hj
  have n : (Shake.params p).n = N.val := hp.n
  have len : (Shake.params p).len = last.val := by change (paramsS p).len = _; rw [hp.len];omega
  rw [bytesEq j hj,padded j hj,absorbed j hj,seeded j hj,← List.foldl_append,← len]
  let addr : Spec.Adrs := {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=keys.val[j]!.val}
  have pkAddr : adrsS pkA.val[j]! = Spec.wotsPkAdrs addr := by
    rw [pkEq j hj,WOTS_PK_eq]; rfl
  have hashAddr : adrsS hashA.val[j]! = addr := by
    rw [hashEq j hj]; with_unfolding_all rfl
  have prfAddr : adrsS prfA.val[j]! = Spec.wotsSkAdrs addr := by
    rw [prfEq j hj,WOTS_PRF_eq]; rfl
  have tips : tip p sk seed prfA.val[j]! hashA.val[j]! =
      pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) addr := by
    funext i
    unfold tip pkGenStep
    rw [hashAddr,prfAddr]
    rfl
  change Spec.shake256 _ N.val = Spec.shake256
    ((bytes seed.val ++ (Spec.wotsPkAdrs addr).bytes) ++
      (List.range (Shake.params p).len).flatMap (pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) addr)) (Shake.params p).n
  rw [pkAddr,tips,n]

end slhdsa.cache.builder.nativeShake.Vector.Fused
