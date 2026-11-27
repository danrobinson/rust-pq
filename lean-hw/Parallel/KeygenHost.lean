import Parallel.KeygenProgram
import X86platform.Hypertree

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section

def NodeCorrect {S} (e : Engine S) {N : Usize} (P : Spec.Params) (okSeed : S N → Prop) :=
  ∀ (sk : Array U8 N) (i z : U32) (s : S N) (a : address.Adrs), okSeed s →
    (i.val+1)*2^z.val ≤ 2^P.hp → e.node sk i z s a ⦃ out =>
    bytes out.val=Spec.xmssNode P (bytes sk.val) i.val z.val (e.seedBytes s) (adrsS a) ⦄

theorem pack_bytes {N} (r : Array U8 N) : pack (bytes r.val)=ok r := by
  have iden : (bytes r.val).map (fun x => (⟨x⟩ : U8)) = r.val := by
    simp [bytes,Function.comp_def]
  simp [pack]
  exact Aeneas.Std.Array.ext _ _ (by rw [Array.from_val]; exact iden)

private theorem word_val {n : Nat} (small : n<2^32) : (word n).val=n := by
  change (BitVec.ofNat 32 n).toNat=n
  simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

theorem worker_value {S} (e : Engine S) {N : Usize} (P : Spec.Params) (okSeed : S N → Prop)
    (height : P.hp≤9) (correct : NodeCorrect e P okSeed) (x86 : Bool) (threads : Nat) (pool : PoolOutcome)
    (sk : Array U8 N) (s : S N) (hs : okSeed s) (a : address.Adrs) (ref : Array U8 N)
    (value : bytes ref.val=Spec.xmssNode P (bytes sk.val) 0 P.hp (e.seedBytes s) (adrsS a)) :
    worker e P x86 threads pool sk s a = ok (if threads<2 ∨ P.hp<3 then none else some ref) := by
  classical
  unfold worker
  split
  · rfl
  rename_i active
  let sub := ParallelKeygen.subHeight x86 P.hp
  let n := ParallelKeygen.count x86 P.hp
  obtain ⟨within,cap,geom⟩ := ParallelKeygen.geometry x86 P.hp height
  have width (i) (hi : i<n) : (word i).val=i := word_val (by omega)
  have sw : (word sub).val=sub := word_val (by omega)
  have nodes (i : Nat) (hi : i<n) : computed e sk s a sub i =
      Spec.xmssNode P (bytes sk.val) i sub (e.seedBytes s) (adrsS a) := by
    obtain ⟨out,hout,good⟩ := spec_imp_exists (correct sk (word i) (word sub) s a hs (by rw [width i hi,sw]; exact geom i hi))
    have existsOut : ∃ v,e.node sk (word i) (word sub) s a=ok v := ⟨out,hout⟩
    have eq := Result.ok_injective (existsOut.choose_spec.symm.trans hout)
    simpa only [computed, dif_pos existsOut,eq,width i hi,sw] using good
  let final := ParallelKeygen.finished n (participants pool (min threads n)) (computed e sk s a sub)
  have pos : 0<participants pool (min threads n) := by unfold participants; split <;> omega
  have root := ParallelKeygen.joined_root P (bytes sk.val) (e.seedBytes s) (adrsS a) sub _ within pos _
    nodes final.property.1 final.property.2
  change Std.bind (pack (ParallelKeygen.result P (e.seedBytes s) (adrsS a) sub final.val)) _=_
  rw [root,←value,pack_bytes,bind_ok]


namespace S2
theorem caller_eq [e : Engine hash.Seed] [host : Host] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8)
    (nodes : NodeCorrect (N:=N) e (paramsS p) (SeedOk))
    (ctx : ∃ s, e.seedCtx pkSeed=ok s ∧ e.seedBytes s=bytes pkSeed.val ∧ (SeedOk) s) :
    slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk =
      slhdsa.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk := by
  obtain ⟨s,get,seedBytes,valid⟩ := ctx
  have hd : 2≤p.d.val := hp.valid.d_ge
  obtain ⟨last,topLayer,_⟩ := spec_imp_exists (U32.sub_spec (x:=p.d) (y:=1#u32) (by scalar_tac))
  have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
  obtain ⟨refSeed,refCtx,pub,refValid⟩ := spec_imp_exists (seed_ctx_spec hp.nok pkSeed)
  have same (a : address.Adrs) :
      (do let o ← worker e (paramsS p) host.x86 host.threads host.pool skSeed s a
          core.option.Option.unwrap_or_else
            (slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N N) o (skSeed,p,s,a)) =
        slhdsa.xmss.xmss_node skSeed 0#u32 p.hp refSeed a := by
    obtain ⟨ref,serial,shape⟩ := spec_imp_exists (slhdsa.xmss_node_spec p hp skSeed 0#u32 p.hp refSeed refValid a (by simp; omega))
    have value : bytes ref.val=Spec.xmssNode (paramsS p) (bytes skSeed.val) 0 (paramsS p).hp (e.seedBytes s) (adrsS a) := by
      simpa only [seedBytes,pub,paramsS_hp,show (0#u32).val=0 by decide] using shape
    obtain ⟨v,actual,good⟩ := spec_imp_exists (nodes skSeed 0#u32 p.hp s a valid (by simp [paramsS_hp]))
    have eq : v=ref := Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (good.trans value.symm))
    simp only [worker_value e (paramsS p) _ hp.valid.hp_le nodes _ _ _ skSeed s valid a ref value,bind_ok,serial]
    split
    · exact actual.trans (congrArg Result.ok eq)
    · rfl
  unfold slh.slh_keygen_internal slhdsa.slh.slh_keygen_internal
  simp only [address.Adrs.new,address.Adrs.with_layer,topLayer,hash.seed_ctx,get,refCtx,bind_ok,slh.parallel.keygen]
  rw [←same]
  rw [Std.bind_assoc]

theorem caller_fips [e : Engine hash.Seed] [host : Host] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8) (skLen : sk.length=4*N.val) (pkLen : pk.length=2*N.val)
    (nodes : NodeCorrect (N:=N) e (paramsS p) (SeedOk))
    (ctx : ∃ s, e.seedCtx pkSeed=ok s ∧ e.seedBytes s=bytes pkSeed.val ∧ (SeedOk) s) :
    slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (paramsS p) (bytes skSeed.val)
        (bytes skPrf.val) (bytes pkSeed.val) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ := by
  rw [caller_eq p hp skSeed skPrf pkSeed sk pk nodes ctx]
  exact slhdsa.slh_keygen_internal_spec p hp skSeed skPrf pkSeed sk pk skLen pkLen
end S2

namespace Sh
theorem caller_eq [e : Engine ShakeSeed] [host : Host] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8)
    (nodes : NodeCorrect (N:=N) e (Shake.params p) (fun _ => True))
    (ctx : ∃ s, e.seedCtx pkSeed=ok s ∧ e.seedBytes s=bytes pkSeed.val ∧ (fun _ => True) s) :
    shake.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk =
      slhdsa.shake.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk := by
  obtain ⟨s,get,seedBytes,valid⟩ := ctx
  have hd : 2≤p.d.val := hp.valid.d_ge
  obtain ⟨last,topLayer,_⟩ := spec_imp_exists (U32.sub_spec (x:=p.d) (y:=1#u32) (by scalar_tac))
  have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
  let refSeed := pkSeed
  have refCtx : slhdsa.shake.hash.seed_ctx pkSeed = ok refSeed := rfl
  have same (a : address.Adrs) :
      (do let o ← worker e (Shake.params p) host.x86 host.threads host.pool skSeed s a
          core.option.Option.unwrap_or_else
            (shake.slh.slh_keygen_internal.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N N) o (skSeed,p,s,a)) =
        slhdsa.shake.xmss.xmss_node skSeed 0#u32 p.hp refSeed a := by
    obtain ⟨ref,serial,shape⟩ := spec_imp_exists (Shake.xmss_node_spec p hp skSeed 0#u32 p.hp refSeed a (by simp; omega))
    have value : bytes ref.val=Spec.xmssNode (Shake.params p) (bytes skSeed.val) 0 (Shake.params p).hp (e.seedBytes s) (adrsS a) := by
      simpa only [seedBytes,refSeed,Shake.params,paramsS_hp,show (0#u32).val=0 by decide] using shape
    obtain ⟨v,actual,good⟩ := spec_imp_exists (nodes skSeed 0#u32 p.hp s a valid (by simp [paramsS_hp,Shake.params]))
    have eq : v=ref := Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (good.trans value.symm))
    simp only [worker_value e (Shake.params p) _ hp.valid.hp_le nodes _ _ _ skSeed s valid a ref value,bind_ok,serial]
    split
    · exact actual.trans (congrArg Result.ok eq)
    · rfl
  unfold shake.slh.slh_keygen_internal slhdsa.shake.slh.slh_keygen_internal
  simp only [address.Adrs.new,address.Adrs.with_layer,topLayer,shake.hash.seed_ctx,get,refCtx,bind_ok,shake.slh.parallel.keygen]
  rw [←same]
  rw [Std.bind_assoc]

theorem caller_fips [e : Engine ShakeSeed] [host : Host] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8) (skLen : sk.length=4*N.val) (pkLen : pk.length=2*N.val)
    (nodes : NodeCorrect (N:=N) e (Shake.params p) (fun _ => True))
    (ctx : ∃ s, e.seedCtx pkSeed=ok s ∧ e.seedBytes s=bytes pkSeed.val ∧ (fun _ => True) s) :
    shake.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p) (bytes skSeed.val)
        (bytes skPrf.val) (bytes pkSeed.val) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ := by
  rw [caller_eq p hp skSeed skPrf pkSeed sk pk nodes ctx]
  exact Shake.slh_keygen_internal_spec p hp skSeed skPrf pkSeed sk pk skLen pkLen
end Sh

end
end slhdsa.ParallelKeygenHost
