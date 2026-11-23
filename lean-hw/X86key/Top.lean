import X86key.Node
import X86key.Seed
import Slhdsa.Proofs.Api
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Key

theorem node_eq {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (s : X86KeyRust.hash.Seed N) (hs : SeedOk (seedOf s)) (a : X86KeyRust.address.Adrs)
    (room : (i.val+1)*2^z.val ≤ 2^p.hp.val) :
    X86KeyRust.xmss.xmss_node sk i z s a = xmss.xmss_node sk i z (seedOf s) (addr a) := by
  have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
  obtain ⟨x,hx,fx⟩ := spec_imp_exists (node_fips p hp sk s hs a z.val i z rfl room)
  obtain ⟨y,hy,fy⟩ := spec_imp_exists (xmss_node_spec p hp sk i z (seedOf s) hs (addr a) (by omega))
  rw [hx,hy]
  congr 1
  exact Aeneas.Std.Array.ext x y ((bytes_inj _ _).mp (fx.trans fy.symm))

theorem internal_eq {N} (p : X86KeyRust.params.Params) (hp : PN (paramsOf p) N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8) :
    X86KeyRust.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk =
      slh.slh_keygen_internal (paramsOf p) skSeed skPrf pkSeed sk pk := by
  obtain ⟨s,actual,pkX,valid⟩ := spec_imp_exists (seed_spec hp.nok pkSeed)
  obtain ⟨base,ctx,pkB,baseOk⟩ := spec_imp_exists (seed_ctx_spec hp.nok pkSeed)
  have same (a : X86KeyRust.address.Adrs) : X86KeyRust.xmss.xmss_node skSeed 0#u32 p.hp s a =
      xmss.xmss_node skSeed 0#u32 p.hp base (addr a) := by
    obtain ⟨x,hx,fx⟩ := spec_imp_exists (node_fips (paramsOf p) hp skSeed s valid a p.hp.val 0#u32 p.hp rfl (by simp [paramsOf]))
    have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
    obtain ⟨y,hy,fy⟩ := spec_imp_exists (xmss_node_spec (paramsOf p) hp skSeed 0#u32 p.hp base baseOk (addr a) (by simp; omega))
    rw [hx,hy]
    congr 1
    exact Aeneas.Std.Array.ext x y ((bytes_inj _ _).mp (by rw [fx,fy,pkX,pkB]))
  unfold X86KeyRust.slh.slh_keygen_internal slh.slh_keygen_internal
  simp only [X86KeyRust.address.Adrs.new,address.Adrs.new,X86KeyRust.address.Adrs.with_layer,
    address.Adrs.with_layer,actual,ctx,bind_ok,same]
  rfl

theorem keygen_eq {N} (p : X86KeyRust.params.Params) (hp : PN (paramsOf p) N)
    (seeds sk pk : Slice U8) : X86KeyRust.api.keygen N p seeds sk pk = api.keygen N (paramsOf p) seeds sk pk := by
  unfold X86KeyRust.api.keygen api.keygen
  simp only [internal_eq p hp]
  rfl

/-- FIPS 205 key generation from the public x86 entry, for every SHA-2 parameter set and dispatch outcome. -/
theorem keygen_fips {N} (p : X86KeyRust.params.Params) (hp : PN (paramsOf p) N)
    (seeds sk pk : Slice U8) (seedLen : seeds.length=3*N.val) (skLen : sk.length=4*N.val)
    (pkLen : pk.length=2*N.val) :
    X86KeyRust.api.keygen N p seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) = Spec.slhKeygenInternal (paramsS (paramsOf p))
        (Spec.block (paramsS (paramsOf p)) (bytes seeds.val) 0)
        (Spec.block (paramsS (paramsOf p)) (bytes seeds.val) 1)
        (Spec.block (paramsS (paramsOf p)) (bytes seeds.val) 2) ∧
      r.1.length=4*N.val ∧ r.2.length=2*N.val ⦄ := by
  rw [keygen_eq p hp]
  exact api_keygen_spec _ hp _ _ _ seedLen skLen pkLen

theorem public_key_fips {N} (p : X86KeyRust.params.Params) (hp : PN (paramsOf p) N)
    (sk pk : Slice U8) (skLen : sk.length=4*N.val) (pkLen : pk.length=2*N.val) :
    X86KeyRust.api.public_key N sk pk ⦃ out =>
      bytes out.val=Spec.skPk (paramsS (paramsOf p)) (bytes sk.val) ∧ out.length=2*N.val ⦄ := by
  exact api_public_key_spec (paramsOf p) hp sk pk skLen pkLen
end slhdsa.X86.Key
