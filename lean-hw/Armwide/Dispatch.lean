import Armwide.DispatchProgram
import Cacheops.Funs

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Public.Dispatcher

/-- Both outcomes of Arm feature detection in the production public WOTS dispatcher
produce the same Rust vector at the signing addresses used in the cached path. -/
theorem wots_dispatch_eq [cpu : Cpu] {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (reachable : hashAddress (slhdsa.adrsS a) = slhdsa.adrsS a) :
    wots.wots_sign m sk seed a = slhdsa.wots.wots_sign m sk seed a := by
  have sizes := hp.nok
  unfold wots.wots_sign
  rcases sizes with h|h|h <;> simp only [h,bind_ok,ite_true,sha256.arm_wide.available] <;> cases cpu.wide
  all_goals first | rfl | exact sign_eq_scalar p hp m sk seed hs a reachable

theorem cached_wots_dispatch_eq [Cpu] {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (CacheopsRust.toSlhParams p) N) (m sk : Array U8 N) (seed : CacheopsRust.hash.Seed N)
    (hs : SeedOk (CacheopsRust.toSlhSeed seed)) (a : CacheopsRust.address.Adrs)
    (reachable : hashAddress (slhdsa.adrsS (CacheopsRust.toSlhAdrs a)) = slhdsa.adrsS (CacheopsRust.toSlhAdrs a)) :
    wots.wots_sign m sk (CacheopsRust.toSlhSeed seed) (CacheopsRust.toSlhAdrs a) =
      CacheopsRust.wots.wots_sign m sk seed a :=
  wots_dispatch_eq _ hp m sk _ hs _ reachable

/-- Both cache-hit signing branches form the WOTS address this way. Address
normalization is discharged here from the extracted Rust constructors. -/
theorem cached_hit_wots [Cpu] {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (CacheopsRust.toSlhParams p) N) (m sk : Array U8 N) (seed : CacheopsRust.hash.Seed N)
    (hs : SeedOk (CacheopsRust.toSlhSeed seed)) (a : CacheopsRust.address.Adrs) (leaf : U32) :
    (show Result (alloc.vec.Vec U8) from do
        let t ← CacheopsRust.address.Adrs.with_type a CacheopsRust.address.WOTS_HASH
        let w ← CacheopsRust.address.Adrs.with_keypair t leaf
        wots.wots_sign m sk (CacheopsRust.toSlhSeed seed) (CacheopsRust.toSlhAdrs w)) =
    (show Result (alloc.vec.Vec U8) from do
        let t ← CacheopsRust.address.Adrs.with_type a CacheopsRust.address.WOTS_HASH
        let w ← CacheopsRust.address.Adrs.with_keypair t leaf
        CacheopsRust.wots.wots_sign m sk seed w) := by
  simp only [CacheopsRust.address.Adrs.with_type,CacheopsRust.address.Adrs.with_keypair,bind_ok]
  change wots.wots_sign m sk _ (CacheopsRust.toSlhAdrs {a with typ:=CacheopsRust.address.WOTS_HASH, keypair:=leaf, word2:=0#u32, word3:=0#u32}) = _
  apply cached_wots_dispatch_eq p hp m sk seed hs
  with_unfolding_all rfl

end slhdsa.Armwide.Public.Dispatcher
