import Cachepath.KeygenProgram
import Cachepath.BuiltSession
import Spec.Correctness

open Aeneas Aeneas.Std Result slhdsa
open slhdsa.cache.endtoend
namespace CacheopsRust.cache.generatedKeys

def specKeys (p : Spec.Params) (seeds : Slice U8) : Spec.Bytes × Spec.Bytes :=
  Spec.slhKeygenInternal p (Spec.block p (bytes seeds.val) 0) (Spec.block p (bytes seeds.val) 1)
    (Spec.block p (bytes seeds.val) 2)

def Output (N : Usize) := cache.TopTreeCache N × Slice U8 × Slice U8

/-- The generated public key, secret key, and cache refer to the same FIPS keypair.
Lengths and the invariant are stated over the actual buffers returned to the caller. -/
structure Generated {N : Usize} (p : Spec.Params) (family : HashFamily) (seeds : Slice U8)
    (out : Output N) : Prop where
  keys : (bytes out.2.1.val, bytes out.2.2.val) = specKeys p seeds
  secretLength : out.2.1.length = 4*N.val
  publicLength : out.2.2.length = 2*N.val
  wellFormed : Spec.KeyOk p (bytes out.2.1.val)
  publicKey : bytes out.2.2.val = Spec.skPk p (bytes out.2.1.val)
  familyEq : out.1.family = family
  valid : CacheValid out.1 p (Spec.block p (bytes out.2.1.val) 0) (Spec.block p (bytes out.2.1.val) 2)
  accepted : TopTreeCache.matches_key out.1 out.2.1 = ok true
  capacity : out.1.layer_d2_capacity = 0#usize
  entries : out.1.layer_d2.val = []

private theorem read_seed {N : Usize} (P : Spec.Params) (n : P.n = N.val) (seed : Slice U8) (i : Usize)
    (h : (i.val+1)*N.val ≤ seed.length) : CacheopsRust.util.block N seed i ⦃ v =>
      bytes v.val = Spec.block P (bytes seed.val) i.val ⦄ := by
  apply WP.spec_mono (block_spec N seed i h)
  intro v hv
  simp [Spec.block,n,hv,bytes,List.map_take,List.map_drop]

private theorem select {N : Usize} (family : HashFamily) (sha2 shake : mutation.Builder N)
    (p : CacheopsRust.params.Params) (P : Spec.Params) (hd : p.d.val = P.d) (height : p.hp.val = P.hp)
    (valid : P.Valid) (sk pk : Array U8 N)
    (a : family = .Sha2 → constructor.TreeKernel sha2 P)
    (b : family = .Shake → constructor.TreeKernel shake P) :
    (match family with
    | .Sha2 => do let layer ← p.d - 1#u32; sha2 p.hp layer 0#u64 sk pk
    | .Shake => do let layer ← p.d - 1#u32; shake p.hp layer 0#u64 sk pk) ⦃ tree =>
      tree.length = treeSize P.hp ∧ slhdsa.cache.Built tree.deref P (bytes sk.val) (bytes pk.val)
        (layerAdrs (P.d-1) 0) ⦄ := by
  have pos := valid.d_ge
  cases family
  · step as ⟨l,hl⟩
    simpa [hl,hd] using a rfl p.hp l 0#u64 sk pk height
  · step as ⟨l,hl⟩
    simpa [hl,hd] using b rfl p.hp l 0#u64 sk pk height

private theorem keyBlocks (P : Spec.Params) (secret prf pub root : Spec.Bytes)
    (a : secret.length = P.n) (b : prf.length = P.n) (c : pub.length = P.n) :
    Spec.block P (secret ++ prf ++ pub ++ root) 0 = secret ∧
    Spec.block P (secret ++ prf ++ pub ++ root) 2 = pub := by
  simp only [Spec.block,List.append_assoc,Nat.zero_mul,List.drop_zero,List.take_left' a]
  rw [show 2*P.n=P.n+P.n by omega,← List.drop_drop,List.drop_left' a,List.drop_left' b,List.take_left' c]
  simp

set_option maxHeartbeats 2000000 in
theorem keygen_spec {N : Usize} (sha2 shake : mutation.Builder N) (family : HashFamily)
    (p : CacheopsRust.params.Params) (P : Spec.Params) (hn : N = p.n) (n : P.n = N.val)
    (hd : p.d.val = P.d) (height : p.hp.val = P.hp) (valid : P.Valid)
    (a : family = .Sha2 → constructor.TreeKernel sha2 P)
    (b : family = .Shake → constructor.TreeKernel shake P)
    (seeds sk pk : Slice U8) (ss : seeds.length = 3*N.val) (ks : sk.length = 4*N.val)
    (ps : pk.length = 2*N.val) :
    keygen N sha2 shake family p seeds sk pk ⦃ out => Generated P family seeds out ⦄ := by
  have bound : 4*N.val ≤ Usize.max := ks ▸ sk.property
  have wrap (v : Slice U8) (k : Usize) (h : v.length=k.val*N.val) :
      v.len = Usize.wrapping_mul k N := by
    have cap := v.property
    change v.length ≤ Usize.max at cap
    apply UScalar.eq_of_val_eq
    simp [h,Nat.mod_eq_of_lt (by scalar_tac : k.val*N.val < Usize.size)]
  unfold keygen
  simp only [ite_eq_left hn,lift,bind_ok,ite_eq_left (wrap seeds 3#usize ss),
    ite_eq_left (wrap sk 4#usize ks),ite_eq_left (wrap pk 2#usize ps)]
  step as ⟨three,h3⟩
  step as ⟨four,h4⟩
  step as ⟨two,h2⟩
  step with read_seed P n seeds 0#usize (by scalar_tac) as ⟨secret,hSecret⟩
  step with read_seed P n seeds 1#usize (by scalar_tac) as ⟨prf,hPrf⟩
  step with read_seed P n seeds 2#usize (by scalar_tac) as ⟨pub,hPublic⟩
  apply WP.spec_bind (select family sha2 shake p P hd height valid secret pub a b)
  rintro tree ⟨treeLen,built⟩
  let c : TopTreeCache N := ⟨family,p.hp,p.d,pub,tree,alloc.vec.Vec.new _,0#usize⟩
  have good : CacheValid c P (bytes secret.val) (bytes pub.val) :=
    ⟨height,hd,rfl,treeLen,built,by intro e h; change e ∈ ([] : List _) at h; simp at h⟩
  step with slhdsa.cache.root tree.deref (by rw [vec_deref_len,treeLen]; exact treeSize_pos _) as ⟨root,atRoot⟩
  have rootSpec : bytes root.val = Spec.xmssNode P (bytes secret.val) 0 P.hp (bytes pub.val) (layerAdrs (P.d-1) 0) := by
    rw [atRoot,vec_deref_len,slhdsa.vec_deref_val]
    exact top_root_eq_fips good
  step*
  all_goals try (subst_vars; scalar_tac)
  all_goals try (rw [s13_post2]; change two.val ≤ _; rw [Slice.setSlice!_length]; omega)
  have ksz : sk.val.length = 4*N.val := ks
  have psz : pk.val.length = 2*N.val := ps
  have secretBuf : (index_mut_back3 s12).val = secret.val ++ prf.val ++ pub.val ++ root.val := by
    rw [s10_post2,s12_post,s7_post2,s9_post,s4_post2,s6_post,s1_post2,s3_post]
    simp only [Array.val_to_slice,Slice.setSlice!_val]
    apply setSlice4 <;> simp only [Array.property] <;> omega
  have publicBuf : (index_mut_back5 s18).val = pub.val ++ root.val := by
    rw [s16_post2,s18_post,s13_post2,s15_post]
    simp only [Array.val_to_slice,Slice.setSlice!_val]
    apply setSlice2 <;> simp only [Array.property]
    omega
  let sk' := index_mut_back3 s12
  let pk' := index_mut_back5 s18
  change Generated P family seeds (c,sk',pk')
  have skBytes : bytes sk'.val = bytes secret.val ++ bytes prf.val ++ bytes pub.val ++ bytes root.val := by
    simp [sk',secretBuf,bytes]
  have pkBytes : bytes pk'.val = bytes pub.val ++ bytes root.val := by simp [pk',publicBuf,bytes]
  have keys : (bytes sk'.val,bytes pk'.val) =
      Spec.slhKeygenInternal P (bytes secret.val) (bytes prf.val) (bytes pub.val) := by
    simp only [Spec.slhKeygenInternal,skBytes,pkBytes,rootSpec,layerAdrs]
    rfl
  have sz (v : Array U8 N) : (bytes v.val).length = P.n := by simp [bytes,n]
  have keyOk := Spec.keygen_keyOk P valid _ _ _ (sz secret) (sz prf) (sz pub)
  rw [← keys] at keyOk
  have blocks := keyBlocks P _ _ _ (bytes root.val) (sz secret) (sz prf) (sz pub)
  rw [← skBytes] at blocks
  have validKey : CacheValid c P (Spec.block P (bytes sk'.val) 0) (Spec.block P (bytes sk'.val) 2) := by
    rw [blocks.1,blocks.2]; exact good
  have skLen : sk'.length = 4 * N.val := by
    change (index_mut_back3 s12).val.length = _
    rw [secretBuf]
    simp only [List.length_append,Array.property]; omega
  have pkLen : pk'.length = 2 * N.val := by
    change (index_mut_back5 s18).val.length = _
    rw [publicBuf]
    simp only [List.length_append,Array.property]; omega
  exact ⟨by simpa only [specKeys,← hSecret,← hPrf,← hPublic] using keys,
    skLen,pkLen,keyOk.1,keyOk.2,rfl,validKey,
    (matches_key_valid_key c P sk' n bound skLen keyOk.1 validKey).2,rfl,rfl⟩

end CacheopsRust.cache.generatedKeys
