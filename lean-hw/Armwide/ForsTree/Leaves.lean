import Armwide.SignBlocks
import Armwide.SignLoad
import Spec.SlhDsa

namespace slhdsa.ArmForsTree
open Armwide.Transitions

private def domain (a : Spec.Adrs) (typ : Nat) := {a.setTypeAndClear typ with keypair:=a.keypair}

def fusedLeaf (n : Nat) (state : List Spec.SHA256.Word) (sk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) :=
  let key := loadDigest n sk
  let secret := hashRegisters n state (domain a Spec.FORS_PRF) 0 i key.1 key.2
  let leaf := hashRegisters n state (domain a Spec.FORS_TREE) 0 i secret.1 secret.2
  storedBytes n leaf.1 leaf.2

/-- The two native short-block invocations use the same absolute index but
distinct FORS domains, and the second consumes the first one's digest registers. -/
theorem fused_leaf_fips (p : Spec.Params) [Fact (p.family=.sha2)] (v : p.Valid)
    (pk sk : Spec.Bytes) (pkSize : pk.length=p.n) (skSize : sk.length=p.n) (a : Spec.Adrs)
    (tree : a.typ=Spec.FORS_TREE) (i : Nat) :
    fusedLeaf p.n (seedState p.n pk) sk a i=Spec.forsNode p sk i 0 pk a := by
  let n := p.n
  let key := loadDigest n sk
  let sec := hashRegisters n (seedState n pk) (domain a Spec.FORS_PRF) 0 i key.1 key.2
  have secret := native_tweakable_hash n v.n_cases pk pkSize (domain a Spec.FORS_PRF) 0 i (by decide) key.1 key.2
  have value := native_tweakable_hash n v.n_cases pk pkSize (domain a Spec.FORS_TREE) 0 i (by decide) sec.1 sec.2
  dsimp only at secret value
  have contents : Armwide.Kernel.storeN n sec.1 sec.2=Spec.forsSkGen p sk pk a i := by
    rw [stored_eq n v.n_cases] at secret
    rw [show Armwide.Kernel.storeN n key.1 key.2=sk from load_content n v.n_cases sk skSize] at secret
    simpa only [Spec.forsSkGen,PRF_eq,sec,n,domain,Spec.Adrs.setTypeAndClear] using secret
  rw [contents] at value
  change storedBytes n _ _=_
  rw [value]
  simp only [Spec.forsNode,F_eq]
  congr 1
  cases a
  simp_all [domain,Spec.Adrs.setTypeAndClear]

end slhdsa.ArmForsTree
