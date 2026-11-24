import Peerarmkeccak.Funs
import Ksha3.Fips
open Aeneas Aeneas.Std Result
namespace PeerKeccak.Arm
open slhdsa.Ksha3
open PeerArmRust
set_option maxHeartbeats 3500000
set_option maxRecDepth 65536

private theorem index {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
    a.index_usize i = ok a.val[i.val]! := by
  have hi : i.val<a.val.length := by simpa using h
  simp [Array.index_usize,Array.getElem?_Usize_eq,getElem?_pos a.val i.val hi,getElem!_pos a.val i.val hi]

def pure_theta (s : Rows) : Reg × Reg × Reg × Reg × Reg :=
  let uxt : Reg := s.val[0]!
  let uxt1 : Reg := s.val[5]!
  let uxt2 : Reg := s.val[10]!
  let uxt3 : Reg := s.val[15]!
  let uxt4 : Reg := s.val[20]!
  let uxt5 : Reg := fun j => uxt2 j ^^^ uxt3 j ^^^ uxt4 j
  let c0 : Reg := fun j => uxt j ^^^ uxt1 j ^^^ uxt5 j
  let uxt6 : Reg := s.val[1]!
  let uxt7 : Reg := s.val[6]!
  let uxt8 : Reg := s.val[11]!
  let uxt9 : Reg := s.val[16]!
  let uxt10 : Reg := s.val[21]!
  let uxt11 : Reg := fun j => uxt8 j ^^^ uxt9 j ^^^ uxt10 j
  let c1 : Reg := fun j => uxt6 j ^^^ uxt7 j ^^^ uxt11 j
  let uxt12 : Reg := s.val[2]!
  let uxt13 : Reg := s.val[7]!
  let uxt14 : Reg := s.val[12]!
  let uxt15 : Reg := s.val[17]!
  let uxt16 : Reg := s.val[22]!
  let uxt17 : Reg := fun j => uxt14 j ^^^ uxt15 j ^^^ uxt16 j
  let c2 : Reg := fun j => uxt12 j ^^^ uxt13 j ^^^ uxt17 j
  let uxt18 : Reg := s.val[3]!
  let uxt19 : Reg := s.val[8]!
  let uxt20 : Reg := s.val[13]!
  let uxt21 : Reg := s.val[18]!
  let uxt22 : Reg := s.val[23]!
  let uxt23 : Reg := fun j => uxt20 j ^^^ uxt21 j ^^^ uxt22 j
  let c3 : Reg := fun j => uxt18 j ^^^ uxt19 j ^^^ uxt23 j
  let uxt24 : Reg := s.val[4]!
  let uxt25 : Reg := s.val[9]!
  let uxt26 : Reg := s.val[14]!
  let uxt27 : Reg := s.val[19]!
  let uxt28 : Reg := s.val[24]!
  let uxt29 : Reg := fun j => uxt26 j ^^^ uxt27 j ^^^ uxt28 j
  let c4 : Reg := fun j => uxt24 j ^^^ uxt25 j ^^^ uxt29 j
  let d0 : Reg := fun j => c4 j ^^^ (c1 j).rotateLeft 1
  let d1 : Reg := fun j => c0 j ^^^ (c2 j).rotateLeft 1
  let d2 : Reg := fun j => c1 j ^^^ (c3 j).rotateLeft 1
  let d3 : Reg := fun j => c2 j ^^^ (c4 j).rotateLeft 1
  let d4 : Reg := fun j => c3 j ^^^ (c0 j).rotateLeft 1
  (d0, d1, d2, d3, d4)

theorem theta_eq (s : Rows) : backends.aarch64_sha3.theta s = ok (pure_theta s) := by
  unfold backends.aarch64_sha3.theta pure_theta
  simp (config := {maxSteps := 1000000}) (disch := decide) only [index,bind_ok,
    PeerArmRust.core.core_arch.aarch64.neon.generated.veor3q_u64,
    PeerArmRust.core.core_arch.aarch64.neon.generated.vrax1q_u64,
    Ksha3Rust.core.core_arch.aarch64.neon.generated.veor3q_u64,
    Ksha3Rust.core.core_arch.aarch64.neon.generated.vrax1q_u64]
  all_goals rfl

def pure_rho_pi (s : Rows) (d0 d1 d2 d3 d4 : Reg) : Rows :=
  let uxt : Reg := s.val[0]!
  let v0 : Reg := fun j => uxt j ^^^ d0 j
  let uxt1 : Reg := s.val[1]!
  let v25 : Reg := fun j => (uxt1 j ^^^ d1 j).rotateRight 63
  let uxt2 : Reg := s.val[6]!
  let v1 : Reg := fun j => (uxt2 j ^^^ d1 j).rotateRight 20
  let uxt3 : Reg := s.val[9]!
  let v6 : Reg := fun j => (uxt3 j ^^^ d4 j).rotateRight 44
  let uxt4 : Reg := s.val[22]!
  let v9 : Reg := fun j => (uxt4 j ^^^ d2 j).rotateRight 3
  let uxt5 : Reg := s.val[14]!
  let v22 : Reg := fun j => (uxt5 j ^^^ d4 j).rotateRight 25
  let uxt6 : Reg := s.val[20]!
  let v14 : Reg := fun j => (uxt6 j ^^^ d0 j).rotateRight 46
  let uxt7 : Reg := s.val[2]!
  let v26 : Reg := fun j => (uxt7 j ^^^ d2 j).rotateRight 2
  let uxt8 : Reg := s.val[12]!
  let v2 : Reg := fun j => (uxt8 j ^^^ d2 j).rotateRight 21
  let uxt9 : Reg := s.val[13]!
  let v12 : Reg := fun j => (uxt9 j ^^^ d3 j).rotateRight 39
  let uxt10 : Reg := s.val[19]!
  let v13 : Reg := fun j => (uxt10 j ^^^ d4 j).rotateRight 56
  let uxt11 : Reg := s.val[23]!
  let v19 : Reg := fun j => (uxt11 j ^^^ d3 j).rotateRight 8
  let uxt12 : Reg := s.val[15]!
  let v23 : Reg := fun j => (uxt12 j ^^^ d0 j).rotateRight 23
  let uxt13 : Reg := s.val[4]!
  let v15 : Reg := fun j => (uxt13 j ^^^ d4 j).rotateRight 37
  let uxt14 : Reg := s.val[24]!
  let v28 : Reg := fun j => (uxt14 j ^^^ d4 j).rotateRight 50
  let uxt15 : Reg := s.val[21]!
  let v24 : Reg := fun j => (uxt15 j ^^^ d1 j).rotateRight 62
  let uxt16 : Reg := s.val[8]!
  let v8 : Reg := fun j => (uxt16 j ^^^ d3 j).rotateRight 9
  let uxt17 : Reg := s.val[16]!
  let v4 : Reg := fun j => (uxt17 j ^^^ d1 j).rotateRight 19
  let uxt18 : Reg := s.val[5]!
  let v16 : Reg := fun j => (uxt18 j ^^^ d0 j).rotateRight 28
  let uxt19 : Reg := s.val[3]!
  let v5 : Reg := fun j => (uxt19 j ^^^ d3 j).rotateRight 36
  let uxt20 : Reg := s.val[18]!
  let v27 : Reg := fun j => (uxt20 j ^^^ d3 j).rotateRight 43
  let uxt21 : Reg := s.val[17]!
  let v3 : Reg := fun j => (uxt21 j ^^^ d2 j).rotateRight 49
  let uxt22 : Reg := s.val[11]!
  let v30 : Reg := fun j => (uxt22 j ^^^ d1 j).rotateRight 54
  let uxt23 : Reg := s.val[7]!
  let v31 : Reg := fun j => (uxt23 j ^^^ d2 j).rotateRight 58
  let uxt24 : Reg := s.val[10]!
  let v29 : Reg := fun j => (uxt24 j ^^^ d0 j).rotateRight 61
  (Array.make 25#usize [
      v0, v25, v26, v5, v15, v16, v1, v31, v8, v6, v29, v30, v2, v12, v22, v23,
      v4, v3, v27, v13, v14, v24, v9, v19, v28
      ])

theorem rho_pi_eq (s : Rows) (d0 d1 d2 d3 d4 : Reg) : backends.aarch64_sha3.rho_pi s d0 d1 d2 d3 d4 = ok (pure_rho_pi s d0 d1 d2 d3 d4) := by
  unfold backends.aarch64_sha3.rho_pi pure_rho_pi
  simp (config := {maxSteps := 1000000}) (disch := decide) only [index,bind_ok,
    PeerArmRust.core.core_arch.aarch64.neon.generated.vxarq_u64,
    PeerArmRust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    Ksha3Rust.core.core_arch.aarch64.neon.generated.vxarq_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64]
  all_goals rfl

def pure_chi_iota (t : Rows) (rc : U64) : Rows :=
  let rc_v : Reg := fun _ => rc.bv
  let uxt : Reg := t.val[2]!
  let uxt1 : Reg := t.val[14]!
  let uxt2 : Reg := t.val[8]!
  let v20 : Reg := fun j => uxt j ^^^ (uxt1 j &&& ~~~(uxt2 j))
  let uxt3 : Reg := t.val[15]!
  let v21 : Reg := fun j => uxt2 j ^^^ (uxt3 j &&& ~~~(uxt1 j))
  let uxt4 : Reg := t.val[21]!
  let v22 : Reg := fun j => uxt1 j ^^^ (uxt4 j &&& ~~~(uxt3 j))
  let v23 : Reg := fun j => uxt3 j ^^^ (uxt j &&& ~~~(uxt4 j))
  let v24 : Reg := fun j => uxt4 j ^^^ (uxt2 j &&& ~~~(uxt j))
  let uxt5 : Reg := t.val[11]!
  let uxt6 : Reg := t.val[23]!
  let uxt7 : Reg := t.val[17]!
  let v17 : Reg := fun j => uxt5 j ^^^ (uxt6 j &&& ~~~(uxt7 j))
  let uxt8 : Reg := t.val[4]!
  let v18 : Reg := fun j => uxt7 j ^^^ (uxt8 j &&& ~~~(uxt6 j))
  let uxt9 : Reg := t.val[5]!
  let v19 : Reg := fun j => uxt6 j ^^^ (uxt9 j &&& ~~~(uxt8 j))
  let v15 : Reg := fun j => uxt8 j ^^^ (uxt5 j &&& ~~~(uxt9 j))
  let v16 : Reg := fun j => uxt9 j ^^^ (uxt7 j &&& ~~~(uxt5 j))
  let uxt10 : Reg := t.val[1]!
  let uxt11 : Reg := t.val[13]!
  let uxt12 : Reg := t.val[7]!
  let v10 : Reg := fun j => uxt10 j ^^^ (uxt11 j &&& ~~~(uxt12 j))
  let uxt13 : Reg := t.val[19]!
  let v11 : Reg := fun j => uxt12 j ^^^ (uxt13 j &&& ~~~(uxt11 j))
  let uxt14 : Reg := t.val[20]!
  let v12 : Reg := fun j => uxt11 j ^^^ (uxt14 j &&& ~~~(uxt13 j))
  let v13 : Reg := fun j => uxt13 j ^^^ (uxt10 j &&& ~~~(uxt14 j))
  let v14 : Reg := fun j => uxt14 j ^^^ (uxt12 j &&& ~~~(uxt10 j))
  let uxt15 : Reg := t.val[10]!
  let uxt16 : Reg := t.val[22]!
  let uxt17 : Reg := t.val[16]!
  let v7 : Reg := fun j => uxt15 j ^^^ (uxt16 j &&& ~~~(uxt17 j))
  let uxt18 : Reg := t.val[3]!
  let v8 : Reg := fun j => uxt17 j ^^^ (uxt18 j &&& ~~~(uxt16 j))
  let uxt19 : Reg := t.val[9]!
  let v9 : Reg := fun j => uxt16 j ^^^ (uxt19 j &&& ~~~(uxt18 j))
  let v5 : Reg := fun j => uxt18 j ^^^ (uxt15 j &&& ~~~(uxt19 j))
  let v6 : Reg := fun j => uxt19 j ^^^ (uxt17 j &&& ~~~(uxt15 j))
  let uxt20 : Reg := t.val[18]!
  let uxt21 : Reg := t.val[0]!
  let uxt22 : Reg := t.val[24]!
  let v3 : Reg := fun j => uxt20 j ^^^ (uxt21 j &&& ~~~(uxt22 j))
  let uxt23 : Reg := t.val[6]!
  let v4 : Reg := fun j => uxt22 j ^^^ (uxt23 j &&& ~~~(uxt21 j))
  let uxt24 : Reg := t.val[12]!
  let v0 : Reg := fun j => uxt21 j ^^^ (uxt24 j &&& ~~~(uxt23 j))
  let v1 : Reg := fun j => uxt23 j ^^^ (uxt20 j &&& ~~~(uxt24 j))
  let v2 : Reg := fun j => uxt24 j ^^^ (uxt22 j &&& ~~~(uxt20 j))
  let v0_iota : Reg := fun j => v0 j ^^^ rc_v j
  (Array.make 25#usize [
      v0_iota, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
      v15, v16, v17, v18, v19, v20, v21, v22, v23, v24
      ])

theorem chi_iota_eq (t : Rows) (rc : U64) : backends.aarch64_sha3.chi_iota t rc = ok (pure_chi_iota t rc) := by
  unfold backends.aarch64_sha3.chi_iota pure_chi_iota
  simp (config := {maxSteps := 1000000}) (disch := decide) only [index,bind_ok,
    PeerArmRust.core.core_arch.aarch64.neon.generated.vbcaxq_u64,
    PeerArmRust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    PeerArmRust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    Ksha3Rust.core.core_arch.aarch64.neon.generated.vbcaxq_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64]
  all_goals rfl

def pureRound (a : Rows) (rc : U64) : Rows :=
  let (d0,d1,d2,d3,d4) := pure_theta a
  pure_chi_iota (pure_rho_pi a d0 d1 d2 d3 d4) rc

end PeerKeccak.Arm
