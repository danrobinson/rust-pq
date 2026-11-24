import Kmixed.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.Kmixed
namespace Operations
def xor3 (a b c : V) : V := ⟨fun j => a.pair j ^^^ (b.pair j ^^^ c.pair j),(a.scalar ^^^ b.scalar) ^^^ c.scalar⟩
def theta (a b : V) : V := ⟨fun j => a.pair j ^^^ (((b.pair j <<< 1) &&& (BitVec.allOnes 64 <<< 1)) ||| (b.pair j >>> 63)),a.scalar ^^^ core.num.U64.rotate_left b.scalar 1#u32⟩
def rho (R S : I32) (a b : V) : V :=
  ⟨fun j => let x := a.pair j ^^^ b.pair j
            ((x <<< R.bv.toNat) &&& (BitVec.allOnes 64 <<< (64-S.bv.toNat))) ||| (x >>> S.bv.toNat),
    core.num.U64.rotate_left (a.scalar ^^^ b.scalar) (IScalar.hcast .U32 R)⟩
def chi (a b c : V) : V := ⟨fun j => a.pair j ^^^ (c.pair j &&& ~~~(b.pair j)),a.scalar ^^^ ((~~~b.scalar) &&& c.scalar)⟩
def iota (a : V) (rc : U64) : V := ⟨fun j => a.pair j ^^^ rc.bv,a.scalar ^^^ rc⟩
local macro "mixed_ops" : tactic => `(tactic|
  simp only [lift,bind_ok,
    KmixedRust.shake256.parallel.mixed.xor3,
    KmixedRust.shake256.parallel.mixed.theta,
    KmixedRust.shake256.parallel.mixed.rho,
    KmixedRust.shake256.parallel.mixed.chi,
    KmixedRust.shake256.parallel.mixed.iota,
    KmixedRust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    KmixedRust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    KmixedRust.core.core_arch.arm_shared.neon.generated.vbicq_u64,
    KmixedRust.core.core_arch.arm_shared.neon.generated.vshlq_n_u64,
    KmixedRust.core.core_arch.aarch64.neon.generated.vsriq_n_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64] )

theorem xor3_eq (a b c : V) : KmixedRust.shake256.parallel.mixed.xor3 a b c = ok (xor3 a b c) := by
  mixed_ops
  rfl
theorem theta_eq (a b : V) : KmixedRust.shake256.parallel.mixed.theta a b = ok (theta a b) := by
  mixed_ops
  rfl
theorem rho_eq (R S : I32) (a b : V) : KmixedRust.shake256.parallel.mixed.rho R S a b = ok (rho R S a b) := by
  mixed_ops
  rfl
theorem chi_eq (a b c : V) : KmixedRust.shake256.parallel.mixed.chi a b c = ok (chi a b c) := by
  mixed_ops
  rfl
theorem iota_eq (a : V) (rc : U64) : KmixedRust.shake256.parallel.mixed.iota a rc = ok (iota a rc) := by
  mixed_ops
  rfl
end Operations

def compactRound (a : Rows) (rc : U64) : Rows := Id.run do
  let v := a.val[0]!
  let v1 := a.val[5]!
  let v2 := a.val[10]!
  let v3 := a.val[15]!
  let v4 := a.val[20]!
  let v5 := Operations.xor3 v2 v3 v4
  let v6 := Operations.xor3 v v1 v5
  let v7 := a.val[1]!
  let v8 := a.val[6]!
  let v9 := a.val[11]!
  let v10 := a.val[16]!
  let v11 := a.val[21]!
  let v12 := Operations.xor3 v9 v10 v11
  let v13 := Operations.xor3 v7 v8 v12
  let v14 := a.val[2]!
  let v15 := a.val[7]!
  let v16 := a.val[12]!
  let v17 := a.val[17]!
  let v18 := a.val[22]!
  let v19 := Operations.xor3 v16 v17 v18
  let v20 := Operations.xor3 v14 v15 v19
  let v21 := a.val[3]!
  let v22 := a.val[8]!
  let v23 := a.val[13]!
  let v24 := a.val[18]!
  let v25 := a.val[23]!
  let v26 := Operations.xor3 v23 v24 v25
  let v27 := Operations.xor3 v21 v22 v26
  let v28 := a.val[4]!
  let v29 := a.val[9]!
  let v30 := a.val[14]!
  let v31 := a.val[19]!
  let v32 := a.val[24]!
  let v33 := Operations.xor3 v30 v31 v32
  let v34 := Operations.xor3 v28 v29 v33
  let v35 := v34
  let v36 := v13
  let v37 := Operations.theta v35 v36
  let v38 := v6
  let v39 := v20
  let v40 := Operations.theta v38 v39
  let v41 := v27
  let v42 := Operations.theta v36 v41
  let v43 := Operations.theta v39 v35
  let v44 := Operations.theta v41 v38
  let v45 := v37
  let v46 := Operations.rho 0#i32 64#i32 v v45
  let v47 := v40
  let v48 := Operations.rho 44#i32 20#i32 v8 v47
  let v49 := v42
  let v50 := Operations.rho 43#i32 21#i32 v16 v49
  let v51 := v43
  let v52 := Operations.rho 21#i32 43#i32 v24 v51
  let v53 := v44
  let v54 := Operations.rho 14#i32 50#i32 v32 v53
  let v55 := Operations.rho 28#i32 36#i32 v21 v51
  let v56 := Operations.rho 20#i32 44#i32 v29 v53
  let v57 := Operations.rho 3#i32 61#i32 v2 v45
  let v58 := Operations.rho 45#i32 19#i32 v10 v47
  let v59 := Operations.rho 61#i32 3#i32 v18 v49
  let v60 := Operations.rho 1#i32 63#i32 v7 v47
  let v61 := Operations.rho 6#i32 58#i32 v15 v49
  let v62 := Operations.rho 25#i32 39#i32 v23 v51
  let v63 := Operations.rho 8#i32 56#i32 v31 v53
  let v64 := Operations.rho 18#i32 46#i32 v4 v45
  let v65 := Operations.rho 27#i32 37#i32 v28 v53
  let v66 := Operations.rho 36#i32 28#i32 v1 v45
  let v67 := Operations.rho 10#i32 54#i32 v9 v47
  let v68 := Operations.rho 15#i32 49#i32 v17 v49
  let v69 := Operations.rho 56#i32 8#i32 v25 v51
  let v70 := Operations.rho 62#i32 2#i32 v14 v49
  let v71 := Operations.rho 55#i32 9#i32 v22 v51
  let v72 := Operations.rho 39#i32 25#i32 v30 v53
  let v73 := Operations.rho 41#i32 23#i32 v3 v45
  let v74 := Operations.rho 2#i32 62#i32 v11 v47
  let v75 := v46
  let v76 := v48
  let v77 := v50
  let v78 := Operations.chi v75 v76 v77
  let v79 := v48
  let v80 := v50
  let v81 := v52
  let v82 := Operations.chi v79 v80 v81
  let v83 := v50
  let v84 := v52
  let v85 := v54
  let v86 := Operations.chi v83 v84 v85
  let v87 := v52
  let v88 := v54
  let v89 := Operations.chi v87 v88 v75
  let v90 := v54
  let v91 := v48
  let v92 := Operations.chi v90 v75 v91
  let v93 := v55
  let v94 := v56
  let v95 := v57
  let v96 := Operations.chi v93 v94 v95
  let v97 := v56
  let v98 := v57
  let v99 := v58
  let v100 := Operations.chi v97 v98 v99
  let v101 := v57
  let v102 := v58
  let v103 := v59
  let v104 := Operations.chi v101 v102 v103
  let v105 := v58
  let v106 := v59
  let v107 := Operations.chi v105 v106 v93
  let v108 := v59
  let v109 := v56
  let v110 := Operations.chi v108 v93 v109
  let v111 := v60
  let v112 := v61
  let v113 := v62
  let v114 := Operations.chi v111 v112 v113
  let v115 := v61
  let v116 := v62
  let v117 := v63
  let v118 := Operations.chi v115 v116 v117
  let v119 := v62
  let v120 := v63
  let v121 := v64
  let v122 := Operations.chi v119 v120 v121
  let v123 := v63
  let v124 := v64
  let v125 := Operations.chi v123 v124 v111
  let v126 := v64
  let v127 := v61
  let v128 := Operations.chi v126 v111 v127
  let v129 := v65
  let v130 := v66
  let v131 := v67
  let v132 := Operations.chi v129 v130 v131
  let v133 := v66
  let v134 := v67
  let v135 := v68
  let v136 := Operations.chi v133 v134 v135
  let v137 := v67
  let v138 := v68
  let v139 := v69
  let v140 := Operations.chi v137 v138 v139
  let v141 := v68
  let v142 := v69
  let v143 := Operations.chi v141 v142 v129
  let v144 := v69
  let v145 := v66
  let v146 := Operations.chi v144 v129 v145
  let v147 := v70
  let v148 := v71
  let v149 := v72
  let v150 := Operations.chi v147 v148 v149
  let v151 := v71
  let v152 := v72
  let v153 := v73
  let v154 := Operations.chi v151 v152 v153
  let v155 := v72
  let v156 := v73
  let v157 := v74
  let v158 := Operations.chi v155 v156 v157
  let v159 := v73
  let v160 := v74
  let v161 := Operations.chi v159 v160 v147
  let v162 := v74
  let v163 := v71
  let v164 := Operations.chi v162 v147 v163
  return writeRows a rc v78 v82 v86 v89 v92 v96 v100 v104 v107 v110 v114 v118 v122 v125 v128 v132 v136 v140 v143 v146 v150 v154 v158 v161 v164
end slhdsa.Kmixed
