import Spec.ShakeWords
open Spec.Keccak
namespace PeerKeccak.SoftLinux

def round (a : State) (rc : Lane) : State :=
  let v0 := a[0]! ^^^ a[5]!
  let v1 := v0 ^^^ a[10]!
  let v2 := v1 ^^^ a[15]!
  let v3 := v2 ^^^ a[20]!
  let v4 := a[1]! ^^^ a[6]!
  let v5 := v4 ^^^ a[11]!
  let v6 := v5 ^^^ a[16]!
  let v7 := v6 ^^^ a[21]!
  let v8 := a[17]! ^^^ a[22]!
  let v9 := v8 ^^^ a[7]!
  let v10 := v9 ^^^ a[2]!
  let v11 := v10 ^^^ a[12]!
  let v12 := a[13]! ^^^ a[18]!
  let v13 := v12 ^^^ a[23]!
  let v14 := v13 ^^^ a[8]!
  let v15 := v14 ^^^ a[3]!
  let v16 := a[14]! ^^^ a[19]!
  let v17 := v16 ^^^ a[24]!
  let v18 := v17 ^^^ a[9]!
  let v19 := v18 ^^^ a[4]!
  let v20 := (v7).rotateLeft 1
  let v21 := v20 ^^^ v19
  let v22 := v21 ^^^ a[0]!
  let v23 := v21 ^^^ a[5]!
  let v24 := v21 ^^^ a[10]!
  let v25 := v21 ^^^ a[15]!
  let v26 := v21 ^^^ a[20]!
  let v27 := (v11).rotateLeft 1
  let v28 := v27 ^^^ v3
  let v29 := v28 ^^^ a[1]!
  let v30 := v28 ^^^ a[6]!
  let v31 := v28 ^^^ a[11]!
  let v32 := v28 ^^^ a[16]!
  let v33 := v28 ^^^ a[21]!
  let v34 := (v15).rotateLeft 1
  let v35 := v34 ^^^ v7
  let v36 := v35 ^^^ a[2]!
  let v37 := v35 ^^^ a[7]!
  let v38 := v35 ^^^ a[12]!
  let v39 := v35 ^^^ a[17]!
  let v40 := v35 ^^^ a[22]!
  let v41 := (v19).rotateLeft 1
  let v42 := v41 ^^^ v11
  let v43 := v42 ^^^ a[3]!
  let v44 := v42 ^^^ a[8]!
  let v45 := v42 ^^^ a[13]!
  let v46 := v42 ^^^ a[18]!
  let v47 := v42 ^^^ a[23]!
  let v48 := (v3).rotateLeft 1
  let v49 := v48 ^^^ v15
  let v50 := v49 ^^^ a[4]!
  let v51 := v49 ^^^ a[9]!
  let v52 := v49 ^^^ a[14]!
  let v53 := v49 ^^^ a[19]!
  let v54 := v49 ^^^ a[24]!
  let v55 := (v29).rotateLeft 1
  let v56 := (v24).rotateLeft 3
  let v57 := (v37).rotateLeft 6
  let v58 := (v31).rotateLeft 10
  let v59 := (v39).rotateLeft 15
  let v60 := (v46).rotateLeft 21
  let v61 := (v43).rotateLeft 28
  let v62 := (v23).rotateLeft 36
  let v63 := (v32).rotateLeft 45
  let v64 := (v44).rotateLeft 55
  let v65 := (v33).rotateLeft 2
  let v66 := (v54).rotateLeft 14
  let v67 := (v50).rotateLeft 27
  let v68 := (v25).rotateLeft 41
  let v69 := (v47).rotateLeft 56
  let v70 := (v53).rotateLeft 8
  let v71 := (v45).rotateLeft 25
  let v72 := (v38).rotateLeft 43
  let v73 := (v36).rotateLeft 62
  let v74 := (v26).rotateLeft 18
  let v75 := (v52).rotateLeft 39
  let v76 := (v40).rotateLeft 61
  let v77 := (v51).rotateLeft 20
  let v78 := (v30).rotateLeft 44
  let v79 := ~~~(v78)
  let v80 := v72 &&& v79
  let v81 := ~~~(v72)
  let v82 := v60 &&& v81
  let v83 := v82 ^^^ v78
  let v84 := ~~~(v60)
  let v85 := v66 &&& v84
  let v86 := v85 ^^^ v72
  let v87 := ~~~(v66)
  let v88 := v22 &&& v87
  let v89 := v88 ^^^ v60
  let v90 := ~~~(v22)
  let v91 := v78 &&& v90
  let v92 := v91 ^^^ v66
  let v93 := ~~~(v77)
  let v94 := v56 &&& v93
  let v95 := v94 ^^^ v61
  let v96 := ~~~(v56)
  let v97 := v63 &&& v96
  let v98 := v97 ^^^ v77
  let v99 := ~~~(v63)
  let v100 := v76 &&& v99
  let v101 := v100 ^^^ v56
  let v102 := ~~~(v76)
  let v103 := v61 &&& v102
  let v104 := v103 ^^^ v63
  let v105 := ~~~(v61)
  let v106 := v77 &&& v105
  let v107 := v106 ^^^ v76
  let v108 := ~~~(v57)
  let v109 := v71 &&& v108
  let v110 := v109 ^^^ v55
  let v111 := ~~~(v71)
  let v112 := v70 &&& v111
  let v113 := v112 ^^^ v57
  let v114 := ~~~(v70)
  let v115 := v74 &&& v114
  let v116 := v115 ^^^ v71
  let v117 := ~~~(v74)
  let v118 := v55 &&& v117
  let v119 := v118 ^^^ v70
  let v120 := ~~~(v55)
  let v121 := v57 &&& v120
  let v122 := v121 ^^^ v74
  let v123 := ~~~(v62)
  let v124 := v58 &&& v123
  let v125 := v124 ^^^ v67
  let v126 := ~~~(v58)
  let v127 := v59 &&& v126
  let v128 := v127 ^^^ v62
  let v129 := ~~~(v59)
  let v130 := v69 &&& v129
  let v131 := v130 ^^^ v58
  let v132 := ~~~(v69)
  let v133 := v67 &&& v132
  let v134 := v133 ^^^ v59
  let v135 := ~~~(v67)
  let v136 := v62 &&& v135
  let v137 := v136 ^^^ v69
  let v138 := ~~~(v64)
  let v139 := v75 &&& v138
  let v140 := v139 ^^^ v73
  let v141 := ~~~(v75)
  let v142 := v68 &&& v141
  let v143 := v142 ^^^ v64
  let v144 := ~~~(v68)
  let v145 := v65 &&& v144
  let v146 := v145 ^^^ v75
  let v147 := ~~~(v65)
  let v148 := v73 &&& v147
  let v149 := v148 ^^^ v68
  let v150 := ~~~(v73)
  let v151 := v64 &&& v150
  let v152 := v151 ^^^ v65
  let v153 := v80 ^^^ rc
  let v154 := v153 ^^^ v22
  #[v154,v83,v86,v89,v92,v95,v98,v101,v104,v107,v110,v113,v116,v119,v122,v125,v128,v131,v134,v137,v140,v143,v146,v149,v152]

def constants : Array Lane := #[
  0x0000000000000001,
  0x0000000000008082,
  0x800000000000808a,
  0x8000000080008000,
  0x000000000000808b,
  0x0000000080000001,
  0x8000000080008081,
  0x8000000000008009,
  0x000000000000008a,
  0x0000000000000088,
  0x0000000080008009,
  0x000000008000000a,
  0x000000008000808b,
  0x800000000000008b,
  0x8000000000008089,
  0x8000000000008003,
  0x8000000000008002,
  0x8000000000000080,
  0x000000000000800a,
  0x800000008000000a,
  0x8000000080008081,
  0x8000000000008080,
  0x0000000080000001,
  0x8000000080008008]

def permute (a : State) : State := constants.foldl round a
end PeerKeccak.SoftLinux
