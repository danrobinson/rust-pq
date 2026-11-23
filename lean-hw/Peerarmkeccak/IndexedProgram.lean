import Spec.ShakeWords
open Spec.Keccak
namespace PeerKeccak.Indexed

def round (a : State) (rc : Lane) : State :=
  let v0 := a[13]! ^^^ a[18]!
  let v1 := v0 ^^^ a[23]!
  let v2 := v1 ^^^ a[8]!
  let v3 := v2 ^^^ a[3]!
  let v4 := (v3).rotateLeft 1
  let v5 := a[1]! ^^^ a[6]!
  let v6 := v5 ^^^ a[11]!
  let v7 := v6 ^^^ a[16]!
  let v8 := v7 ^^^ a[21]!
  let v9 := v4 ^^^ v8
  let v10 := v9 ^^^ a[12]!
  let v11 := (v10).rotateLeft 43
  let v12 := a[17]! ^^^ a[22]!
  let v13 := v12 ^^^ a[7]!
  let v14 := v13 ^^^ a[2]!
  let v15 := v14 ^^^ a[12]!
  let v16 := (v15).rotateLeft 1
  let v17 := a[0]! ^^^ a[5]!
  let v18 := v17 ^^^ a[10]!
  let v19 := v18 ^^^ a[15]!
  let v20 := v19 ^^^ a[20]!
  let v21 := v16 ^^^ v20
  let v22 := v21 ^^^ a[6]!
  let v23 := (v22).rotateLeft 44
  let v24 := ~~~(v23)
  let v25 := v11 &&& v24
  let v26 := (v8).rotateLeft 1
  let v27 := a[14]! ^^^ a[19]!
  let v28 := v27 ^^^ a[24]!
  let v29 := v28 ^^^ a[9]!
  let v30 := v29 ^^^ a[4]!
  let v31 := v26 ^^^ v30
  let v32 := v31 ^^^ a[0]!
  let v33 := v25 ^^^ v32
  let v34 := v33 ^^^ rc
  let v35 := (v30).rotateLeft 1
  let v36 := v35 ^^^ v15
  let v37 := v36 ^^^ a[18]!
  let v38 := (v37).rotateLeft 21
  let v39 := ~~~(v11)
  let v40 := v38 &&& v39
  let v41 := v40 ^^^ v23
  let v42 := (v20).rotateLeft 1
  let v43 := v42 ^^^ v3
  let v44 := v43 ^^^ a[24]!
  let v45 := (v44).rotateLeft 14
  let v46 := ~~~(v38)
  let v47 := v45 &&& v46
  let v48 := v47 ^^^ v11
  let v49 := ~~~(v45)
  let v50 := v32 &&& v49
  let v51 := v50 ^^^ v38
  let v52 := ~~~(v32)
  let v53 := v23 &&& v52
  let v54 := v53 ^^^ v45
  let v55 := v31 ^^^ a[10]!
  let v56 := (v55).rotateLeft 3
  let v57 := v43 ^^^ a[9]!
  let v58 := (v57).rotateLeft 20
  let v59 := ~~~(v58)
  let v60 := v56 &&& v59
  let v61 := v36 ^^^ a[3]!
  let v62 := (v61).rotateLeft 28
  let v63 := v60 ^^^ v62
  let v64 := v21 ^^^ a[16]!
  let v65 := (v64).rotateLeft 45
  let v66 := ~~~(v56)
  let v67 := v65 &&& v66
  let v68 := v67 ^^^ v58
  let v69 := v9 ^^^ a[22]!
  let v70 := (v69).rotateLeft 61
  let v71 := ~~~(v65)
  let v72 := v70 &&& v71
  let v73 := v72 ^^^ v56
  let v74 := ~~~(v70)
  let v75 := v62 &&& v74
  let v76 := v75 ^^^ v65
  let v77 := ~~~(v62)
  let v78 := v58 &&& v77
  let v79 := v78 ^^^ v70
  let v80 := v36 ^^^ a[13]!
  let v81 := (v80).rotateLeft 25
  let v82 := v9 ^^^ a[7]!
  let v83 := (v82).rotateLeft 6
  let v84 := ~~~(v83)
  let v85 := v81 &&& v84
  let v86 := v21 ^^^ a[1]!
  let v87 := (v86).rotateLeft 1
  let v88 := v85 ^^^ v87
  let v89 := v43 ^^^ a[19]!
  let v90 := (v89).rotateLeft 8
  let v91 := ~~~(v81)
  let v92 := v90 &&& v91
  let v93 := v92 ^^^ v83
  let v94 := v31 ^^^ a[20]!
  let v95 := (v94).rotateLeft 18
  let v96 := ~~~(v90)
  let v97 := v95 &&& v96
  let v98 := v97 ^^^ v81
  let v99 := ~~~(v95)
  let v100 := v87 &&& v99
  let v101 := v100 ^^^ v90
  let v102 := ~~~(v87)
  let v103 := v83 &&& v102
  let v104 := v103 ^^^ v95
  let v105 := v21 ^^^ a[11]!
  let v106 := (v105).rotateLeft 10
  let v107 := v31 ^^^ a[5]!
  let v108 := (v107).rotateLeft 36
  let v109 := ~~~(v108)
  let v110 := v106 &&& v109
  let v111 := v43 ^^^ a[4]!
  let v112 := (v111).rotateLeft 27
  let v113 := v110 ^^^ v112
  let v114 := v9 ^^^ a[17]!
  let v115 := (v114).rotateLeft 15
  let v116 := ~~~(v106)
  let v117 := v115 &&& v116
  let v118 := v117 ^^^ v108
  let v119 := v36 ^^^ a[23]!
  let v120 := (v119).rotateLeft 56
  let v121 := ~~~(v115)
  let v122 := v120 &&& v121
  let v123 := v122 ^^^ v106
  let v124 := ~~~(v120)
  let v125 := v112 &&& v124
  let v126 := v125 ^^^ v115
  let v127 := ~~~(v112)
  let v128 := v108 &&& v127
  let v129 := v128 ^^^ v120
  let v130 := v43 ^^^ a[14]!
  let v131 := (v130).rotateLeft 39
  let v132 := v36 ^^^ a[8]!
  let v133 := (v132).rotateLeft 55
  let v134 := ~~~(v133)
  let v135 := v131 &&& v134
  let v136 := v9 ^^^ a[2]!
  let v137 := (v136).rotateLeft 62
  let v138 := v135 ^^^ v137
  let v139 := v31 ^^^ a[15]!
  let v140 := (v139).rotateLeft 41
  let v141 := ~~~(v131)
  let v142 := v140 &&& v141
  let v143 := v142 ^^^ v133
  let v144 := v21 ^^^ a[21]!
  let v145 := (v144).rotateLeft 2
  let v146 := ~~~(v140)
  let v147 := v145 &&& v146
  let v148 := v147 ^^^ v131
  let v149 := ~~~(v145)
  let v150 := v137 &&& v149
  let v151 := v150 ^^^ v140
  let v152 := ~~~(v137)
  let v153 := v133 &&& v152
  let v154 := v153 ^^^ v145
  #[v34,v41,v48,v51,v54,v63,v68,v73,v76,v79,v88,v93,v98,v101,v104,v113,v118,v123,v126,v129,v138,v143,v148,v151,v154]

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
end PeerKeccak.Indexed
