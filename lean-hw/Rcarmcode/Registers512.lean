import Rcarmcode.Code512

namespace slhdsa.RcArmCode.S512

open Spec.SHA512 slhdsa.H512

private theorem add_comm (a b : Arm.V2) : Arm.ADD2 a b = Arm.ADD2 b a := by
  cases a; cases b; simp [Arm.ADD2, BitVec.add_comm]

private theorem finish1 (a b c : Arm.V2) :
    Arm.ADD2 b (Arm.ADD2 a c) = Arm.ADD2 (Arm.ADD2 a b) c := by
  cases a; cases b; cases c
  simp only [Arm.ADD2, Arm.V2.mk.injEq]
  constructor <;> ac_rfl

private theorem finish2 (a b c : Arm.V2) :
    Arm.ADD2 (Arm.ADD2 a c) b = Arm.ADD2 (Arm.ADD2 a b) c := by
  cases a; cases b; cases c
  simp only [Arm.ADD2, Arm.V2.mk.injEq]
  constructor <;> ac_rfl

/-- Addition is commutative. The instruction offsets below guide definitional
reduction where LLVM interchanged the input registers of an ADD instruction. -/
private def oriented (swaps : List Nat) (i : Nat) (a b : Arm.V2) :=
  if swaps.contains i then Arm.ADD2 b a else Arm.ADD2 a b

private theorem orient (swaps : List Nat) : (fun (_ : Nat) => Arm.ADD2) = oriented swaps := by
  funext i a b
  unfold oriented
  split
  · exact add_comm a b
  · rfl

theorem linux_constants : linuxConstants = K := by decide
theorem apple_constants : appleConstants = K := by decide

def reference (ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 : Arm.V2) :=
  let s := H512.kcompress ab cd ef gh [m0,m1,m2,m3,m4,m5,m6,m7]
  (Arm.ADD2 s.ab ab, Arm.ADD2 s.cd cd, Arm.ADD2 s.ef ef, Arm.ADD2 s.gh gh)

private theorem tuple_eq {a b : Arm.V2 × Arm.V2 × Arm.V2 × Arm.V2}
    (h₀ : a.1 = b.1) (h₁ : a.2.1 = b.2.1) (h₂ : a.2.2.1 = b.2.2.1)
    (h₃ : a.2.2.2 = b.2.2.2) : a = b :=
  Prod.ext h₀ (Prod.ext h₁ (Prod.ext h₂ h₃))

attribute [local irreducible] Arm.ADD2 Arm.EXT1 Arm.SHA512H Arm.SHA512H2
  Arm.SHA512SU0 Arm.SHA512SU1

set_option maxHeartbeats 400000
set_option maxRecDepth 65536

private theorem advance {s x y : H512.KState} {n : Nat}
    (before : (List.range n).foldl H512.kstep s = x) (next : H512.kstep x n = y) :
    (List.range (n+1)).foldl H512.kstep s = y := by
  simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, before] using next

private def linuxSwaps : List Nat := [9, 17, 22, 27, 31, 35, 40, 44, 48, 51, 56, 65, 66, 76, 87, 102, 111, 119, 130, 142, 157, 168, 182, 195, 206, 219, 232, 243, 256, 269, 280, 291, 302, 312, 321, 330, 339, 347, 358, 370, 382, 391, 397, 403, 410]

theorem linux_registers (ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 : Arm.V2) :
    linux (fun _ => Arm.ADD2) linuxConstants ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 =
      reference ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 := by
  rw [linux_constants, orient linuxSwaps]
  unfold linux
  extract_lets
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17
    t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35
    t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t50 t51 t52 t53
    t54 t55 t56 t57 t58 t59 t60 t61 t62 t63 t64 t65 t66 t67 t68 t69 t70 t71
    t72 t73 t74 t75 t76 t77 t78 t79 t80 t81 t82 t83 t84 t85 t86 t87 t88 t89
    t90 t91 t92 t93 t94 t95 t96 t97 t98 t99 t100 t101 t102 t103 t104 t105 t106 t107
    t108 t109 t110 t111 t112 t113 t114 t115 t116 t117 t118 t119 t120 t121 t122 t123 t124 t125
    t126 t127 t128 t129 t130 t131 t132 t133 t134 t135 t136 t137 t138 t139 t140 t141 t142 t143
    t144 t145 t146 t147 t148 t149 t150 t151 t152 t153 t154 t155 t156 t157 t158 t159 t160 t161
    t162 t163 t164 t165 t166 t167 t168 t169 t170 t171 t172 t173 t174 t175 t176 t177 t178 t179
    t180 t181 t182 t183 t184 t185 t186 t187 t188 t189 t190 t191 t192 t193 t194 t195 t196 t197
    t198 t199 t200 t201 t202 t203 t204 t205 t206 t207 t208 t209 t210 t211 t212 t213 t214 t215
    t216 t217 t218 t219 t220 t221 t222 t223 t224 t225 t226 t227 t228 t229 t230 t231 t232 t233
    t234 t235 t236 t237 t238 t239 t240 t241 t242 t243 t244 t245 t246 t247 t248 t249 t250 t251
    t252 t253 t254 t255 t256 t257 t258 t259 t260 t261 t262 t263 t264 t265 t266 t267 t268 t269
    t270 t271 t272 t273 t274 t275 t276 t277 t278 t279 t280 t281 t282 t283 t284 t285 t286 t287
    t288 t289 t290 t291 t292 t293 t294 t295 t296 t297 t298 t299 t300 t301 t302 t303 t304 t305
    t306 t307 t308 t309 t310 t311 t312 t313 t314 t315 t316 t317 t318 t319 t320 t321 t322 t323
    t324 t325 t326 t327 t328 t329 t330 t331 t332 t333 t334 t335 t336 t337 t338 t339 t340 t341
    t342 t343 t344 t345 t346 t347 t348 t349 t350 t351 t352 t353 t354 t355 t356 t357 t358 t359
    t360 t361 t362 t363 t364 t365 t366 t367 t368 t369 t370 t371 t372 t373 t374 t375 t376 t377
    t378 t379 t380 t381 t382 t383 t384 t385 t386 t387 t388 t389 t390 t391 t392 t393 t394 t395
    t396 t397 t398 t399 t400 t401 t402 t403 t404 t405 t406 t407 t408 t409 t410 t411 t412 t413
    t414 t415 t416 t417 t418 t419
  let initial : H512.KState := ⟨ab, cd, ef, gh, [m0,m1,m2,m3,m4,m5,m6,m7]⟩
  have h0 : (List.range 0).foldl H512.kstep initial = initial := rfl
  have h1 := advance h0 (y := ⟨t10, ab, t9, ef, [t61, m1, m2, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h2 := advance h1 (y := ⟨t19, t10, t17, t9, [t61, t68, m2, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h3 := advance h2 (y := ⟨t28, t19, t27, t17, [t61, t68, t84, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h4 := advance h3 (y := ⟨t37, t28, t35, t27, [t61, t68, t84, t94, m4, m5, m6, m7]⟩) (by rfl)
  have h5 := advance h4 (y := ⟨t45, t37, t44, t35, [t61, t68, t84, t94, t99, m5, m6, m7]⟩) (by rfl)
  have h6 := advance h5 (y := ⟨t53, t45, t51, t44, [t61, t68, t84, t94, t99, t109, m6, m7]⟩) (by rfl)
  have h7 := advance h6 (y := ⟨t67, t53, t66, t51, [t61, t68, t84, t94, t99, t109, t128, m7]⟩) (by rfl)
  have h8 := advance h7 (y := ⟨t78, t67, t76, t66, [t61, t68, t84, t94, t99, t109, t128, t138]⟩) (by rfl)
  have h9 := advance h8 (y := ⟨t88, t78, t87, t76, [t149, t68, t84, t94, t99, t109, t128, t138]⟩) (by rfl)
  have h10 := advance h9 (y := ⟨t103, t88, t102, t87, [t149, t154, t84, t94, t99, t109, t128, t138]⟩) (by rfl)
  have h11 := advance h10 (y := ⟨t112, t103, t111, t102, [t149, t154, t164, t94, t99, t109, t128, t138]⟩) (by rfl)
  have h12 := advance h11 (y := ⟨t123, t112, t119, t111, [t149, t154, t164, t170, t99, t109, t128, t138]⟩) (by rfl)
  have h13 := advance h12 (y := ⟨t131, t123, t130, t119, [t149, t154, t164, t170, t179, t109, t128, t138]⟩) (by rfl)
  have h14 := advance h13 (y := ⟨t143, t131, t142, t130, [t149, t154, t164, t170, t179, t187, t128, t138]⟩) (by rfl)
  have h15 := advance h14 (y := ⟨t158, t143, t157, t142, [t149, t154, t164, t170, t179, t187, t193, t138]⟩) (by rfl)
  have h16 := advance h15 (y := ⟨t169, t158, t168, t157, [t149, t154, t164, t170, t179, t187, t193, t203]⟩) (by rfl)
  have h17 := advance h16 (y := ⟨t183, t169, t182, t168, [t208, t154, t164, t170, t179, t187, t193, t203]⟩) (by rfl)
  have h18 := advance h17 (y := ⟨t196, t183, t195, t182, [t208, t217, t164, t170, t179, t187, t193, t203]⟩) (by rfl)
  have h19 := advance h18 (y := ⟨t207, t196, t206, t195, [t208, t217, t224, t170, t179, t187, t193, t203]⟩) (by rfl)
  have h20 := advance h19 (y := ⟨t220, t207, t219, t206, [t208, t217, t224, t230, t179, t187, t193, t203]⟩) (by rfl)
  have h21 := advance h20 (y := ⟨t233, t220, t232, t219, [t208, t217, t224, t230, t240, t187, t193, t203]⟩) (by rfl)
  have h22 := advance h21 (y := ⟨t244, t233, t243, t232, [t208, t217, t224, t230, t240, t245, t193, t203]⟩) (by rfl)
  have h23 := advance h22 (y := ⟨t257, t244, t256, t243, [t208, t217, t224, t230, t240, t245, t254, t203]⟩) (by rfl)
  have h24 := advance h23 (y := ⟨t270, t257, t269, t256, [t208, t217, t224, t230, t240, t245, t254, t261]⟩) (by rfl)
  have h25 := advance h24 (y := ⟨t281, t270, t280, t269, [t267, t217, t224, t230, t240, t245, t254, t261]⟩) (by rfl)
  have h26 := advance h25 (y := ⟨t292, t281, t291, t280, [t267, t278, t224, t230, t240, t245, t254, t261]⟩) (by rfl)
  have h27 := advance h26 (y := ⟨t303, t292, t302, t291, [t267, t278, t289, t230, t240, t245, t254, t261]⟩) (by rfl)
  have h28 := advance h27 (y := ⟨t313, t303, t312, t302, [t267, t278, t289, t300, t240, t245, t254, t261]⟩) (by rfl)
  have h29 := advance h28 (y := ⟨t322, t313, t321, t312, [t267, t278, t289, t300, t311, t245, t254, t261]⟩) (by rfl)
  have h30 := advance h29 (y := ⟨t331, t322, t330, t321, [t267, t278, t289, t300, t311, t354, t254, t261]⟩) (by rfl)
  have h31 := advance h30 (y := ⟨t340, t331, t339, t330, [t267, t278, t289, t300, t311, t354, t366, t261]⟩) (by rfl)
  have h32 := advance h31 (y := ⟨t348, t340, t347, t339, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h33 := advance h32 (y := ⟨t359, t348, t358, t347, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h34 := advance h33 (y := ⟨t371, t359, t370, t358, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h35 := advance h34 (y := ⟨t383, t371, t382, t370, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h36 := advance h35 (y := ⟨t392, t383, t391, t382, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h37 := advance h36 (y := ⟨t398, t392, t397, t391, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h38 := advance h37 (y := ⟨t404, t398, t403, t397, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h39 := advance h38 (y := ⟨t411, t404, t410, t403, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  have h40 := advance h39 (y := ⟨t418, t411, (Arm.ADD2 t404 t415), t410, [t267, t278, t289, t300, t311, t354, t366, t378]⟩) (by rfl)
  unfold reference H512.kcompress
  rw [show (List.range 40).foldl H512.kstep initial = _ from h40]
  apply tuple_eq
  · rfl
  · rfl
  · apply finish1
  · rfl

private def appleSwaps : List Nat := [6, 14, 17, 22, 26, 30, 33, 38, 42, 46, 50, 54, 58, 62, 73, 84, 95, 106, 117, 128, 142, 150, 161, 172, 183, 194, 205, 216, 230, 238, 249, 260, 271, 282, 293, 304, 318, 326, 337, 348, 359, 370, 382, 397, 406]

theorem apple_registers (ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 : Arm.V2) :
    apple (fun _ => Arm.ADD2) appleConstants ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 =
      reference ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 := by
  rw [apple_constants, orient appleSwaps]
  unfold apple
  extract_lets
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17
    t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35
    t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t50 t51 t52 t53
    t54 t55 t56 t57 t58 t59 t60 t61 t62 t63 t64 t65 t66 t67 t68 t69 t70 t71
    t72 t73 t74 t75 t76 t77 t78 t79 t80 t81 t82 t83 t84 t85 t86 t87 t88 t89
    t90 t91 t92 t93 t94 t95 t96 t97 t98 t99 t100 t101 t102 t103 t104 t105 t106 t107
    t108 t109 t110 t111 t112 t113 t114 t115 t116 t117 t118 t119 t120 t121 t122 t123 t124 t125
    t126 t127 t128 t129 t130 t131 t132 t133 t134 t135 t136 t137 t138 t139 t140 t141 t142 t143
    t144 t145 t146 t147 t148 t149 t150 t151 t152 t153 t154 t155 t156 t157 t158 t159 t160 t161
    t162 t163 t164 t165 t166 t167 t168 t169 t170 t171 t172 t173 t174 t175 t176 t177 t178 t179
    t180 t181 t182 t183 t184 t185 t186 t187 t188 t189 t190 t191 t192 t193 t194 t195 t196 t197
    t198 t199 t200 t201 t202 t203 t204 t205 t206 t207 t208 t209 t210 t211 t212 t213 t214 t215
    t216 t217 t218 t219 t220 t221 t222 t223 t224 t225 t226 t227 t228 t229 t230 t231 t232 t233
    t234 t235 t236 t237 t238 t239 t240 t241 t242 t243 t244 t245 t246 t247 t248 t249 t250 t251
    t252 t253 t254 t255 t256 t257 t258 t259 t260 t261 t262 t263 t264 t265 t266 t267 t268 t269
    t270 t271 t272 t273 t274 t275 t276 t277 t278 t279 t280 t281 t282 t283 t284 t285 t286 t287
    t288 t289 t290 t291 t292 t293 t294 t295 t296 t297 t298 t299 t300 t301 t302 t303 t304 t305
    t306 t307 t308 t309 t310 t311 t312 t313 t314 t315 t316 t317 t318 t319 t320 t321 t322 t323
    t324 t325 t326 t327 t328 t329 t330 t331 t332 t333 t334 t335 t336 t337 t338 t339 t340 t341
    t342 t343 t344 t345 t346 t347 t348 t349 t350 t351 t352 t353 t354 t355 t356 t357 t358 t359
    t360 t361 t362 t363 t364 t365 t366 t367 t368 t369 t370 t371 t372 t373 t374 t375 t376 t377
    t378 t379 t380 t381 t382 t383 t384 t385 t386 t387 t388 t389 t390 t391 t392 t393 t394 t395
    t396 t397 t398 t399 t400 t401 t402 t403 t404 t405 t406 t407 t408 t409 t410 t411 t412 t413
    t414 t415 t416 t417 t418 t419
  let initial : H512.KState := ⟨ab, cd, ef, gh, [m0,m1,m2,m3,m4,m5,m6,m7]⟩
  have h0 : (List.range 0).foldl H512.kstep initial = initial := rfl
  have h1 := advance h0 (y := ⟨t12, ab, t6, ef, [t66, m1, m2, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h2 := advance h1 (y := ⟨t18, t12, t14, t6, [t66, t77, m2, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h3 := advance h2 (y := ⟨t23, t18, t22, t14, [t66, t77, t88, m3, m4, m5, m6, m7]⟩) (by rfl)
  have h4 := advance h3 (y := ⟨t34, t23, t30, t22, [t66, t77, t88, t99, m4, m5, m6, m7]⟩) (by rfl)
  have h5 := advance h4 (y := ⟨t39, t34, t38, t30, [t66, t77, t88, t99, t110, m5, m6, m7]⟩) (by rfl)
  have h6 := advance h5 (y := ⟨t49, t39, t46, t38, [t66, t77, t88, t99, t110, t121, m6, m7]⟩) (by rfl)
  have h7 := advance h6 (y := ⟨t55, t49, t54, t46, [t66, t77, t88, t99, t110, t121, t131, m7]⟩) (by rfl)
  have h8 := advance h7 (y := ⟨t65, t55, t62, t54, [t66, t77, t88, t99, t110, t121, t131, t134]⟩) (by rfl)
  have h9 := advance h8 (y := ⟨t76, t65, t73, t62, [t153, t77, t88, t99, t110, t121, t131, t134]⟩) (by rfl)
  have h10 := advance h9 (y := ⟨t87, t76, t84, t73, [t153, t164, t88, t99, t110, t121, t131, t134]⟩) (by rfl)
  have h11 := advance h10 (y := ⟨t98, t87, t95, t84, [t153, t164, t175, t99, t110, t121, t131, t134]⟩) (by rfl)
  have h12 := advance h11 (y := ⟨t109, t98, t106, t95, [t153, t164, t175, t186, t110, t121, t131, t134]⟩) (by rfl)
  have h13 := advance h12 (y := ⟨t120, t109, t117, t106, [t153, t164, t175, t186, t197, t121, t131, t134]⟩) (by rfl)
  have h14 := advance h13 (y := ⟨t137, t120, t128, t117, [t153, t164, t175, t186, t197, t208, t131, t134]⟩) (by rfl)
  have h15 := advance h14 (y := ⟨t143, t137, t142, t128, [t153, t164, t175, t186, t197, t208, t219, t134]⟩) (by rfl)
  have h16 := advance h15 (y := ⟨t154, t143, t150, t142, [t153, t164, t175, t186, t197, t208, t219, t222]⟩) (by rfl)
  have h17 := advance h16 (y := ⟨t165, t154, t161, t150, [t241, t164, t175, t186, t197, t208, t219, t222]⟩) (by rfl)
  have h18 := advance h17 (y := ⟨t176, t165, t172, t161, [t241, t252, t175, t186, t197, t208, t219, t222]⟩) (by rfl)
  have h19 := advance h18 (y := ⟨t187, t176, t183, t172, [t241, t252, t263, t186, t197, t208, t219, t222]⟩) (by rfl)
  have h20 := advance h19 (y := ⟨t198, t187, t194, t183, [t241, t252, t263, t274, t197, t208, t219, t222]⟩) (by rfl)
  have h21 := advance h20 (y := ⟨t209, t198, t205, t194, [t241, t252, t263, t274, t285, t208, t219, t222]⟩) (by rfl)
  have h22 := advance h21 (y := ⟨t226, t209, t216, t205, [t241, t252, t263, t274, t285, t296, t219, t222]⟩) (by rfl)
  have h23 := advance h22 (y := ⟨t232, t226, t230, t216, [t241, t252, t263, t274, t285, t296, t307, t222]⟩) (by rfl)
  have h24 := advance h23 (y := ⟨t243, t232, t238, t230, [t241, t252, t263, t274, t285, t296, t307, t311]⟩) (by rfl)
  have h25 := advance h24 (y := ⟨t254, t243, t249, t238, [t329, t252, t263, t274, t285, t296, t307, t311]⟩) (by rfl)
  have h26 := advance h25 (y := ⟨t265, t254, t260, t249, [t329, t340, t263, t274, t285, t296, t307, t311]⟩) (by rfl)
  have h27 := advance h26 (y := ⟨t276, t265, t271, t260, [t329, t340, t351, t274, t285, t296, t307, t311]⟩) (by rfl)
  have h28 := advance h27 (y := ⟨t287, t276, t282, t271, [t329, t340, t351, t362, t285, t296, t307, t311]⟩) (by rfl)
  have h29 := advance h28 (y := ⟨t298, t287, t293, t282, [t329, t340, t351, t362, t373, t296, t307, t311]⟩) (by rfl)
  have h30 := advance h29 (y := ⟨t309, t298, t304, t293, [t329, t340, t351, t362, t373, t384, t307, t311]⟩) (by rfl)
  have h31 := advance h30 (y := ⟨t321, t309, t318, t304, [t329, t340, t351, t362, t373, t384, t393, t311]⟩) (by rfl)
  have h32 := advance h31 (y := ⟨t332, t321, t326, t318, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h33 := advance h32 (y := ⟨t343, t332, t337, t326, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h34 := advance h33 (y := ⟨t354, t343, t348, t337, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h35 := advance h34 (y := ⟨t365, t354, t359, t348, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h36 := advance h35 (y := ⟨t376, t365, t370, t359, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h37 := advance h36 (y := ⟨t394, t376, t382, t370, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h38 := advance h37 (y := ⟨t398, t394, t397, t382, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h39 := advance h38 (y := ⟨t413, t398, t406, t397, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  have h40 := advance h39 (y := ⟨t416, t413, (Arm.ADD2 t398 t412), t406, [t329, t340, t351, t362, t373, t384, t393, t399]⟩) (by rfl)
  unfold reference H512.kcompress
  rw [show (List.range 40).foldl H512.kstep initial = _ from h40]
  apply tuple_eq
  · rfl
  · rfl
  · apply finish2
  · rfl

end slhdsa.RcArmCode.S512
