import Lean

/-! Simp attributes of the `Ct` library. -/

/-- Lemmas pushing `Ct.Leak.erase` through the instrumented program. -/
register_simp_attr ct_erase

/-- Constant-time lemmas `Rel (f args) (f args') R` used by `ct_step` at calls of `f`. -/
register_label_attr ct_rel
