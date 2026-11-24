module
public import Aeneas
public import Prehashdigest.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
namespace PrehashDigestRust

@[reducible]
def toSlhParams (p : params.Params) : slhdsa.params.Params :=
  ⟨p.n, p.h, p.d, p.hp, p.a, p.k, p.m⟩

@[reducible]
def shake256.shake256 (input output : Slice Std.U8) : Result (Slice Std.U8) :=
  slhdsa.shake256.shake256 input output

@[reducible]
def sha512.sha512 (msg : Slice Std.U8) : Result (Array Std.U8 64#usize) :=
  slhdsa.sha512.sha512 msg

@[reducible]
def sha256.sha256 (msg : Slice Std.U8) : Result (Array Std.U8 32#usize) :=
  slhdsa.sha256.sha256 msg

@[reducible]
def slh.slh_sign_internal {N : Std.Usize} (p : params.Params) (m sk : Slice Std.U8)
    (addrnd : Array Std.U8 N) : Result (alloc.vec.Vec Std.U8) :=
  slhdsa.slh.slh_sign_internal (toSlhParams p) m sk addrnd

@[reducible]
def shake.slh.slh_sign_internal {N : Std.Usize} (p : params.Params) (m sk : Slice Std.U8)
    (addrnd : Array Std.U8 N) : Result (alloc.vec.Vec Std.U8) :=
  slhdsa.shake.slh.slh_sign_internal (toSlhParams p) m sk addrnd

@[reducible]
def slh.slh_verify_internal (N : Std.Usize) (p : params.Params) (m sig pk : Slice Std.U8) :
    Result Bool :=
  slhdsa.slh.slh_verify_internal N (toSlhParams p) m sig pk

@[reducible]
def shake.slh.slh_verify_internal (N : Std.Usize) (p : params.Params) (m sig pk : Slice Std.U8) :
    Result Bool :=
  slhdsa.shake.slh.slh_verify_internal N (toSlhParams p) m sig pk

end PrehashDigestRust
