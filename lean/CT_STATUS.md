# Constant time: what is proved (2026-11-21)

For both builds of the crate, the Lean library [Ct](Ct) proves that what key
generation and signing reveal through branches and memory accesses is either
nothing or computable from public data. Build it with
`cd lean && lake build Ct` (default build) and `cd lean-hw && lake build Ct`
(`hw-sha2`); [Ct/Theorems.lean](Ct/Theorems.lean), one file for both, holds
the statements and prints their axioms (the three standard ones).

## What is secret and what is public

- **Secret:** SK.seed, SK.prf, the signing randomness `addrnd`, and everything
  derived from them before publication (WOTS+ and FORS secret values, chain
  values below the signed digit).
- **Public:** PK.seed, PK.root, the message, the context, the signature, and
  so everything a verifier recomputes from them: the randomizer R, the digest
  and its indices, the FORS public key, every XMSS root, hence every WOTS+
  digit.

Signing cannot have a trace that is independent of the key given its public
*inputs* alone: R and the chain lengths depend on the key and are then
published. The property that can hold, and is proved, is that the trace is
determined by the public key, the message, the context and the signature.

## The model

A run of a function produces, besides its result, a list of events
([Ct/Leak.lean](Ct/Leak.lean), [Ct/Model.lean](Ct/Model.lean)):

- the outcome of every `if`, and so of every loop test;
- for every array, slice or vector element access: the index and the length;
- for every sub-slice: its bounds and the length;
- for every `copy_from_slice`, `push` and `extend_from_slice`: the lengths;
- for every comparison of two arrays: how long their common prefix is;
- for every division and remainder: both operands;
- for a `match` on an optional value: whether it is present.

Not recorded: the operands of addition, subtraction, multiplication and bit
operations, and shift amounts (every shift amount in the code is a public
height or counter). A run that fails has no trace; the functional theorems
show that runs do not fail.

The instrumented program is not written by hand. [Ct/Funs.lean](Ct/Funs.lean)
is the text of the verified translation, `Slhdsa/Funs.lean`, copied verbatim by
`scripts/ct-gen.sh` and elaborated where the primitives it names are the
instrumented ones. Two things tie it to the verified program:

- [Ct/Check.lean](Ct/Check.lean) inspects all resulting definitions (221 in
  the default build, 261 with `hw-sha2`) and rejects any that reaches a
  primitive that is neither instrumented nor on a short list of ones that
  leak nothing in this model.
- [Ct/Erase.lean](Ct/Erase.lean) proves, for each function and constant (190
  and 226), that dropping the trace gives exactly the verified function.

## The `hw-sha2` build

[lean-hw/Ct](../lean-hw/Ct) is the same library over that build's translation.
Every file that does not depend on the build is shared; what is specific is
the instrumented copy, the lemmas for the two functions whose bodies differ
(`sha256::compress`, `hash::chain_blocks`), the lemmas for the hardware
kernels, and a leakage model of the eighteen intrinsic wrappers
([lean-hw/Ct/ModelBuild.lean](../lean-hw/Ct/ModelBuild.lean)):

- the wrappers that load from or store to a caller's slice record the range
  they touch and the slice's length;
- the feature test records nothing itself (the `if` on its answer is a branch
  like any other; whether the processor has the instructions is public);
- **the register-only wrappers record nothing. This is an assumption about the
  processor**: they are fixed-latency vector and SHA-256 instructions, which
  Arm lists as taking time independent of their operands when its
  data-independent-timing mode is on. The crate does not switch that mode on.

The four-lane kernel's control flow has two inputs besides lengths: the step
ranges, which are public, and a cache keyed on the first 16 bytes of a block.
Those bytes are part of the hash address. The lemma about `chain_blocks`
therefore requires the two runs' blocks to agree on their first 16 bytes
(the value bytes are free), and the proofs of the callers show that every
block that reaches it is built from a public address.

## The theorems

- **Key generation leaks nothing** (`keygen_ct`, `keygen_trace`, and the same
  for `slh_keygen_internal`): any two runs, whatever their seeds, return with
  the same trace.
- **Signing leaks only what the signature shows** (`sign_simulated`,
  `sign_deterministic_simulated`, `slh_sign_simulated`,
  `slh_sign_internal_simulated`, and the four `…_checked_simulated`): if a
  signer returns a signature with trace `t`, then a simulator returns with
  the same trace `t`. The simulator ([Ct/Sign.lean](Ct/Sign.lean),
  `slhdsa_leak.Sim`) is given only the public key, the message, the context
  and that signature. It runs the signer's steps with zeros in place of the
  seeds and the randomness, and with each value the signer derives from
  secrets replaced by what a verifier recomputes from the signature.
  The statement is put this way, and not as "two runs with equal public
  outputs have equal traces", because two runs with the same public key and
  signature have practically the same key, which would make the two-run
  statement nearly empty. `sign_two_runs` is that weaker statement, as a
  corollary.
- **A context longer than 255 bytes** (`sign_long_context`): the trace is one
  branch.
- **Verification** (`verify_ct`): all of its inputs are public.

The only hypothesis is the message-length bound of the functional theorems.

## What this does not cover

- **The compiler.** The statement is about the Rust source as Aeneas
  translates it. Nothing proves that rustc and LLVM preserve it, and Rust's
  own documentation says the language has no mechanism that guarantees
  constant-time code. This code only copies and hashes its secrets; it has no
  secret-dependent selection or arithmetic of the kind compilers are known to
  turn into branches.
- **The processor.** That an instruction takes the same time whatever its
  operands is a property of the processor, on Arm only promised in its
  data-independent-timing mode, which the application has to switch on.
  Speculative execution, prefetchers, frequency scaling, power and
  electromagnetic emanation are outside the model.
- **Faults.** See the checked signer in the README. When a checked signer
  returns nothing because a recomputation disagreed, its trace shows how many
  leading bytes of the two roots agreed; no claim is made about such runs.
- **The adapter** in `compat/`: its glue is not translated.
- **Erasure of secrets from memory**: tested in `compat/`, not modelled here.

## What is trusted, beyond the functional proof's trust base

`Ct/Model.lean` (which primitive emits what), `Ct/Do.lean` (the elaborator
that turns each `if` of the program text into a recorded branch), the list of
non-leaking operations in `Ct/Check.lean`, and that `scripts/ct-gen.sh`
copies the program text unchanged (it checks this itself).

## Binary-level evidence

`rust/ct-evidence` compares execution traces of the compiled crate under an
emulator and runs timing tests. Its recorded results are for the crate as it
was on 2026-11-20, before the hashing was restructured.
