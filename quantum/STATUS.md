# SLH-DSA quantum security proofs

## SHAKE benchmark

Lean checks the following bounds on strong and existential forgery for the pure byte API. Each row allows at most `2^40` coherent public queries and one classical signing query. The signed and forged messages may each use up to 65,536 encoded bytes, including the context and two framing bytes.

| SHAKE sets | Shared ideal byte XOF | Shared ideal permutation, two-way quantum access | Ideal endpoint of the permutation simulator |
|---|---:|---:|---:|
| 128s, 128f | `2^-39` | `2^-19 + 2^-25` | `2^-9` |
| 192s, 192f | `2^-103` | `2^-51 + 2^-25` | `2^-73` |
| 256s, 256f | `2^-167` | `2^-83 + 2^-25` | `2^-137` |

The simulator column charges up to 30,944 raw XOF calls per public permutation query and a further `2^40` calls for the signature reductions. The shared ideal permutation column comes from a direct signature reduction. The signer and verifier use the same uniformly sampled 1,600-bit permutation that the forger can query in both directions. Applying its numerical bound to the fixed Keccak-f[1600] permutation requires a cryptographic assumption. [Shared-XOF signature theorem](Integration/SlhDsaShakeSetPrecision.lean) · [Quantum permutation signature theorem](Integration/SlhDsaShakePermutationLongBenchmark.lean) · [Ideal endpoint](Integration/SlhDsaShakePermutationIdealEndpoint.lean)

For a classical forger with the same public and signing budgets, Lean checks the actual two-way ideal permutation signature game. Its strong and existential forgery bounds are the direct XOF bounds in the table plus `2^-427`, for each of the six sets. The comparison permits adaptive forward and inverse permutation queries. [Classical byte signature theorem](Integration/SlhDsaShakePermutationClassicalSignature.lean) · [Permutation comparison](Integration/SlhDsaShakePermutationClassicalCrossing.lean)

The two-way quantum permutation proof bounds all twelve terms in the signature reduction. Replacing the secret-key PRF costs at most `2^-42` and replacing the message PRF costs at most `2^-40` plus `2^-19`, `2^-51`, or `2^-83` according to node width. Each of the one-node and two-node target-collision terms and the FORS target-collision term is at most `2^-38`, including the cost of the honest calls. The FORS decisional second-preimage term adds at most `2^-31`. The WOTS+ undetectability, preimage and chain target-collision terms contribute individual bounds of `2^-35`, `2^-37` and `2^-38`, respectively, before applying the coefficients in the signature reduction. The message-hash term is at most `2^-81`. The target-collision terms for the WOTS+ public key and FORS roots each contribute at most `2^-27`. The proof conditions the quantum search on the private table entries read during adaptive classical target selection. After applying the reduction coefficients and cancelling the distinguishing baselines, `Reduction.ShakePermutation.Long.signature_benchmark_width` gives the shared ideal permutation bound in the table. [Combined signature bound](Integration/SlhDsaShakePermutationLongBenchmark.lean) · [Conditioned quantum search](Integration/SlhDsaShakePermutationLongTargetEndpoint.lean) · [PRF replacements](Integration/SlhDsaShakePermutationMsgSecondHybrid.lean) · [One- and two-node target collisions](Integration/SlhDsaShakePermutationSparseSignature.lean) · [FORS target collisions](Integration/SlhDsaShakePermutationForsSignature.lean) · [FORS decisional second preimages](Integration/SlhDsaShakePermutationDsprSignature.lean) · [WOTS+ undetectability](Integration/SlhDsaShakePermutationWotsUdSignature.lean) · [WOTS+ preimages](Integration/SlhDsaShakePermutationWotsPreSignature.lean) · [WOTS+ chain collisions](Integration/SlhDsaShakePermutationWotsChainSignature.lean)

For the shared ideal Keccak permutation, the forward and inverse public query circuits and the honest signature query budget have been checked. A separate analysis of the permutation simulator shows that a recorded hash value can occupy a different capacity in each quantum branch. Moving the value to its common input path before or after local mask compression gives an output amplitude difference above `1/2`, even on a good database with one recorded value in each bank. This witness concerns the order of two internal simulator operations. The direct signature proof uses the twelve game bounds above. [Public port](Integration/SlhDsaShakePermutationPortMatrix.lean) · [Honest query budget](Integration/SlhDsaShakePermutationHonestBudget.lean) · [Checked witness](Integration/SlhDsaShakePermutationRelabelCorrelation.lean)

The real game uses the same capped byte inputs and the full two-way public permutation. A separate estimate bounds the mean squared state distance by `2^-430` when one uniformly hidden capacity is programmed during `2^40` coherent queries. Applying this estimate requires proving that the location is hidden from the incoming state. [Simulator signature bound](Integration/SlhDsaShakePermutationIdealEndpoint.lean) · [Real signature game](Integration/SlhDsaShakePermutationHonestGame.lean) · [Hidden-capacity estimate](Integration/SlhDsaShakePermutationHiddenQueries.lean)

## SHAKE work and repeated signing

With one signing query in the shared ideal XOF model, both forgery probabilities are strictly below one half through `2^59`, `2^91`, and `2^123` public quantum queries for the 128-, 192-, and 256-bit parameter families, respectively. These thresholds count public oracle queries. A comparison with AES under FIPS 205 also requires a computational cost model for the two primitives. [Query threshold](Integration/SlhDsaShakeAdaptiveSignature.lean) · [FIPS 205, §11](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf)

The repeated-signing theorem takes independent public and signing-query budgets. With two signing queries, `2^40` public queries, and up to 65,536 encoded bytes per message, Lean checks the following bounds for both forgery games. The classical two-way permutation bound adds `2^-427` to each entry. The two-way quantum permutation result in the first table covers one signing query. [Shared-XOF signature theorem](Integration/SlhDsaShakeXofRepeatedSignature.lean) · [Two-signature bounds](Integration/SlhDsaShakeXofRepeatedBenchmark.lean) · [Classical permutation transfer](Integration/SlhDsaShakePermutationClassicalSignature.lean)

| Shared ideal XOF, two signatures | Small signatures (s) | Fast signing (f) |
|---|---:|---:|
| SHAKE-128 | `2^-10` | `2^-12` |
| SHAKE-192 | `2^-49` | `2^-46` |
| SHAKE-256 | `2^-73` | `2^-72` |

A successful forgery can draw different FORS coordinates from different signed targets. The proof counts the subsets of coordinates that must agree with a single target. At `2^64` signing queries this estimate reaches at least one for every set, even at zero public queries. For the 128-bit sets, charging the signer's hash calls at the public quantum query rate also makes the original secret-key PRF estimate reach one. The adaptive proof and mixed-query PRF results below improve these estimates. [Subset proof](Integration/SlhDsaShakeCoverSubset.lean) · [Lifetime inequalities](Integration/SlhDsaShakeXofRepeatedBenchmark.lean)

With up to `2^64` independent uniform target digests, the probability that they cover a fresh uniform digest is at most `2^-133`, `2^-128`, `2^-193`, `2^-194`, `2^-255`, and `2^-255` in the order 128s, 128f, 192s, 192f, 256s, 256f. The certificate bounds the binomial occupancy moments using a sum of only `k+1` terms. A security proof for adaptive quantum signing must also bound the effect of choosing messages after prior signatures and coherent oracle queries. [Lifetime FORS coverage](Integration/SlhDsaForsLifetime.lean)

Lean transfers the pinned VCVio dependency’s classical full-lifetime result to its deterministic pure SHAKE-128s game with encoded public and secret keys. Key encoding preserves the law of the experiment, including the work counters. At up to `2^64` signing requests it bounds strong forgery by `q / 2^127`, where `q` counts signing requests, the adversary’s classical hash queries, and verification hash calls. All parties use one ideal random oracle. The game uses the reference signer under an ideal random oracle. The Rust implementation uses fixed Keccak-f[1600]. [Byte-key lifetime theorem](Integration/SlhDsaShakeClassicalLifetime.lean) · [Reference theorem at the pinned revision](https://github.com/Verified-zkEVM/VCVio/blob/a10530a59390442437f3c69db11015c4dd437839/HashSig/SLHDSA/SHAKE128s/Statement/Theorems/StrongUnforgeability.lean)

For the fixed SHAKE functions used by the pure byte API, Lean reduces quantum EUF-CMA and SUF-CMA to the component hash games on those same functions. Concrete numerical strength requires estimates of those component advantages at the attacker's computational cost. The Rust correspondence identifies the extracted key generator, signer and verifier with the byte operations in this scheme. [Fixed-function security reduction](Integration/SlhDsaShakeFixedQuantum.lean) · [Rust operation correspondence](../security/ME2E/ShakeRust.lean)

### Adaptive signing and key lifetimes

The quantum byte-signature game now keeps the signing requests in their original order. The forger can choose the next message after receiving earlier signatures and querying the same ideal XOF in superposition. The proof embeds the bounded, encoded message-digest inputs in the raw XOF table. It preserves reads at those inputs by every other hash operation. The resulting bound includes the honest work of key generation, signing and final verification. It covers ordinary and strong forgery, with up to 65,536 encoded bytes in each signed or forged message. [Adaptive digest game](Integration/SlhDsaShakeAdaptiveItsr.lean) · [Shared-XOF signature proof](Integration/SlhDsaShakeAdaptiveSignature.lean)

| Pure SHAKE set | Classical direct hash queries with success below ½ at up to 2^64 signatures | Quantum signing budget at 2^40 public XOF queries | Quantum forgery probability at that budget |
|---|---:|---:|---:|
| 128s | 2^125 | 2^27 | ≤ 1/4 |
| 128f | 2^124 | 2^30 | ≤ 1/4 |
| 192s | 2^189 | 2^48 | ≤ 1/4 |
| 192f | 2^189 | 2^51 | ≤ 1/2 |
| 256s | 2^252 | 2^64 | ≤ 2^-19 |
| 256f | 2^252 | 2^64 | ≤ 2^-25 |

The classical column uses the pinned VCVio wire algorithm, a fixed valid pure-mode context, a uniform public seed and one random oracle with the output width of the profile. Both deterministic and hedged signing are covered. With up to `2^64` direct hash queries and `2^64` signing requests, strong forgery has probability at most `2^-62` for the 128 sets, `2^-126` for the 192 sets, and `2^-189` (deterministic) or `2^-190` (hedged) for the 256 sets. [Classical theorem and exact rational certificates](Integration/SlhDsaShakeClassicalProfiles.lean)

With up to `2^20` signing requests, quantum forgery in the shared XOF game stays strictly below one half through `2^52`, `2^84`, and `2^116` public queries for the respective widths. With up to `2^64` signing requests and `2^94` public queries, success is at most one third for both 256-bit sets. At a full lifetime the adaptive randomizer-programming estimate for the four narrower sets already reaches one from the reduction's honest digest work alone. This puts a precise limit on the present proof. The two keyed PRF games now charge coherent and classical reads separately. With `2^40` public quantum queries and `2^64` signatures, each real acceptance probability is at most its ideal counterpart plus `2^-41`, `2^-43`, `2^-105`, `2^-107`, `2^-169`, or `2^-171` in table order. The mixed-query composition includes both improvements in the signature bound. [Signature bounds](Integration/SlhDsaShakeAdaptiveSignature.lean) · [Programming estimate](Integration/SlhDsaShakeLifetimeCertificate.lean) · [Secret-address PRF](Integration/SlhDsaShakeXofSkLifetime.lean) · [Message PRF](Integration/SlhDsaShakeXofMsgLifetime.lean) · [Mixed-query signature theorem](Integration/SlhDsaShakeMixedSignature.lean)

For SHAKE-192, Lean also checks an intermediate estimate that charges only coherent public queries for changing the salt rows. At `2^64` signatures the probability of an exceptional salt tape is at most `2^-64`. On all other tapes the honest key-generation and signing evaluations agree under the two tables. Applying the estimate to the complete signature experiment still requires showing that its compiled adversary and simulator have equal winning probabilities under both oracle schedules, including the schedule that changes after each target response. The current compiler proves equivalence for fixed tables. If the simulation obligation is discharged, the checked arithmetic gives bounds of `2^-13` and `2^-21` for 192s and 192f at `2^40` public queries. [Split-query theorem and simulation premise](Integration/SlhDsaItsrSplitHybrid.lean) · [Honest evaluations](Integration/SlhDsaShakeHonestIssued.lean) · [Simulator and compiler](Integration/SlhDsaShakeItsrPhaseMachine.lean) · [Numerical certificate](Integration/SlhDsaShakePhaseCertificate.lean)

The four-independent-component model attains the same quantum checkpoints. For a classical forger with forward and inverse access to a shared ideal Keccak permutation, the permutation comparison adds at most `2^-395`, `2^-398`, `2^-352`, `2^-354`, `2^-320`, or `2^-326` in row order at the table's signing budgets. The additional loss at the `2^94`-query full-lifetime checkpoint for the two widest sets is at most `2^-319`. [Independent components](Integration/SlhDsaSetLifetime.lean) · [Classical ideal permutation](Integration/SlhDsaShakePermutationClassicalLifetime.lean)

For SHAKE-256f the probability that `2^64` independent uniform encoded target digests cover a fresh independent digest lies strictly above `2^-256` and at most `2^-255`. Thus 255 is the largest valid integer exponent for this particular coverage probability. An adversary's probability of producing a valid signature is a different event. [Lower bound on the encoded distribution](Integration/SlhDsaForsCoverageFloor.lean) · [Upper bound](Integration/SlhDsaForsLifetime.lean)

For all twelve pure parameter sets with the fixed SHA-2 or SHAKE functions, a quantum forger that succeeds with probability at least one half yields a reduction machine with advantage at least `1/54` in one of twelve named hash games. The twelve terms and their coefficients are explicit. The coefficients sum to 27 because the Winternitz parameter is 16. This gives a concrete target for cryptanalysis of the fixed primitives. Assessing computational cost still requires charging the reduction's work. [Fixed-function witnesses](Integration/SlhDsaFixedPrimitiveWitness.lean)

The forward implication also holds for every pure SHA-2 and SHAKE parameter set. Fix a quantum forger with adaptive classical signing requests. If every primitive adversary constructed from it has advantage at most `2^-(b+5)` in its respective game, its probability of producing a valid fresh message/signature pair is at most `2^-b`. The five bits round up the reduction's factor of 27. The hypothesis covers the two keyed pseudorandom functions, the message digest used to select FORS targets, and the multi-target properties of addressed hashes used in FORS, WOTS+ and tree authentication. A concrete hardness estimate must cover the resources used by each constructed adversary, including simulating signing. [Lean theorem](Integration/SlhDsaFixedPrimitiveWitness.lean) · [Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*](https://eprint.iacr.org/2022/346)

For comparison with AES key search, the proposed quantum metric is total logical gates at a common maximum depth and a common success probability. A path through the oracle machine can return any function of its classical input at zero charged cost. Consequently a gate-level comparison needs an explicit circuit model for classical control, state preparation and coherent operations, along with computational hardness estimates for the fixed hash functions. NIST identifies several relevant cost measures and suggests maximum-depth checkpoints of `2^40`, `2^64` and `2^96`. [Checked scope of path costs](Integration/SlhDsaPathCostScope.lean) · [Fixed SHAKE reduction](Integration/SlhDsaShakeFixedQuantum.lean) · [NIST evaluation criteria](https://csrc.nist.gov/projects/post-quantum-cryptography/post-quantum-cryptography-standardization/evaluation-criteria/security-%28evaluation-criteria%29)

The generic block-cipher reference game has one independent uniform permutation per key. A uniformly chosen key selects the challenge permutation. The adversary receives the entire challenge permutation for free and can query the keyed family in either direction. A classical player making `q` forward or inverse queries recovers the hidden key with probability at most `(q+1)/|K|`. In the quantum game `D` counts sequential batches and `W` bounds the sum of active lanes on each execution path. The proof allows entangled queries and adaptively selected batch widths. At the three AES key widths, recovering the hidden key with probability one half requires `D·W ≥ 2^124`, `2^188`, or `2^252`. Applying this comparison to concrete AES and SLH-DSA in logical gates needs a common circuit model and a depth-sensitive signature reduction. [Classical ideal-cipher key recovery](Integration/SlhDsaIdealCipherClassical.lean) · [Quantum ideal-cipher key recovery](Integration/SlhDsaIdealCipherWork.lean) · [Adaptive batch semantics](Integration/SlhDsaParallelRowWork.lean) · [FIPS 205, §11](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf)

## Six-set extensions (2026-11-23)

Lean checks strong and existential forgery bounds for all six pure SHA-2 sets in each of the following models. The [all-set shared-compression theorems](Integration/SlhDsaCompressionAllSets.lean) state both forgery bounds directly for the classical and quantum byte forgers, with their query budgets and encoded-message cap.

| Parameter sets | Classical ideal compression | Quantum independent components | Quantum shared ideal compression |
|---|---|---|---|
| SHA2-128s, 128f | [128s](../security/MIdeal/Sha2_128s.lean) · [128f](../security/MIdeal/Sha2_128f.lean) | [SUF](Integration/SlhDsaSetClosed.lean) · [EUF](Integration/SlhDsaSetEuf.lean) | [General budgets and one signature](Integration/SlhDsaCompressionLongSignature.lean) · [numerical certificate](Integration/SlhDsaCompressionLongBenchmark.lean) |
| SHA2-192s, 192f, 256s, 256f | [SUF and EUF for classical byte forgers](Integration/SlhDsaCompressionClassicalWide.lean) | [SUF](Integration/SlhDsaSetClosed.lean) · [EUF](Integration/SlhDsaSetEuf.lean) | [General budgets](Integration/SlhDsaCompressionWideMixed.lean) · [at most one signature](Integration/SlhDsaCompressionSingleTarget.lean) · [multiple signatures](Integration/SlhDsaCompressionTargetSubset.lean) |

For all six sets, the classical simulation prepares and measures a basis query for each classical table read. It preserves the public and signing budgets, the encoded-message cap, and the forgery probability at each fixed pair of tables. Consequently the shared-table quantum numerical certificates below also apply to these classical forgers. All compression-model probabilities are averaged over random compression tables. Security of the concrete SHA-2 functions remains a cryptographic assumption.

[The concrete SHA-2 reduction](Integration/SlhDsaRustQuantum.lean) pairs the Rust
API correspondence with strong and existential unforgeability in the quantum hash
games for every set. [The full component-oracle proof](Integration/SlhDsaSetClosed.lean) bounds strong
forgery for all six pure byte schemes, including the reduction's own queries.
[Existential forgery](Integration/SlhDsaSetEuf.lean) has the same bound. Both results
assume capped messages and a tweakable-hash input cap at least the maximum of two,
the WOTS length, and the FORS tree count. The signer handles classical queries.

For SHA2-192s, 192f, 256s and 256f, the [shared ideal-compression SUF and EUF theorems](Integration/SlhDsaCompressionWideMixed.lean)
give explicit forgery bounds. The earlier [fully quantum estimate](Integration/SlhDsaCompressionWideFloor.lean)
exceeded or equaled one even at zero adversary queries because it charged the entire honest construction as quantum work.
The [two-phase signature reduction](Integration/SlhDsaCompressionClassTwoPhase.lean) charges this work classically.
With `c` classical reads followed by `q` quantum queries, the [prefix collision term](Integration/SlhDsaCompressionMixedCollision.lean)
is `(c² + c(2q+1)² + 16(q+1)³) / 2^(8n)` for an `n`-byte prefix. At a 1 KiB message limit,
`2^40` public queries and `2^20` signing queries, Lean [checks this cost is at most 1/256](Integration/SlhDsaCompressionMixedBudget.lean)
per nonsingleton arity. The message-hash proof retains only one FORS coordinate, and its contribution
makes that particular estimate at least one at `2^40` public queries for any message or signing budget.

With at most one signing query, the proof uses all decoded FORS coordinates. For encoded messages of at most 64 KiB and up to `2^40` public queries, the complete forgery bounds are `2^-19` (192s), `2^-22` (192f), `2^-78` (256s), and `2^-79` (256f). [Signature theorems](Integration/SlhDsaCompressionSingleTarget.lean) · [Numerical certificate](Integration/SlhDsaCompressionSingleBenchmark.lean)

The following entries give $b$ such that forgery probability is at most $2^{-b}$, with at most `2^40` public queries and encoded messages up to 64 KiB. The [multi-signature proof](Integration/SlhDsaCompressionTargetSubset.lean) counts the FORS coordinates that a single target must share with the forgery. [Benchmarks for two through four signatures](Integration/SlhDsaCompressionSubsetBenchmark.lean)

| Maximum signing queries | 128s | 128f | 192s | 192f | 256s | 256f |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 39 | 39 | 19 | 22 | 78 | 79 |
| 2 | — | — | 19 | 22 | 74 | 73 |
| 3 | — | — | 9 | 2 | 33 | 22 |
| 4 | — | — | — | — | 7 | — |

A dash indicates that the certificate provides no value for that case.

For SHA2-128s and 128f, the [SHA-256 message PRF](Integration/SlhDsaCompressionHmac256Signature.lean)
and [all four arity-specific target collision terms](Integration/SlhDsaCompressionSmallClass.lean)
have numerical bounds for the signature forger using both shared compression tables.
The [signature ITSR bound](Integration/SlhDsaCompressionSmallItsr.lean) uses a 75-bit projection
on SHA2-128s and a 61-bit projection on SHA2-128f. These projections describe collision events
in the reduction. Their widths alone give no forgery-security level.
[The initial narrow shared-compression theorems](Integration/SlhDsaCompressionSmallClosed.lean) give strong and existential forgery bounds for both sets. Their class-collision cost already exceeds one at zero adversary queries. At one signature, a 64 KiB encoded-message cap, and `2^40` public queries, each of the [one- and two-node target-collision terms](Integration/SlhDsaCompressionShortClosed.lean) is at most `2^-45`. The [message-hash term](Integration/SlhDsaCompressionSmallSingle.lean) is at most `2^-43` for 128s and `2^-73` for 128f because all FORS indices must match the same target. For the WOTS public key and FORS roots, the [long-input proof](Integration/SlhDsaCompressionLongSignature.lean) conditions the quantum forgery on the honest transcript and charges the cells read to verify a specific forged path. The [complete numerical bound](Integration/SlhDsaCompressionLongBenchmark.lean) is `2^-39` for both narrow sets at that benchmark.

At `2^40` quantum port calls and `2^20` signatures Lean checks the following
upper bounds. The first row is for the entire signature scheme in the four-component
model. The second is for the exact ITSR digest game alone. The sharper 128s signature
entry uses the existing specialized numerical estimate.

| SHA-2 set | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---:|---:|---:|---:|---:|---:|
| [Strong or existential forgery](Integration/SlhDsaSetNumeric.lean) | 2^-22 | 2^-21 | 2^-81 | 2^-85 | 2^-147 | 2^-149 |
| [Exact ITSR game](Integration/SlhDsaItsrWidths.lean) | 2^-20 | 2^-22 | 2^-82 | 2^-86 | 2^-148 | 2^-150 |

[The compression-table experiment](Integration/SlhDsaCompressionQuantum.lean) gives the
forger superposition access to the same tables the signer uses. Its linear theorem
reduces forgery to comparisons of averaged hash games. [The fixed-public-seed address PRF](Integration/SlhDsaCompressionPrf.lean) now
has a bound of `8 q² / 2^(8n)` with quantum access to both compression tables
and classical requests to the exact truncated PRF. The port-uniform distinguisher
can make at most `q` quantum port calls. The [public-seed average](Integration/SlhDsaCompressionPrfSeed.lean) permits an arbitrary independent public-seed distribution
and uses the scheme’s full PRF domain. The [signature reduction’s address-PRF step](Integration/SlhDsaCompressionPrfBudget.lean)
has loss at most `8 B² / 2^(8n)` for all six sets. The [budget `B`](Integration/SlhDsaCompressionPrfMachine.lean)
counts key generation, the forger’s compression queries, a signing cost per signing
query, and the final forgery check. Each signing cost includes the message PRF.
Its inputs are the byte forger’s query limits and the maximum encoded message length. The [FORS target-collision](Integration/SlhDsaCompressionFors.lean) and
[decisional second-preimage](Integration/SlhDsaCompressionDspr.lean) games now also have bounds
in the shared-compression model. For all six sets, the bounds are `(2q+1)² / 2^(8n)`
and `168q² / 2^(8n)` above the DSPR baseline, respectively. Here `q` bounds the
quantum compression queries of the second phase. The [public hash interpreter](Integration/SlhDsaCompressionOpen.lean)
charges the FORS reduction's final answer one `Hmsg` evaluation and `k` singleton
hashes. The [tweakable hash](Integration/SlhDsaCompressionCost.lean) and
[message hash and PRF](Integration/SlhDsaCompressionMsgCost.lean) costs count the
compression blocks used by each set. [Open key generation](Integration/SlhDsaCompressionKeygen.lean)
and [each FORS signing request](Integration/SlhDsaCompressionForsSign.lean) have
compression-query budgets for all six sets. The [signature reduction](Integration/SlhDsaCompressionForsReduction.lean)
instantiates both FORS bounds with `forsBudget S L q qs`. Here `L` bounds the
encoded signing and forgery messages, `q` bounds the forger's compression queries,
and `qs` bounds its signing queries. The budget counts honest compression calls
during key generation, each signing request, and the final answer. For SHA2-192s, 192f, 256s, and 256f, the WOTS+ [preimage](Integration/SlhDsaCompressionWotsPre.lean),
[chain target-collision](Integration/SlhDsaCompressionWotsTcr.lean), and
[undetectability](Integration/SlhDsaCompressionWotsUd.lean) games also have
shared-compression bounds. With `q` second-phase queries and an `n`-byte node,
the bounds are `2(2q+1)²/2^(8n)`, `(2q+1)²/2^(8n)`, and `8q²/2^(8n)`
above ideal for undetectability. The first phase can use its challenge and
collection oracles. The [WOTS+ signature reduction](Integration/SlhDsaCompressionWotsReduction.lean)
instantiates all three budgets from the byte-level forger's compression queries,
signing queries and encoded-message limit. Its budget includes the cost of each
game's final answer. For the same four sets the [arity-one class TCR theorem](Integration/SlhDsaCompressionClassOne.lean)
bounds the component game by `(2q+1)²/2^(8n)` for a second phase making at most
`q` compression queries. The [arity-one signature reduction](Integration/SlhDsaCompressionClassReduction.lean) derives this
query count from key generation, signing, verification, and the byte forger’s budgets. The two 128-bit sets also need
a separate argument for collection queries that hash multiple nodes with SHA-256. In particular, `shared_singleton` proves that the secret-address PRF and
a singleton tweakable-hash call agree on the corresponding inputs. An independent
four-component oracle does not preserve this identity. Any transfer must account for
which inputs the reduction exposes or analyze the compression games directly.

The [shared-compression forgery bounds](Integration/SlhDsaCompressionCompose.lean)
now substitute the address-PRF and both FORS estimates directly into the averaged
byte-level SUF and EUF theorems for all six sets. For the four wider sets they
also substitute the three WOTS estimates and arity-one TCR. This intermediate theorem groups five terms in
`wideRemaining`: the averaged message-PRF gap, ITSR, and class TCR at arities
two, WOTS length, and FORS tree count. All seven discharged terms use budgets
from the byte forger. The narrower sets also retain the three WOTS games and
arity-one TCR.

The [SHA-512 HMAC key-block hop](Integration/SlhDsaCompressionHmacHop.lean)
replaces the two keyed starting states together in the actual message-PRF
experiment. The loss is at most `8q²/2^(8n)` with the external compression port
available throughout. The weighted budget charges each message evaluation for
its remaining inner blocks and its outer compression. The ideal side of this
hop continues HMAC from two independent chaining states. The [signature-level message PRF theorem](Integration/SlhDsaCompressionHmacSignature.lean) derives the weighted budget from the actual byte forger’s queries and maximum encoded message length.

For each wider set, the [composed HMAC theorem](Integration/SlhDsaCompressionHmac.lean)
also replaces the outer compression with a private random function of the inner
digest, for an additional loss of `8q²/2^512`. A collision between inner
digests of distinct messages can still cause equal answers. The [ideal-message comparison](Integration/SlhDsaCompressionHmacCollision.lean) bounds the remaining gap by the probability of observing two distinct message-oracle queries with the same inner digest. The [extractor](Integration/SlhDsaCompressionHmacExtract.lean) converts such a pair into a full SHA-512 compression collision or a compression input mapping back to the inner starting state, charging one query per block on each path.

For class TCR at arities two, WOTS length and FORS tree count, the
[signer reduction](Integration/SlhDsaCompressionClassCandidates.lean) constructs
a compression-port machine that outputs two distinct SHA-512 inputs with equal
`n`-byte output prefixes. Its query count includes the honest first-phase
transcript, the byte forger’s second phase, and the [collision extractor](Integration/SlhDsaCompressionClassCollision.lean).
The [adaptive recording-oracle bound](Integration/SlhDsaCompressionDatabaseAdaptive.lean) proves collision mass at most `16q³/2^(8n)` after `q` coherent queries with intermediate measurements. The [measured-output theorem](Integration/SlhDsaCompressionReadout.lean) bounds the chance that the two reported inputs have colliding prefixes by `16(q+1)³/2^(8n)` for a paired ordinary-table and recording-oracle experiment. The [native program proof](Integration/SlhDsaCompressionCompileShared.lean) establishes this measured-event bound for the actual public-port machine on arbitrary normalized mixed input states.

The [combined wide-set SUF and EUF theorems](Integration/SlhDsaCompressionSearch.lean)
reduce forgery to ITSR for the signature reduction and
a public SHA-512 search game. The latter accepts a pair of distinct inputs with
equal digest prefixes or a preimage of an independently sampled starting state.
The [preimage theorem](Integration/SlhDsaCompressionPreimage.lean) bounds success against the revealed state by `(2q+1)²/2^512`, including superposition access to both tables. The [search reduction](Integration/SlhDsaCompressionSearchSplit.lean) adds this loss to the success bound for a machine that reports a prefix collision. Its four applications have separate explicit budgets. For HMAC, the
[monitored message machine](Integration/SlhDsaCompressionHmacMonitor.lean) costs
at most three times the signature message-PRF budget including witness extraction.

For ITSR on the four wider sets, [a winning transcript](Integration/SlhDsaCompressionItsrEvidence.lean) yields a covered digest among distinct final compression inputs, a full-state collision, or a preimage of the initial SHA-512 state. The [path budgets](Integration/SlhDsaCompressionItsrWalk.lean) count the compression calls needed to recover those addresses. The [FORS coordinate theorem](Integration/SlhDsaCompressionItsrCover.lean) identifies one candidate cell covered across all FORS trees and proves the distribution of its decoded coordinates for a fresh uniform state. The [signer reduction](Integration/SlhDsaCompressionItsrReduction.lean) extracts a preimage of the initial state or a pair matching on a chosen coordinate. Applying the native collision and preimage estimates gives the closed forgery bound above.

> **Update (2026-11-22): `../security` is now the six-set tree's security project.** The
> `Reduction`, `Reduction.Open` and `Ideal.Transport` modules these Integration files import are the
> same sources as before, but `Link.Basic`, `Link.Hash`, `Link.Verify`, `Link.Sha256` are now the
> Spec-free stand-ins (the single-set `Spec` = VCVio proofs were removed with the single-set tree,
> git commit `26aa3d8`; `../security/STATUS.md`, "The stand-ins"). No Integration file needed a
> change: `scripts/check-integration.sh` passes against the new `../security` (93 `security`
> modules checked, 46 Integration files, 348 theorems, standard axioms only; the last run is
> recorded in `../HANDOFF.md`, "Checks"). The quantum theorems are about SLH-DSA-SHA2-128s at
> VCVio's level (`Reduction.pureBytesAlg Link.vp (randPrims ω) …` averaged over capped random
> functions `ω`); that numerical result is separate from the real-SHA-2 Rust reduction (`../README.md`, "Quantum
> adversaries").

> **Update (2026-11-21): the composed QROM theorem is finished. Read this first; everything
> below it describes an earlier, conditional state.**
> `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed`
> (`Integration/SlhDsaComposedClosed.lean:64`, `:93`) has hypotheses on the forger only (`hq`,
> `hqs`, `hcap`) and `35 ≤ c.tl`; `hInd` and all eleven bridge statements are proved. Numeric:
> `≤ 2^-22` at `q = 2^40`, `qs = 2^20` (`SlhDsaComposedClosedNum.lean`). `scripts/check-integration.sh`
> passes (46 Integration files, 348 theorems, standard axioms). State, file map, caveats and the
> statement-level audit: `../HANDOFF.md`, `AUDIT-closed.md`, `HANDOFF-{qprf,qmach,qtcr,qfors,qwots}.md`.


> **Update (handoff).** See `quantum/HANDOFF.md` for the full state and the ordered remaining
> chain. Since the note below: `PQ/Interactive/QromBridgeCall.lean` (`run₂_callBasis_branch`:
> branch law of a computational-basis call on a general register against the additive oracle —
> PROVED) and `PQ/Interactive/QromBridgeEval.lean` (`PUE`: port-uniform machines with
> classical-evaluation nodes and weighted interface queries; closure lemmas, `EvalCost`,
> `PUE.close` — PROVED; `PUE.compileQ`, `PUE.exists_prog`, the hybrid model — NOT done). Both in
> the default target. Headlines and `BridgesRest` unchanged; no field discharged.

> **Update (bridge, stage report).** The composed QROM theorem is STILL CONDITIONAL. Proved since
> the last note (all `[propext, Classical.choice, Quot.sound]`, default target green,
> `scripts/check-integration.sh` PASS):
> * **Encoding fixed** (`Integration/SlhDsaBridgePrf.lean`): `EncX c` (tagged union of the four
>   bounded hash domains), `EncY = Bytes n × Bytes m` with bytewise addition mod 256
>   (`bytesGroup`), `encΩ ω : EncX c → EncY`; one port call evaluates one component
>   (`encΩ_thash/_hmsg/_prf/_prfMsg`), `encΩ_withPrf_local`.
> * **Bridge infrastructure** (`PQ/Interactive/QromBridgeUnif.lean`, in the default target):
>   port-uniform machine families `PU Mach q`; closure under `bind`, `liftQ`, `map`, `wrap`,
>   `wrap0`, and `close` with ANY stateful probabilistic implementation (`PU.close`);
>   `PU.compileQ`; `PU.exists_prog(_qprob)`: one VCVio query program for all port functions,
>   Part-2 `qprob` = Part-1 Born weight, uniform-sampling nodes as uniform-coin instruments.
>   This covers uniform-sampling nodes and probabilistic/lazy challengers for ONE-port,
>   ONE-phase games.
> * **PRF in the Part-1 model** (`PQ/QROM/ExactPrfStruct.lean`,
>   `PQ/Interactive/QromBridgePrfStruct.lean`): `prfStruct_real_le_ideal_add` (tight PRF bound
>   for an oracle built locally from the keyed function), `lazy_eq_avg` (VCVio's lazy random
>   function around any Part-1 machine = average over eager tables through an injective key
>   map), `prf_PU_real_le_ideal_add`: for port-uniform machines,
>   `E qPrfRealPr ≤ E qPrfIdealPr + 8q²/|K|`.
> * **`PRF` term** (`prf_term_suf`, `prf_term_euf`): the `TermBounds.prf` inequality with count
>   `q` (reduction's hashing not charged), for every port forger over `encΩ`, UNDER ONE NAMED
>   HYPOTHESIS `hInd : ∀ ω g H, prfMachSuf (ω.withPrf g) H = prfMachSuf ω H`.
> * **Headline** `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc`
>   (`Integration/SlhDsaComposedEnc.lean`): encoding fixed; hypotheses `hq`, `hqs`, `hcap`,
>   `hInd`, and `BridgesRest` (the eleven other bridge fields); bound
>   `composedBoundFinal q qs r.noPrf`.
>
> **Added after the stage report (coordinator: transport is built elsewhere, under
> `security/Ideal/Transport/`; `hInd` stays a named hypothesis here):**
> * `PQ/QROM/HybridPullback.lean` (default target): `HybridModel.pullback` — a `q`-query hybrid
>   model whose real oracle is `φ H`, built locally from `H` through an embedding of domains, is
>   a hybrid model for `H`. This is the structured-oracle form of every leaf-level Part-2 bound
>   stated on `HybridModel` (in particular `spr_embedded_obs_weighted_le`, the core of the TCR
>   family), so no ancilla simulation is needed for the FORGER's port queries.
> * `Integration/SlhDsaOpenCounts.lean`: `openCounts128s_sound` — the fields of `openCounts128s`
>   are exactly the hash-query bounds of `Reduction.Open.final_resources_final_open_128s`
>   (classical open programs at `Link.prims`); `security/Reduction/Open/Bundle` is now imported.
> * `_qrom_enc` headlines take the explicit hypothesis `35 ≤ c.tl` (not used by the proof).
> * NOT done, and why: stage 2(b) proper (a classical hash evaluation inside the quantum
>   reduction machine as an oracle call of the Part-2 program) needs (i) a port-uniformity
>   notion with classical-evaluation nodes and the branch law of VCVio's `QComp.callBasis`
>   against `additiveOracleRuntime` on a general register (only the trivial-register /
>   emulated-oracle forms exist: `fid_run_query`, `EmulatedOracle.branch_run₂_callBasis`), and
>   (ii) the quantum reduction machines in open form (their hashing is `pure (PublicHash.impl
>   prims q)` inside `liftQ` code). Stage 2(c) and every Thash/H_msg field are not started.
>
> **Blocked / not done:**
> * `hInd` (PRF-independence of the reduction machine) is NOT `rfl`: `PublicKeyCore core`,
>   `SignatureCore core`, `ForsTreeSigCore`, `XmssSigCore` are structures indexed by the whole
>   `core`, which contains `PRF` and `PRF_msg`. Needed: a transport of signing, verification,
>   the codecs and the logging harness along `core ↦ {core with PRF := g}` (not built in
>   `security/` either, `status/OPEN.md` §6). The same obstacle applies to the `msg` term.
> * Stage 2(b) (a classical hash evaluation of the reduction = a port call) and 2(c) (two ports /
>   two phases) are not started; `openCounts128s` is still hand-copied numerals. No field of
>   `msg`, `itsr`, `dspr`, `tcrFv`, `tcr*`, `ud`, `pre`, `tcrT` is discharged.
> * Limitation unchanged: at `r = openCounts128s qs` the reduction's classical hashing is charged
>   quadratically (bound ≈ 2^-22.9 at `q = 2^40, qs = 2^20`; vacuous for `qs ≳ 2^28` (ITSR) /
>   `2^39` (other terms) and for `q = 2^64`).
>
> **Earlier in this round** (`Integration/SlhDsaComposedFinal.lean`): `…_qrom_of_bridges`,
> `…_qrom_closed`: every numerical term derived from its Part-2 theorem, hypotheses `Bridges`
> (twelve simulation statements over `MixLE`/`MixPair` and the value classes), tight DSPR
> `168q'²/2^128`, UD `8q'²/2^128`, `composedBoundFinal_open_le`. `epsDspr` in
> `Integration/SlhDsaComposed.lean` switched to the tight shape.

> **Update (coordinator, after consolidation).** Tight exact DSPR-FV is now proved and imported:
> `dspr_exact_tight`, `dspr_exact_tight_of_card`, `dspr_exact_tight_zeroPre_of_card`
> (`PQ/QROM/ExactDsprTightCore.lean`, `ExactDsprTightGame.lean`): with `2 ≤ |Y| ≤ |Msg|` and no
> quantum queries before the seed reveal, `dsprSucc − dsprSP ≤ 168·q₂²/|Y|`, independent of the
> number of targets, no named hypothesis; for general `q₁` the old `2·seedLoss Sd q₁` term remains.
> Default target rebuilt (7200 jobs) and `scripts/check-integration.sh` re-run: PASS. This
> supersedes item A.2 and the DSPR row of the bounds table below (≈ 2^-40.6 at q₂ = 2^40).
> `epsDspr` in `Integration/SlhDsaComposed.lean` still uses the old shape. Not independently audited.


Lake project `quantum/` (library `PQ`, ~33k lines; `Integration/`, ~5.5k lines), Lean 4.36.0,
depends on VCVio (`../.tools/VCVio-upstream`, commit a10530a) by path.

```
cd quantum && PATH=$HOME/.elan/bin:$PATH lake build     # default target PQ: 7208 jobs, green
cd quantum && scripts/check-integration.sh               # PQ + staleness check of security/'s oleans (no lake run
                                                         # there) + every Integration/*.lean; fails on error / sorry /
                                                         # non-standard axiom. Last solo run: PASS, 204 theorems.
```
No `sorry`/`axiom`/`native_decide`/`bv_decide`. 456 `#print axioms` lines in `PQ`, 204 in
`Integration/`, all `[propext, Classical.choice, Quot.sound]`. `PQ.lean` imports every module
under `PQ/QROM` and `PQ/Interactive`.

## A. What is conditional / open (read this first)

1. **The single composed QROM theorem is NOT established.** Strongest form:
   `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc` (`Integration/SlhDsaComposedEnc.lean`):
   port function fixed to `encΩ`; forgery probability `≤ composedBoundFinal q qs r.noPrf`.
   Unproved hypotheses: `hInd` (the `PRF` distinguisher machine does not depend on the `PRF`
   component of the world; needs a transport along `core ↦ {core with PRF := g}`), and
   `BridgesRest` — eleven simulation statements (`msg`, `itsr`, `dspr`, `tcrFv`, `tcr1`, `tcr2`,
   `tcrLen`, `tcrK`, `ud`, `pre`, `tcrT`): the `ω`-averaged Part-1 game is dominated by a
   sub-convex combination of Part-2 exact-game values for adversaries with no first-phase quantum
   query and at most `q + r.<term>` quantum queries, sizes `2^128`. Formal hypotheses on the
   forger: one port program over `encΩ` with bounds `q`, `qs`; message-length cap;
   oracle-independent `optRand`/`pkSeedDist`. Pure-bytes interface only. Loose: `r` is a free
   parameter (`openCounts128s qs` = numerals copied from `security/Reduction/Open/Bundle.lean`);
   the tweak-list cap `c.tl ≥ 35` is not a hypothesis; the Open results R1–R7 of `security/` are
   not used by any proof here. The older forms (`…_qrom_of_bridges`, `…_qrom_closed`,
   `…_qrom_conditional`) quantify over an arbitrary encoding `enc`.
2. **Tight exact DSPR-FV**: PROVED and imported (`dspr_exact_tight`, `dspr_exact_tight_of_card`,
   `dspr_exact_tight_zeroPre_of_card`, `PQ/QROM/ExactDsprTightGame.lean`):
   `Success − SPprob ≤ 168·q₂²/|Y| + 2·seedLoss Sd q₁` for `2 ≤ |Y| ≤ |Msg|`, independent of the
   number of targets. Used by the composed statements. Not independently audited.
3. **Adaptive ITSR, general regime** (hash queries interleaved with target requests): the
   reprogramming term `2q√(s/|K|)` makes it vacuous at `s = 2^64`, `|K| = 2^128` for `q ≥ 2^31`.
   No known technique (incl. Grilo–Hövelmanns–Hülsing–Majenz, ≈2^30.6 there) is informative.
4. **Bridge**: one-port, one-phase. Bridged: classical requests and the PRF game for port
   programs (`QromBridgeReq/Prf.lean`); uniform-sampling nodes and probabilistic/lazy classical
   challengers and wrappers, for port-uniform machine families (`QromBridgeUnif.lean`: `PU`,
   `PU.close`, `PU.exists_prog_qprob`); the PRF game of the Part-1 model with VCVio's lazy ideal
   oracle (`QromBridgePrfStruct.lean`). NOT bridged: the two-port seed-keyed two-phase games; a
   classical hash evaluation by the reduction machine as a port call; the reduction's machines
   at the random primitives beyond port-uniformity of the two `PRF` distinguishers
   (`pu_qbPrfWC`, `pu_qbPrfC`), whose `PRF`-independence is the open hypothesis `hInd`.
5. **Fidelity** equalities hold for classical adversaries that are coin-free or draw ONE uniform
   coin up front and query the random hash classically (adaptive coins not covered). The UD
   fidelity is for the older `ExactUd.lean` game (collection = the same function, `M' = Msg`),
   not for `ExactGenUd.lean`.
6. Not proved: a uniform `Bytes m` digest pushes forward uniformly through `splitDigest` (FORS
   cover relation is on pre-split digests); the counterexample showing the OLD ITSR hybrid's
   collision term could not be dropped is a paper argument; that the `ReductionCertificate`
   "excludes a second run / classical simulation" is prose; first-phase independence from the
   forger is proved only for `bTcrArM`/`bTcrArST`; `p_cov ≈ 2^-133.7` at 128s, `s = 2^64` is the
   auditor's evaluation, not machine-checked; no running-time model; nothing about SHA-2 itself.
7. Literature status of DSPR: a single-target quantum bound for DSPR of a random function is in
   the literature (Bernstein–Hülsing, ePrint 2019/492, per a search summary); the dependence on
   the number of targets there is unconfirmed (theorem statements not read). No novelty is
   claimed for any multi-target bound here.

### Requests to the reduction lead (R1–R7; unchanged)
`HSpec prims` := `publicHashSpec prims.core` + a `.prfmsg` query.
* R1 `bPrfOpen A`, `bPrfWOpen w A` (and behind `restrictImpl`): every `Thash`/`Hmsg`/`PRFmsg`
  evaluation and the final verification as oracle queries; equation back to `bPrf`/`bPrfW`;
  count `keygenHashes + qs·signHashes + verifyHashes`, `≤ qs` `.prfmsg` queries.
* R2 `msgOpenV`, `msgOpenWV`: lazy distinguishers with the final verification open; equation;
  count `c.lazyHashes + verifyHashes`.
* R3 second-phase open programs of `toDspr/toTcr (Lazy.bOpenPreS ·)`, `bTcrArM n`,
  `rUd/rPre/rTcrT (Lazy.bWotsS ·)` provably contain EVERY hash evaluation (incl. `wotsAnswer`).
* R4 first phases do no hashing (formal: `choose`/`pick` unchanged when only the hash functions
  change). R5 same for the wrappers. R6 one bundle `final_resources_final_open`.
* R7 second phases DEFINED as the `Lazy.tblImpl` interpretation of the open program, or the
  interpretation lemmas generic in the forger program.

## B. Part 1 — the reduction against all quantum forgers (standard model) — CLOSED

Model: `QOC W spec α := OracleComp (instrSpec W + spec) α`; Born semantics `qWeight`; all quantum
games defined by `qWeight`. `RationalBorn` removed by a limit of classical approximants
(`Approx*.lean`); no change to `security/`.

Headlines, all amplitudes, no hypothesis on the forger:
`slhdsa_{,pure_,bytes_,pure_bytes_}{euf,suf}_cma_final{,_linear}_quantum_all` (`SlhDsaAll.lean`),
at SLH-DSA-SHA2-128s (`SlhDsaAll128s.lean`), general-game right-hand sides
(`SlhDsaAllGeneral.lean`), tight caps (`SlhDsaAllTight.lean`), at `randPrims f` / uniformly over a
finite function space (`SlhDsaRandom.lean`, `SlhDsaRandomFinite.lean`).
Resources: `reduction_certificate` (`SlhDsaAllCertificate.lean`): for EVERY sampler, each
reduction machine's classicalisation is syntactically the classical reduction adversary applied
to the forger's classicalisation (headline resource fact); trace inclusions
(`SlhDsaAllResources.lean`), classical counts (`SlhDsaAllCounts.lean`).
General two-phase games (`GamesGeneral.lean`) are limits of unbounded classical games
(`ApproxGeneral.lean`); they are not "the" quantum hardness assumptions.

## C. Part 2 — QROM bounds (`PQ/QROM/`), random function, all VCVio programs

| game (exact = adaptive two-phase / interactive, as the reduction uses) | theorem | bound |
|---|---|---|
| SM-DT-TCR; indexed-family collection | `tcr_exact_le`, `gen_coll_tcr_exact_le`; `…_zeroPre` | `(√((2q₂+1)²/N) + 2q₁/√|Sd|)²`; `q₁=0`: `(2q₂+1)²/N` |
| TCR final-validity | `tcr_fv_exact_le` | same |
| SM-DT-PRE (VCVio shape, planted type `M'`) | `gen_pre_sub_exact_le`, `gen_pre_exact_le` | `(√((2q₂+1)²(1/N+1/|M'|)) + 2q₁/√|Sd|)²` |
| SM-DT-UD (VCVio shape: planted `Mp ↪ Msg`, collection on other members) | `gen_ud_exact_tight` (`ExactGenUd`) | `8(q₁+q₂)²/|Mp|` |
| SM-DT-UD, older game (collection on attacked member) | `ud_exact_tight` | `(16(q₁+q₂)²+2n)/|Msg|` |
| DSPR final-validity, `Succ − SPprob` | `dspr_exact_adv_le_of_card'` | `8q₂/√N + 8q₁/√|Sd|` (O2H) |
| PRF (classical PRF oracle, quantum access to the keyed function) | `prfExact_tight_abs_le` | `8q²/|K|` |
| adaptive ITSR, no collision term | `itsr4_adaptive_le`; weighted `itsr4_adaptive_weighted_le`; queries after the last target request `itsr4_adaptive_noloss_le`; FORS `itsr4_adaptive_fors_*` | `(√((2q+1)²p_cov) + 2q√(s/|K|))²`; no-loss: `(2q+1)²·p_cov` |
| one-shot PRF / UD / DSPR, tight | `prf_tight_program`, `ud_tight_program`, `dspr_tight_program`, `dspr_tight_adv_program_of_card_le` | `8q²/size` |

Superseded but kept: O2H forms, `ExactItsr.lean`/`ExactItsr3.lean` (collision terms), circuit-only
tight forms.

Fidelity to VCVio's definitions at a uniformly random hash (classical adversaries, ≤ one
up-front coin): TCR `fid_tcrExp_eq`; TCR-FV `fid_fv_tcrFvExp_eq`; PRE `fid_pre_genPreSubExp_eq`
(+ pre-sampling `fid_pre_presample`); PRF `fid_prf_real_eq`, `fid_prf_ideal_eq` (incl. lazy =
eager ideal oracle); UD `fid_ud_real_eq`, `fid_ud_ideal_eq` (older game); DSPR-FV
`fid_dspr_succ_eq`, `fid_dspr_sp_eq`; ITSR `fid_itsr_eq`.

"Seed hidden then revealed": `Th : Sd × Tw × Msg → Y` uniform, quantum access to all of it in
both phases; phase 1 is not a function of the seed `P` (sees it only through classical answers);
phase 2 gets `P`, phase 1's classical output and the register.

### Numbers at 128s sizes (N = |Msg| = |K| = |Sd| = 2^128), q = q₁ = q₂

| bound | q = 2^40 | q = 2^60 | q = 2^64 |
|---|---|---|---|
| exact TCR / TCR-FV (`q₁ = 0`: `(2q+1)²/2^128`) | ≈2^-44 (2^-46) | ≈2^-4 (2^-6) | vacuous |
| exact PRE | ≈2^-43.5 | ≈2^-3.5 | vacuous |
| exact PRF `8q²/2^128` | 2^-45 | 2^-5 | vacuous |
| exact UD (VCVio shape) `32q²/2^128` (×14 in the headline) | 2^-43 | 2^-3 | vacuous |
| exact DSPR-FV, O2H `16q/2^64` (`q₁=0`: `8q/2^64`) | 2^-20 (2^-21) | vacuous | vacuous |
| adaptive ITSR, s = 2^64, queries after last request (`p_cov ≈ 2^-133.7`, not checked) | ≈2^-51.7 | ≈2^-11.7 | vacuous |
| adaptive ITSR, s = 2^64, general | vacuous | vacuous | vacuous |

Uninformative at realistic `q`: exact DSPR-FV (pending item A.2) and ITSR in the general regime
at `s = 2^64`. Everything is vacuous at q = 2^64 (inherent for search).

Non-vacuity: `NonVacuity*.lean` (Deutsch; Grover N=4 vs classical incl. mixtures),
`FidelityNonVacuity.lean`, `ExactPrfNonVacuity.lean`, `Examples.lean`.

## D. Composition — the strongest justified statement
(1) Standard model, machine-checked: every quantum forger (classical signing queries) against
SLH-DSA-SHA2-128s (internal/pure/byte-level, EUF/SUF) satisfies the linear inequality with
explicit reduction machines certified syntactically; also uniformly over a finite random-function
space. (2) QROM, machine-checked: the exact games above for a random function, faithful to
VCVio's definitions for classical adversaries. (1) and (2) are NOT composed (item A.1).
