# Independent role and interface review

Reviewed current `SemiprimeCountRecovery.lean`, `SemiprimeSharedSummary.lean`, and stable `SemiprimeMacroFermatNetwork.lean`, including the final strict quarter-radix carry-capacity theorems. Compared against frozen `semiprime-shared-counter-20261026/shared_counter.py:218–252,290–325` and `factor_network.py:38–74,190–241`.

**Disposition: PASS for their stated theorem roles. No substantive arithmetic or contract mismatch found. This is an interface/scope review, not a second verification of every Lean proof.**

## Prefix recovery

`select_sound` and `search_some_sound` fix ONE original witness predicate P and its bit projection. The count input is indexed only by a list of fixed original bits, and `hcount` identifies those values with exact counts of `restricted bits P fixed`. This does not require a counter for arbitrary new global predicates. The zero-child rule is legal when its count vanishes because a witness in the current prefix exists; the other child must contain one.

Call counts are attached to the same recursive branch: at most one initial count and one count per requested bit. Repeated indices do not invalidate soundness; the theorem promises a single witness satisfying all returned pairs. Recovering an entire numerical factor additionally requires the selected original input bits to cover its encoding, and requires the original predicate to be the actual valid network. Neither is silently asserted. The count correctness and its cost remain explicit premises, not free capabilities.

## Shared measurements

`fibre_factorization` has exactly the useful invariant: group g's value may depend on its own assignment, but on every OTHER group only through its measurement. Representatives are required to match inhabited measurement fibres; they need not obey forced-coordinate restrictions. Forced restrictions are imposed on the real local summation variable, exactly as in Python, where representatives are found BEFORE the forced-bit filter.

Empty measurement fibres produce zero and require no valid representative. Empty coordinate groups correspond to singleton local-assignment spaces, so the theorem permits them without changing multiplicities. If a local-assignment TYPE itself is empty, a globally supplied representative function may not exist; this is not an issue for Boolean coordinate groups and is not claimed as a construction theorem. Empty group-index families are also covered by the finite empty sum/product conventions.

Python mutates the working full assignment between group scans instead of restoring a fixed representative. This is consistent: every previous group value left in the buffer remains in the same measurement fibre, so `hinvariant` makes the result equal to the formal fixed-representative formula. A future imperative refinement should record this invariant explicitly.

The theorem does not construct integer measurement ranges, prove their size/height bounds, find representatives, partition actual tensor factors, or prove that the counter's group expressions satisfy `hinvariant`. These are genuine next compiler/layout interfaces. Its hypotheses are pointwise structural facts, not supplied contraction values.

## Macro arithmetic and canonical carries

The literal Fermat ring is `ZMod(2^n+1)`, n a dyadic length, with principal root four. Complete character cancellation and length inversion are proved without primality. The two-axis identity has the compiler's index convention `j=j1+r*j2`, `k=k2+t*k1`, first root `w^r`, twiddle `w^(j1*k2)`, and second root `w^t`. The reflected frequency includes its j=0 case.

`canonical_inverse_convolution` does not confuse modular equality with integer equality: BOTH inverse output and true convolution coefficient have explicit bounds below the modulus. `2*digits<=n` ensures ordinary convolution has no cyclic wrap. The ordinary coefficient bound is `digits*radix^2`, not digits squared times radix squared.

`ArithmeticNetworkValid` contains canonical inverse outputs, the literal normalized inverse equation, and **integer** carry equations with zero start/end. `arithmetic_network_iff` consequently proves existence iff the actual digit sums multiply to the actual target digit sum; digit ranges and no-wrap are explicit hypotheses. `arithmetic_network_unique` proves uniqueness only on the stated finite coefficient/carry ranges. It does not claim that unconstrained function values beyond those ranges are unique.

The final `compiler_quarter_strict_bound` and `compiler_carry_capacity` close the physical-word distinction: under positive bits, `n=4*bits` and `digits<=bits`, coefficient bound and every carry are strictly below `2^n`, matching Python's carry predicate. A merely `<2^n+1` bound would not have sufficed. The weaker `compiler_no_wrap` remains appropriate to the modular canonical-output step.

## Still required for full composition

A Boolean bit-graph theorem must decode canonical words, show each local DFT/scale/multiply predicate equals its intended deterministic operation, wire the two macro stages and subdivision/equality vertices, enforce digit-width and nontrivial-factor flags, map target digit sum to the original N, and show every factor-pair input has exactly one valid INTERNAL bit extension. Intermediate macro words are not variables in `ArithmeticNetworkValid`; their determinism is mathematically supported by the explicit operations but the bit-level compiler bridge is not yet formalized here. Parameter choice must discharge `digits<=bits`, quarter radix and target/input range bounds. Graph edge/degree counts also remain separate.

The shared counter needs an execution/refinement proof for finite measurement and Boolean scans, exact local streaming jets, Möbius assembly and Hermite recovery, preserving original network prefixes and resource bounds. The new algebraic modules are genuine components of that proof, not a completed end-to-end counting or factoring machine. No D.1 or asymptotic factoring theorem is imported by these three interfaces.
