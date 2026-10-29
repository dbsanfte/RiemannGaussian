# Independent review: finite Boolean multiplication and jet recurrence

26 October 2026. **PASS at the modules' stated finite algebraic/specification scope.** Reviewed stable `SemiprimeBooleanNetwork.lean` and `SemiprimeJetRecurrence.lean` against the accepted Python network/counter code and the relevant MacroFermat arithmetic lemmas. No owned source was edited. The root's combined compile/lint/axiom audit is separate; this is a semantic and scope review, not an additional machine-resource proof.

## BooleanNetwork: literal values and exact finite count

The inputs are actual `BitVec bits` arrays. `decode` is their canonical natural value; `encode_decode` and `decode_encode` establish the intended finite-word correspondence, with the latter explicitly requiring the value to fit. The positional operand map is the ordinary radix-2^bits value. Its injectivity proof splits the low digit by integer remainder and then cancels the positive radix. `operandEquiv` uses this concrete value map, not an unspecified permutation or assumed semantic equivalence. Its noncomputable inverse is used only to prove finite reindexing, not as an inexpensive integer-to-digit program.

A caller must retain the encoding bound when interpreting arbitrary integer arguments: encoding an out-of-range integer wraps modulo the word width. The theorem counts actual finite words, and makes no claim that `encode` itself rejects an invalid unbounded integer. The independently reviewed Python witness's explicit invalid-input guard remains a separate interface.

`Extension` contains the inverse-output coefficient words, all n+1 physical carry words including boundaries, and the two flags **of this finite relation**. It does not yet include every forward/twiddle/inverse-stage word of the small-port Python compiler. `Valid` imposes the actual canonical Fourier equation, integer carry equations, and literal nontriviality flags. The Fourier expression is computed from the inputs; no convolution oracle or correctness premise is supplied to the final count theorem.

The coefficient word width n+1 alone would permit noncanonical residues, but `Valid` separately checks output<2^n+1. This is essential and present. Canonical inverse-convolution uniqueness uses the true coefficient no-wrap bound to turn equality in the possibly composite ring `ZMod(2^n+1)` into ordinary integer equality. The supporting MacroFermat module proves root-four cancellation and length invertibility without a primality assumption. No field assumption on the auxiliary modulus, hidden factorization of it, or modular substitute for the integer carry equations was found.

`valid_unique` fixes every output coefficient, then propagates the fixed initial carry through the ordinary equations. Both endpoint carry words and all intermediate carry bits are included in the equality of extensions. Flags are fixed to the actual operands' decide(2<=value). There is no multiplicity from unused carry capacity or a second canonical encoding.

Completeness uses public hypotheses `bits>0`, `n=4*bits`, `digits<=bits`, and target digits<2^bits. It derives `digits*(2^bits)^2<2^n`, stronger than mere canonicality below 2^n+1. The carry bound is derived from the actual equations and coefficient bound, giving every carry<2^n. Therefore encoding witnesses into the finite coefficient/carry words loses no value; the proof does not postulate a bounded carry witness. The positive-bit hypothesis is used to ensure radix>=2 and the strict exponent margin.

The nontriviality flags force **both** operands>=2. `extension_count` consequently gives one accepted extension for a true input pair and zero for a false pair, including equal-factor squares. `contraction_counts_factor_pairs` counts **ordered nontrivial integer pairs within the explicit input width** P,Q<(2^bits)^digits. It does not silently count unordered pairs or divide by two. For prime targets its right side is zero. To conclude coverage of all integer factor pairs for a chosen original N, the caller must instantiate the target digits and show the input width covers all such factors; that mapping is not hidden in the theorem.

The local predicates and their product are also derived explicitly. `valid_iff_local` expands exactly the canonical output, inverse, carry, boundary and flag conditions. `local_product` is proved from them, so there is no assumed global graph semantics or a local-entry callback that already returns the desired factor count.

## Deliberate network scope limit

This is a finite Boolean multiplication relation with explicit tensor predicates. Each inverse predicate still reads all input digits, and the nontrivial flag predicate likewise evaluates the whole operand. These are not yet the Python compiler's small-scope two-axis DFT and OR-chain vertices. The source header and local-contraction theorem acknowledge the larger scopes; the pending MacroBitNetwork work is necessary for the small-arity layout claim. The current finite count theorem alone supplies no O(L)-wire/O(L^(3/4))-scope compiler or primitive verifier cost.

Likewise, the relation uses a uniform bits-wide digit array, whereas the Python compiler explicitly limits its top input digit to the original L-bit width. An application can use the integer product bound to rule out excess high input bits for a true nontrivial factor pair, but the actual port/witness correspondence still needs to be proved. Neither this observation nor equality subdivision is a free graph construction/time theorem.

## JetRecurrence: exact code signs, index ranges and truncation

The recurrence is the literal one executed by `Jets.inverse`:

- coefficient zero is 1/a_0;
- coefficient k>=1 is `-(1/a_0)*sum_(i=1..k) a_i*b_(k-i)`.

The Lean definition writes k=n+1 and reindexes i=0,...,n to a_(i+1)*b_(n-i), with the same negative sign and no dropped boundary term. Every recursive index is smaller. Its convolution theorem is derived from this recurrence and assumes a_0!=0, matching the code's explicit zero-constant rejection. For the actual Hermite denominator a_0=1 is proved, so no unguarded rational inverse or modular nonunit arises.

`jetPolynomial` encodes exactly indices 0,...,J-1. `coeff_mod_X_pow` proves that monic remainder modulo X^J has these same coefficients and zero afterwards. `jet_add` matches componentwise addition. `jet_mul` matches the truncated convolution in the code: for k<J, all pairs i+(k-i)=k already have both indices<J. Skipping zero terms in Python changes no value.

`inversePolynomial_congruence` derives the inverse congruence from the recurrence, rather than assuming it. `inverse_congruences_difference` has the correct cross-multiplication sign: `(LB-1)C-(LC-1)B=B-C`. Thus the recurrence inverse and the previously constructed finite-geometric inverse have the same retained output.

`packet_recurrence_localQuotient` closes the precise mathematical bridge noted in the prior Hermite review: the denominator is first truncated, its constant coefficient is retained because J>0, the recurrence inverse is formed from that truncated packet, and the resulting retained quotient equals the full-cardinal-factor local quotient. The sign in subtracting the denominator-modulo discrepancy is correct. Combined with the existing numerator truncation theorem and `jet_mul`, this matches the actual Hermite inverse/product packet semantics on both inputs.

These are exact coefficient/finite-polynomial results. They do not by themselves prove that an extracted recursive `inverseCoeff` evaluation has the Python loop's memoized O(J^2) operation count, nor that arbitrary malformed arrays passed to Python retain the declared length J. The production counter always constructs positive J and length-J arrays; their imperative-state/length/resource refinement remains separate. No full bit-cost, machine execution or factor-recovery theorem is inferred from this semantic PASS.

## Source/provenance records

`boolean-jet-review-source-hashes.json` identifies the two stable reviewed modules and the MacroFermat supporting source. Tail's exact adapted external source and license pin are now explicitly recorded in `tail-external-source-provenance.json`, embedded in `tail-verification.json`, and appended to `tail-proof.md`. The working SpectralBinomial source was compared byte-for-byte with the pinned Git blob; the Apache-2.0 license bytes were recovered read-only from that same commit and retained locally. No frozen baseline was changed.
