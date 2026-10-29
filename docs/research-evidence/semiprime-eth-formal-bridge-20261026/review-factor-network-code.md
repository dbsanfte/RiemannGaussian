# Independent review of the executable macro-FFT tensor compiler

26 October 2026. Read `factor_network.py`, `test_factor_network.py`, `factor-network-notes.md`; independently replayed the focused tests and additional fixed structural controls. **PASS for the compiler/verifier specification and all-input mathematical construction below.** The tests do not execute a contraction algorithm or establish a new asymptotic running time. No source or frozen repository files changed.

## 1. Parameters and composite-ring Fourier correctness

For every integer N>=2, L=N.bit_length()=ceil(log2(N+1)). The compiler chooses power-of-two n>=4sqrt L with n>=8, b=n/4 and d=ceil(L/b)<=n/4. Minimality gives n²<64L. Inputs have d bounded digits followed by n-d zero words, hence polynomial degree<=d-1. Their ordinary convolution has degree<=2d-2<n, so length-n cyclic convolution is exactly the required ordinary one.

The coefficient bound is uniform:

    c_i<=d(2^b-1)²<2^n.

Thus its residue modulo M=2^n+1 is its ACTUAL nonnegative integer value. This is not an assumption of typical small coefficients. The code's assert is justified by d<=n/4 and exponential domination; no instance-specific success condition is being used.

The auxiliary ring may be composite. With omega=4, omega^(n/2)=2^n=-1 modulo M. For EVERY prime divisor p|M, n is a power of two and p is odd, so ord_p(omega)=n. Therefore omega^k-1 is a unit modulo M for0<k<n, and n is a unit. The ordinary geometric orthogonality proof gives the inverse DFT over the entire ring, including prime powers; no field assumption, factorization of M or square-root oracle is required. The r/t subtransform roots inherit the appropriate principal orders.

The factorization indices are correct. For j=j1+r*j2,k=k2+t*k1,n=rt,

    omega^(jk)=omega^(r*j2*k2)*omega^(j1*k2)
                          *omega^(t*j1*k1).

The first axis, separate scale/twiddle vertices, second axis and output permutation implement precisely this identity. For inverse transforms, both roots are inverted and EVERY final output is multiplied by n^-1, giving the correct whole-transform normalization exactly once.

## 2. Canonical words and soundness on every Boolean assignment

A DFT, scale or multiply vertex first rejects ANY input or output word>=M. Its expected result is then a deterministic canonical residue. Thus a congruence does not create many alternative word encodings. Padded zero words and all constants are fixed by their local predicates.

Each actual operand digit has at most b bits, with the last digit restricted further to L-i*b bits. Consequently the collected free input bits describe EXACTLY one integer in[0,2^L). All higher bits of that digit word are forced zero. Low-digit flag `word>=2`, higher-digit flags `word!=0`, their deterministic OR chain and final one-check accept exactly operands>=2. In particular0 and1 cannot exploit padding or a nonzero flag assignment. Flags themselves have no free choices.

After the Fourier pipeline, the coefficient words are the true integer convolution coefficients by §1. The carry predicate uses INTEGER equality

    c_i+carry_i=N_i+2^b*carry_(i+1),

not a ring congruence. Carry0 is fixed zero, the final carry is checked zero, and all carries are constrained to[0,2^n). This range contains every true carry: c_i<2^n and carry_i<2^n imply floor((c_i+carry_i)/2^b)<2^n. Summing the equalities with weights2^(bi) proves PQ=N, since N fits into the n target digits. Conversely every represented factor pair P,Q>=2 with PQ=N determines its standard carries, all in range, and satisfies every check.

All internal outputs are deterministic functions of the operand digits: flags, OR outputs, both transform stages, twiddles, point products, inverse outputs and carries. Equality subdivision gives a unique second half for each original bit. Therefore valid complete Boolean assignments are in BIJECTION with ordered nontrivial factor pairs of N; there is no multiplicity from ring representations, carries, flags or padding. The total count is<=2^(2L), validating precision2L+1 for a counting theorem. The code does not itself compute that count.

## 3. Witness API truncation and prefix restrictions

`witness(P,Q)` is a verifier/generator from SUPPLIED integers, not a search algorithm. Negative or >=2^L values force the first digit word to M, which fits its n+1-bit storage but violates the digit bound. They cannot silently validate the truncation of an invalid input. True in-range nonfactors fail the target integer-carry checks. Invalid Python objects outside the stated integer/Boolean domain are not part of this mathematical interface.

`restrict` appends a local Boolean condition at an EXISTING endpoint host. It neither adds ports nor changes the underlying variables. Restricting either half of a subdivided signal is equivalent on valid assignments, because its equality vertex identifies the halves. Repeated contradictory restrictions give no valid assignment. The witness generator correctly uses the unchanged original forward computation and then validates the modified predicates; it does not recompute a convenient answer to satisfy restrictions. This supports count-based self-reduction, provided the counting backend actually returns exact restricted counts.

Every original bit has one producer and one consumer. `Builder.add` and its final endpoint assertion enforce that property in the constructed object. Subdivision replaces it by two edges and one binary equality vertex; each endpoint/ordered port is used exactly once. Original vertices lie on side0, equality vertices on side1. Parallel signals remain distinct ports/variables, as required by the tensor interface.

## 4. Exact implementation counts versus the folded mathematical network

This code has SEPARATE scale vertices for twiddles. Let w=n+1. Before subdivision:

* operand words contribute2n word edges, plus4d-2 one-bit flag/OR edges;
* three transforms contribute9n word edges (first-axis, scale and second-axis outputs);
* pointwise products contribute n word edges;
* initial carry plus n carry outputs contribute n+1 word edges.

Hence the EXACT implemented pre-subdivision edge count is

    E0=(13n+1)(n+1)+4d-2.

The original vertex count is

    V0=7n+2d+3(r+t)+2.

After subdivision the counts are E=2E0 and V=V0+E0. These formulas were checked independently against generated descriptors. They should be stated in the executable notes; the smaller folded construction's `(10n-1)(n+1)+2(n-1)` is NOT this compiler's exact count. Folding twiddles and handling flags/carry endpoints differently is a separate mathematically valid representation, not a source-code identity.

The coarse advertised bounds remain generous: d<=n/4,n>=8 imply E<=26n²+30n-2<100n²<6400L. Maximum degree is at most max(2max(r,t)(n+1),3(n+1)); since max(r,t)<=sqrt(2n), this is O(L^(3/4)) with an absolute constant below the stated100. Thus the actual degree meets the stated s=1024L power bound, not merely a word-count bound. Vertex/description counts are polynomial, and all bit ports are charged.

## 5. Uniform local cost and what remains unimplemented

The compiler is uniform integer code. Its roots, twiddles, modulus, dimensions and wiring are generated from N/L in polynomial bit time and space. A local tensor entry uses direct finite DFT arithmetic on O(L^(1/4)) canonical words of O(sqrt L) bits, or a simpler check. Even naive word multiplication and modular division give polynomial bit time/space. No complete truth table or precomputed factorization is required. Descriptions/parameters have polynomial size; wiring specifically has O(L log L) bits.

The local0/1 predicates can serve either the paper's implicit-tensor interface or the streamed Q-multilinear-extension interface in the older-route review. That mathematical connection is additional to code correctness. This implementation explicitly does NOT implement TheoremD.1, the generic counting algorithm, the primitive-machine compilation of either bridge, or a factor search. The statistics flags are structural checks, not measured proof of a factoring rate.

## 6. Independent executions

Replayed all TEN supplied focused tests, writing `factor-network-independent-replay.json`: PASS. These cover wiring, canonical encodings, integer carries, invalid/trivial supplied values, square/axis cases, restrictions, equality subdivision, convolution coefficients and inverse DFT over the COMPOSITE Fermat ring2^32+1.

Also wrote `factor-network-independent-controls.json`: four FIXED structural fixtures independently check E0/V0 and subdivision counts, supplied-factor witnesses, rejection of P+2^L and negative inputs, and cumulative conflicting restrictions. They include the n=32 network over2^32+1=641*6700417, not just a standalone transform over that modulus. All pass. These are compiler/verifier controls with supplied pairs, not a factor-search or success-frequency campaign. The all-input conclusions in §§1–3 are algebraic proofs, not extrapolations from those tests.

**Final disposition:** PASS; the exact-count distinction in §4 should be incorporated in the notes. No Boolean, canonical-word, carry, composite-ring or prefix-restriction loophole found. No new contraction-time claim inferred from testing.
