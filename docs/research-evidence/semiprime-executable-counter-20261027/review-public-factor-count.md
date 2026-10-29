# Independent semantic review: actual public factor count

**PASS within theorem scope.** Read-only review of GraphSemantics, GraphExtension, GraphUnique/FlagExtension dependencies, MacroParameters, and PublicFactorCount. Hashes of the reviewed sources are in `review-public-height-sources.json`. No experiment campaign or source changes.

## What the endpoint actually counts

`public_tensor_factor_count N hN` is an unconditional finite equality for each positive N. Its left side is the product of the literal local zero/one tables on the actual ordered equality-subdivided graph, summed over all physical half-edge assignments. Its right side counts **ordered nontrivial integer factor pairs**, with both entries at least 2 and product exactly N. It is not prime-only: it applies equally to composite factors. For unequal semiprime factors it counts both orientations; for a square the equal pair is counted once. N=1 and prime inputs have no such pairs and hence zero count. No factor-coverage, unique-extension, tensor-count, or global multiplication oracle is a premise.

## Local-to-global soundness

GraphSemantics derives literal source widths and inactive zero padding, every canonical first/twiddle/second-stage equation, the point-product equation, and **integer** carry equations including both endpoints from actual ordered tables. `actual_arithmetic_valid` and `accepted_integer_product` do not merely compare residues: no-wrap and canonical-representative uniqueness recover integer convolution coefficients, and the integer carry chain reconstructs the target. Actual input digit flags and OR/terminal checks prove both operands at least 2, including d=1.

The equality subdivision is also instantiated to literal port maps. Equality slots 0/1 are the producer/consumer half-edges; `subdivided_tables_iff` proves both directions, `subdivided_original` reads the actual shared signal, and `actual_subdivision_count` preserves the entire count without multiplicity. `boolean_product_indicator` then converts the actual local entry product into the conjunction. Thus the endpoint is more than a theorem about an arbitrary supplied accepted predicate.

## Converse and uniqueness

GraphExtension constructs the actual three-stage canonical arrays, point products, inverse arrays, bounded integer carries and physical word bits. `coefficient_convolution` proves the inverse coefficients are the ordinary no-wrap convolution under the quarter-radix capacity; `computed_carries_exist` derives carries from the true ordinary product and proves their strict n-bit capacities. `buildAssignment_accepted` checks every actual vertex, including OR/terminal flags. `accepted_extension_exists` preserves the actual active source digits.

The projection back to input words is lossless: source checks supply the b-bit bound, so `extractedInput_value` does not truncate. Top-digit caps are separately preserved. `acceptedInput_injective` invokes the actual stage/carry/flag/bit uniqueness proof; `acceptedInput_surjective` uses the constructed accepted assignment. Consequently no hidden internal-witness multiplicity remains.

## Public coverage and actual graph identification

`publicConfig` obtains transform shape, quarter radix, positive widths, active digit capacity, target digits and inverse-length unit from the public bit length. The numerical transform length is the least dyadic with square at least 16L, with minimum four derived for positive L, matching the compiler's stopping convention. Active source top widths match the L-bit input capacity. `public_target_value` reconstructs N exactly. Every factor at most N is encoded within these actual widths; both inequalities factor≤N follow from a nontrivial product and do not require balanced factors or semiprimality. Conversely operand encoding is injective, so `ordinaryFactorEquiv` is a genuine bijection.

The theorem graph uses the same explicit source/stage/scale/product/carry/flag/equality signal families and ordered port wiring that the compiler implements. Nevertheless, no theorem in these files is a compiler-refinement equality between arbitrary Python objects/bytecode and Lean values. The normalizer is chosen noncomputably from its public unit equation; uniqueness makes it mathematically the same inverse used by Python, but that is not an extracted executable implementation proof. Likewise `Equiv.ofBijective` is a finite mathematical bijection, not a fast enumeration of factors. These distinctions should remain explicit in the checkpoint.

## Remaining scope

The endpoint closes graph correctness, factor coverage and exact multiplicity for the Lean graph. It does not itself provide the fast tensor counter, a primitive bit-time/space theorem, or a formal Python/Lean execution correspondence. Prefix-count recovery and the source-layout counter may now compose with this actual endpoint rather than an assumed graph-correctness oracle; their resource proofs remain separate.
