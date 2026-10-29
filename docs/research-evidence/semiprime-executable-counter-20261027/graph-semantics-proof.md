# Actual ordered macro graph: complete semantics and public factor count

Owned NEW modules:

- `RiemannGaussian/SemiprimeMacroGraphSemantics.lean`
- `RiemannGaussian/SemiprimeMacroGraphExtension.lean`
- `RiemannGaussian/SemiprimePublicFactorCount.lean`

No prior/frozen module, lakefile, AGENTS or journal was edited. Dependencies supplied by peers: `MacroFlagExtension`, `MacroGraphUnique`, `MacroParameters`.

## Closed endpoint

`public_tensor_factor_count` proves the **literal full subdivided local 0/1 tensor contraction** equals `Fintype.card (OrdinaryFactors N)` for every public `N>0`. `OrdinaryFactors N` is exactly ordered ordinary integer pairs `P,Q : Fin(N+1)` with `P>=2`, `Q>=2`, and `P*Q=N`. Distinct orientations and squares are handled by the same predicate. The `Fin(N+1)` bound loses no factor because the positive partner proves each factor <=N.

There is no supplied global graph-correctness theorem, counting answer, factor-field operation, width-coverage promise, assumed inverse correctness, or desired unique-extension premise. The result does not itself assert a fast machine implementation or a factoring runtime.

## Literal local tables and full soundness

`Config` contains only public dyadic shape, quarter-radix/capacity, actual active widths, target digits and the actual length-unit normalizer. `localTable` / `table` read actual least-significant-first finite Boolean words in `MacroGraph.localSlotFinEquiv`'s proved ordered ports. Source digit/zero-padding/flag predicates, bundled first DFTs, explicit twiddles, normalized second DFTs, point products, INTEGER carry equations with strict physical carry-value bounds, OR gates and terminal checks are all spelled out. `subdividedTable` adds the actual equality table with port zero producer half, port one consumer half.

`ordered_tables_iff` identifies those ordered tables with their actual role-port pullback. Individual checks are extracted from literal vertices. `all_words_canonical` derives canonicality from actual producer tables rather than assuming an invariant on an array.

`extracted_macro_valid` instantiates all three canonical macro arrays from actual decoded wires. Both forward transforms are shown to evaluate the original **unpadded** digit polynomials; the point product supplies their actual Fourier product. The actual inverse tables satisfy the exact normalized reflected inverse equation, including the zero slot. `actual_arithmetic_valid` constructs the previous arithmetic-network witness out of those actual inverse and carry wires. `accepted_integer_product` then proves the original integer multiplication, not just a ring congruence.

The actual OR checks trace true outputs to true source flags; their specific lowest-digit >=2 / other-digit !=0 convention proves both operands >=2. `accepted_factor_pair` and `subdivided_factor_pair` are whole-graph soundness theorems. `subdivided_tables_iff`, `subdivided_original`, and `actual_subdivision_count` instantiate the complete equality gluing/count relation for these arithmetic tables, rather than leaving an arbitrary accepted predicate as the semantic endpoint.

## Full converse and uniqueness/count composition

`forwardArrays`, `productWord`, and `inverseArrays` explicitly evaluate the actual canonical stages. `coefficient_convolution` derives that the actual computed inverse words are the integer ordinary convolution, using proved Fourier inversion, canonical representatives and the public no-wrap bound. It does not assume that computation's correctness.

`computed_carries_exist` derives actual nonnegative bounded INTEGER carries from the true original integer product and the actual computed coefficient words. The strict quarter capacity proves physical fit. `buildAssignment` fills **all** actual physical word bits and the peer-proved unique digit/OR flags. `buildAssignment_accepted` checks every actual vertex, and `accepted_extension_exists` constructs a full accepted assignment preserving all original active input digits.

The only converse premises are the original digit-width limits, nontrivial operands and their true integer product. They are not graph-correctness/count assumptions. Their role is the ordinary witness-to-network direction of a factor-count reduction.

`extractedInput` reads accepted actual source words without truncation. `acceptedInputEquiv` proves accepted complete signal assignments are in bijection with `InputValid`: literal active-width bounds, >=2 original integer operands and their true product. Injectivity invokes the peer's proved `accepted_unique`, which derives all canonical macro/point/carry/flag/physical-bit uniqueness; it is not supplied as a promise. `actual_tensor_contraction` gives the complete local product/sum count, including equality vertices, for these input data.

## Public N, no coverage assumption

`publicConfig N hN` uses the actual quantum-proved parameter formulas: `N.size`, the literal least admissible dyadic length, axis factors, radix n/4, ceiling digit count, `min(b,L-i*b)` active widths, literal quotient/modulo target digits and the public proved unit normalizer. Its target sum is proved equal to N at the full n horizon.

`publicInput` explicitly encodes the ordinary candidate's quotient/modulo radix digits. `publicInput_width` proves every candidate x<=N obeys every actual top-bit cap, using the public target-digit bound. `publicInput_operand` reconstructs x exactly. Thus `ordinaryProjection_surjective` covers **every** ordinary nontrivial factor pair; no width-coverage or source-family guarantee is assumed. Positional digit injectivity proves the reverse direction. `publicAcceptedFactorEquiv` and `public_tensor_factor_count` close the resulting ordinary integer endpoint.

## Remaining execution/resource boundary

The previous semantic graph gap is closed: this is now an actual table/bit-assignment/factor-count proof for the typed ordered graph, not only a wiring or signal-family count.

It is still not a primitive machine-time theorem. Mathematical `readWord` uses the proved actual little-endian `bitPortsEquiv` inverse, and the public normalizer is selected from the proved unique unit equation. They have their intended exact numeric meaning, but direct binary-sum/unpack and explicit modular-inverse execution refinements, with bit costs, remain separate. The source-defined counter likewise has noncomputable finite/basis selections that require their execution/resource refinements. No original Python numeric builder-ID trace theorem is asserted; the proved typed producer/consumer graph has the literal local port order, while numeric edge/vertex renaming is a separate implementation correspondence. No root full build was restarted.

## Verification

All three modules strictly compiled with `-DautoImplicit=false -DwarningAsError=true`, writing their own `.olean` outputs. Individual logs: `semantics-build.log`, `extension-build.log`, `public-factor-build.log`. `graph-semantics-hashes.json` records exact source SHA256/commands/exit0.

`CheckGraphSemantics.lean` imports both the repository root and the public leaf, runs all 15 scoped linters for each owned namespace and audits every generated declaration plus transitive axioms. Final PASS: **348 declarations, 270 theorems; only propext, Classical.choice and Quot.sound**. Log: `semantics-audit.log`. No sorry/custom axioms/native_decide and no numerical campaign.
