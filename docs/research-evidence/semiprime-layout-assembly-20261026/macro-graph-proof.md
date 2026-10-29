# Concrete complete macro port graph

Owned NEW module: `RiemannGaussian/SemiprimeMacroGraph.lean`. Earlier source/AGENTS/frozen evidence untouched. Source comparison: frozen `factor_network.py`, `Builder.add`, `make_input`, `transform`, point products, INTEGER carries, and equality subdivision.

## Structural graph obligations now closed

The actual `WordSignal` and `FlagSignal` constructors represent every produced word/flag; `WordPort` and `FlagPort` are the concrete source, DFT input/output, scale, product, carry and flag/check roles. `inputIndex` is exactly `j1+r*j2`, `outputIndex` exactly `k2+t*k1`. `producer`, `consumer`, `portSignal` and their flag counterparts give explicit forward/inverse ownership maps, including initial/final carries, the inverse transform, and the d=1 OR boundary. Their inverses are proved, not inferred from cardinality.

`bitEndpointEquiv` proves every physical `(n+1)`-bit word role and one-bit flag role is reached by exactly one original signal/endpoint. `Vertex`, `wordOwner`, `flagOwner`, `owner` attach those roles to actual vertices, sharing the source word and its flag in one vertex. Concrete stage ranks prove distinct producer/consumer owners. `scope_signal_injective` proves no original vertex has two roles for the same signal variable.

The critical **ordered API is explicit**: `LocalSlot` records input blocks before output blocks, word-major then bit-minor. `sourceFlagSlotEquiv` identifies the optional source flag; `localSlotFinEquiv` uses only standard finite sum/product index maps. `structuredPortEquiv`, `orderedPortEquiv`, and `orderedEndpointEquiv` prove

`BitSignal × Bool ≃ Sigma vertex, Fin(arity vertex)`.

No arbitrary enumeration of endpoint fibres is substituted for actual port positions. Literal first/second DFT input/output, product-input, carry-input/output and source-flag offset theorems match `Builder.add`: input word j bit l at j*W+l, output after q input words at (q+k)*W+l, source flag at W.

After equality subdivision, `Edge=BitSignal×Bool`, actual vertices are original vertices plus one equality vertex per signal, and actual role ports are original roles plus two equality roles. `subdividedEndpointEquiv` and `subdividedOrderedEndpointEquiv` prove the corresponding ordered endpoint bijection. `subdivided_bipartite`, `subdivided_scope_injective`, `edge_occurrence_two`, and their ordered-scope API versions prove opposite-side endpoints, no repeated variable in each actual local scope, and exactly two local ports per actual edge. These are ownership proofs, not consequences asserted from the signal count.

## Exact counts and arities

For n=r*t, d>0, d<=n:

- actual generated word signals: `13*n+1`;
- actual generated flag signals: `4*d-2`;
- original bit signals: `Epre=(13*n+1)*(n+1)+4*d-2`;
- subdivided edges: `2*Epre`;
- original ports: `2*Epre`; subdivided ports / sum of subdivided arities: `4*Epre`;
- actual original vertices: `7*n+3*(r+t)+2*d+2`;
- subdivided vertices add Epre actual equality vertices.

These are now derived for the concrete constructed/wired vertex/port graph. `total_arity` and `subdivided_total_arity` follow from the explicit endpoint/ordered-port bijections.

Exact local arity includes full source words and flag: source W or W+1; first DFT 2*t*W; scale 2W; second DFT 2*r*W; product/carry 3W; initial/terminal W; OR 3; one-check 1; equality 2. `arity_bound` / `subdivided_arity_bound` prove `(2*(r+t)+3)*(n+1)` for every actual vertex. These symbolic bounds do not yet establish the balanced public r/t or original-input-bit-size estimates.

## Representation/count bridges also proved

`boundedWordEquiv` is the literal zero-extension bijection between a small binary word and the larger physical words whose checked value fits that width. `physicalCarryEquiv` therefore resolves the real source mismatch: Python allocates n+1 carry bits but forces value<2^n, whereas the earlier Boolean relation used n bits. The extra top bit is uniquely zero; no multiplicity is inserted. The same generic theorem applies to active source digits once their public width is supplied.

`edgeAssignmentEquiv` splits a post-subdivision assignment into its two actual host halves; `originalAssignment` and `subdividedAssignment` are the real role-port pulls along the constructed endpoint maps. `graph_subdivision_count` proves equality vertices preserve the number accepted by **any** predicate on actual original role ports. It assumes no graph-correctness equivalence and invokes no counter oracle. It is not yet an instantiation of that predicate with the entire actual arithmetic compiler.

## Remaining semantic/resource boundary (explicit)

The complete structural graph and ordered scope interface are now constructed. What is **not yet proved** is one combined theorem evaluating every actual original vertex predicate on those ordered bits and identifying its accepted assignments with the previous factor-pair count. That requires:

1. define actual bit-local entries for the source, bundled DFTs, explicit scales, products, INTEGER carries, flags/OR/checks;
2. extract canonical word arrays from accepted physical bit words (and converse encode them), instantiate `MacroValid`/unique intermediates for both forward transforms and inverse, and connect their flat words to products/carries;
3. instantiate the proved actual OR-chain and carry-width equivalences across the full graph;
4. zero-pad n-d source words and enforce the last source digit's `min(b,L-i*b)` active width; prove this cap loses no nontrivial factor pair of the public N;
5. prove target digit evaluation=N, actual dyadic n/r/t/b/d public parameter formulas, and the original-bitlength bounds n^2<64L and balanced-axis arities;
6. optionally identify the typed graph with Python's exact numeric vertex/edge creation IDs. The local port order and source/result axis maps are already explicit, but no theorem currently parses/executes the Python builder trace. Edge-ID renaming is mathematically harmless only after its actual isomorphism is given.

Thus occurrence-two and no-repeated-scope are now genuine graph facts available to the generic layout, but the final factor-count/bit-runtime theorem still needs the original vertex-entry instantiation and numerical compiler bridge. No full factorer or machine-time claim is made here.

## Verification

Strict individual compiler command uses `-DautoImplicit=false -DwarningAsError=true`; log `graph-build.log`, metadata/hash file `graph-build-metadata.json`. Root+leaf `#lint+` and all-generated-declaration/transitive-axiom audit: `CheckMacroGraph.lean`, `graph-audit.log`. Only propext, Classical.choice and Quot.sound allowed. No sorry/custom axioms/native_decide. External full build not restarted.
