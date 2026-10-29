# Actual local truth and leaf-prefix heights

New module `RiemannGaussian/SemiprimeLocalPrefixHeight.lean`: strict compile PASS; root-import15 lint PASS; all-generated audit **16 declarations, 14 theorem constants**, standard axioms only. Logs `local-prefix-build.log`, `local-prefix-audit.log`; auditor `CheckLocalPrefixHeight.lean`.

`masked_evaluate` proves that the actual subtotal over any finite truth-assignment prefix equals the same-arity multilinear evaluator with its table set to zero outside that prefix. The masked table retains abs(entry)<=1. This is a height identity for the existing subtotal, not an instruction to materialize an exponential truth table or execute a second interpolation.

`leafNumerator` explicitly constructs

`C(delta^(w−|selected ports|))*product_(selected i)(P_i or C(delta)−P_i)`.

Its map is exactly delta^w times the selected-port interpolation leaf product. No port/factor is inverted, including at zero, and no cancellation among completed leaves is used. Its coefficient bound below J is `[J(delta+2Bport)]^w`. Missing ports are padded by known denominator powers, preserving the original local arity.

`built_local_inputs` derives the input numerator polynomials from the actual source constructor through PacketHeight. `built_truth_prefix_representation`, `built_leaf_prefix_representation`, and the actual entry-weighted leaf variant give the real local subtotal/partial product coefficients Representation over delta^w with this envelope. The entry0/1 weight adds no denominator or numerator growth. Empty truth prefixes, empty selected-port products, and zero local arity are covered.

For use in the global counter, w<=original total incidence, so this denominator and numerator are bounded by the already used total-incidence envelopes. Combined with FibreAccumulatorHeight's recordwise table masks, the partial local truth/factor-product values now have actual native height connectors, rather than an assumed intermediate Fits predicate.

Scope remains algebraic execution attachment at the polynomial/finite-jet value level. A tracked entire counter interpreter, input packet array acquisition, Boolean table verifier/circuit implementation, indexing/allocation and primitive space/time composition are separate. Ordered scan prefixes can instantiate the finite sets in these theorems without computing the expanded table family; no shortcut runtime is claimed from the identities.
