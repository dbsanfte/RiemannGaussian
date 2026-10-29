# Padding/reindex transport: final gate

`SemiprimePaddedConstraintSpan.lean` proves rational row-space and rank equality when every new integer row is an old row or zero and every old row appears. The independent kernel-locality transport only requires the latter completeness direction. No coefficient or row-space oracle is an algorithm input. The optional `padded old pick` construction makes zero padding explicit.

Strict compilation passed. Combined root15/all-generated/transitive-axiom audit: 236 declarations, 122 theorems, standard axioms only (includes the three binomial execution modules). Logs: `padded-span-build.log`, `source-suppliers-audit.log`; audit source `CheckSourceSuppliers.lean`. This transports correctness/rank; it does not acquire the concrete source row matches.
