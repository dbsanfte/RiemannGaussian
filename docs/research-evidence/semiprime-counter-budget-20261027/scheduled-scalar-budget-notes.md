# Actual public scalar resource bound

NEW `SemiprimeScheduledScalarBudget` proves `scalarResources_le N hN hg` for the exact `SemiprimePublicReportPolynomial.scalarResources`. The explicit envelope is

`20*n + 2*n^2 + 5 + entryEnvelope n + scopeEnvelope n + decoderEnvelope n`,

where `n=wireCount N`. Existing public dimension theorems bound factor count and original scope. The actual fast guard supplies group/sample/degree bounds, positivity of the source denominator, and both finite alphabet bounds. The rational head ceiling is at most `2*n`; the literal precision is at most `2*n^2+1`. No separate dimension advice, hidden prime/order, matrix-rank premise or supplied count is assumed.

These coarse bounds apply only to scalar preprocessing factors. They do not replace the actual head or scope exponents, and do not replace the exact support cutoff in the weighted traversal. PublicReportPolynomial.resources separately retains those actual exponential resources. Thus the theorem is suitable for polynomial closure without erasing the balanced-head or truncated-support estimates.

Final canonical strict build PASS; root fifteen-linter and every-generated-declaration standard-only axiom audit PASS: 19 declarations,18 theorem constants (7 user declarations). Source frozen. Qholonomic has the exact scalarEnvelope API for its polynomial-growth closure. This remains a resource-envelope statement, not a new complete primitive-bit/tape execution theorem.
