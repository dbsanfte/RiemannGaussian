# Independent final-byte matrix-clock review A

2026-10-16. Verdict: PASS. No corrections requested. This is a mathematical/source review of the implicit-agent-authored matrix consequence; I authored its earlier scalar prerequisite, so the independent review here concerns the new scalarization/finite-orbit composition and its exact scope.

Frozen targets:

- matrix-clock-obstruction.md: 10313 bytes, SHA256 `810253fc2e1749fc713b54bae6b506eeb08d5fe522c1e0c0024274e5e62206e2`.
- source-pins.json: 821 bytes, SHA256 `b918890274dfc50183fab7f2139241df72e499c3cf62a7ddbb97dbb78696df5d`.

All three durable source files were independently rehashed and match their exact byte/SHA records. The all-semiprime setup and the square-alias screen supply precisely the scalar prerequisite's short-relation box and order margins; their original controller coverage is not silently transferred.

The denominator-cleared row formula is correctly oriented: the product M(h^(t−1)X)...M(X) acts on v_k from right to left, and multiplication by the remaining B factors makes every row yield the same b_s(h^k) times the observed a_(k+t). Each row degree is at most s delta. At actual k<=L−s every denominator lies in the promised time range0,...,L−1. No matrix invertibility or state genericity is assumed.

Over K(X), rank rho<=s gives a genuine row dependency through a nonzero rho-minor and one additional row. The selected independent rows span all rows; hence solving on the selected columns implies the relation on ALL columns. Cramer/adjugate coefficients have degree at most rho*s delta<=s²delta. The coefficient of the additional row is the nonzero selected determinant, so the dependency is formally nonzero. Rankzero is handled separately by a constant coefficient relation. When ord(h)>D, root counting gives a nonzero coefficient FUNCTION on the orbit, including delta=0,D=0 and h=1.

When ord(h)=R<=D, each orbit point has a nonzero numerical row-kernel vector for the s+1 cleared rows in K^s. Interpolating its coordinates on the R distinct points gives degree<=R−1<=D and a nonvacuous coefficient function. The CLEARED rows are defined even where B vanishes. Division by b_s is needed only at the actual state times, where regularity is promised. Thus neither orbit coverage by the sample window nor denominator regularity outside that window is required. This is proof-side existence, not a hidden-order/interpolation acquisition primitive.

The scalar recurrence retains nominal order s and range k<=L−s even if its effective coefficient order drops. Substitution D=s²delta into the preceding scalar theorem gives exactly s<=m,2s³delta<=m and the displayed sample bound. The latter includes the D-position loss required to reach a nonzero leading evaluation; no extra equations are invented. The certified q-order>16m² exceeds L+s for s<=m. Therefore the claimed no-realization consequence is sound for every advised h, matrix, output vector and state on either hidden field, within these quantitative bounds.

For separately rational entries, multiplying at most s² denominators indeed gives common degree at most s²delta_entry: each cleared numerator uses its own numerator and all other denominators. Adjoining a constant coordinate for affine updates properly charges the increased dimension and degree accounting. These standard conversions do not supply a cheap scalarization or a paid matrix algorithm.

The conclusion is deliberately about exact complete-stream realization in ONE scalar geometric clock, constant output functional and bounded degree/dimension. The known two-clock scalar ratio is outside the contract. Selected jumps, other transformed streams, sparse high-degree entries, arbitrary vector circuits, nonlinear methods and direct norm/factor observations remain open. The report credits standard minors/interpolation and the prior scalar/setup results, makes no absolute priority claim, gives no operation lower bound or acquisition clock improvement, and claims no new Lean theorem/native edit. No frozen proof was mutated, numerical example used, or build run during this review.
