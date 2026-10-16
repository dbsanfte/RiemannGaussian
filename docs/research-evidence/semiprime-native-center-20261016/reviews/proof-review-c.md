# Independent final-byte review C

2026-10-16. Verdict: PASS, with the report's stated qualifications. No correction requested. This is a source/math/scope review of the entire report, not a Lean compilation or a new query algorithm.

Reviewed frozen artifacts:

- report.md: 15784 bytes, SHA256 `2e9eef8c4ba33e53fc5ae822483a2d6d524dfb8d46ff02eeb73209f2a88aea1d`.
- source-pins.json: 1914 bytes, SHA256 `6b75e6e2a4f6f0c39ededd3ab0ba3cb581152a67759a88dc594bf549d8b11848`.

All eight listed source files were independently read/revalidated as appropriate to their claims, and their exact byte counts and SHA256 values recomputed: all match. Native definitions inspected include lowerSum/upperSum/publicShift in SemiprimeQuotientCentering, reflectedShift/publicPairs/residuePackets in SemiprimeEuclidRowFamily, the Euclidean frame/lift in SemiprimeQuotientRows, and the compiled packet budget in SemiprimeEuclidRowBudget. The inherited cone-energy, signed row ranges, tag trimming, original order-qualified supply, and varying-selector strip premises were checked against the pinned predecessor reports. Their proofs and construction bounds are credited as inherited here.

## Arithmetic averaging

For fixed n, the catalog and light-tag labels are low-digit dependent. The exact centered lift changes modulo m² by −m h_N t/j; hence the low equation is Δa−2Δu+sΔt=0 and the high equation has coefficients Δt on h_S and −Δu/n on h_N. The factor-digit matrix has determinant q−p, so the p=q exclusion must precede the high-solution count, as it does.

Case A fixes s and permits at most two low p through the monic quadratic p²−(s+1)p+n. Its high equation is nonzero. Case B has a genuinely bounded projection fiber: the monic quadratic u²−nt(v+2u)=0 gives at most two u, and at most two signed integer a representatives give at most four deduplicated triples. Thus its projected energy is at most 4R³. Case C is precisely the inherited weighted cone energy, even with repeated field points across colors. The three contributions are bounded by 2mR⁴, 4m²R³, and 4C⁴m^(11/2). Their stated sum and subsequent sum over n and Markov bound are correct.

The exceptional object is an ordered PAIR of factor residues modulo m². The report correctly does not reuse an N-residue exceptional-set argument or claim a public exclusion test. Each first-factor residue has O(M) integer lifts; each second-factor residue occurs at most once in a half-open width-m² selector box. The inherited sum of selector boxes gives O(K_*M⁶/λ). Separately, p=q contributes O(K_*M⁵). These are absolute counts on the same original supply, simultaneously over its current candidates; no prime distribution in residue classes is assumed. Both parameter examples give negligible new loss in their stated envelopes.

## Exact native centers and multiplicities

The midpoint quantities A_N,B_N are rational half-integers, not integer-divided averages. Expanding the native endpoint sums gives the displayed nearest-integer floor for either sign of a; swapping endpoints for negative a does not alter their sum. Integer division by the positive 2m² denominator is floor division even for negative numerators. Thus the error bound |e|≤m²/2 is valid and the centered b term cancels exactly.

For N≥4, both midpoint coefficients lie between 1 and 1.5√N. The inequality S≥2√N−1 implies S−β≥0. The stated common interval for all public/reflected phases, with independently chosen centers per row, follows. Its pair-sum span is less than 16m⁴, so the inherited order D>16m⁴ suffices without strengthening it. This is the order of the actual projected gamma globally, not merely a large ambient group order. N≡S modulo D justifies replacing tN by tS.

A selected light source entry is labeled by its tag and chosen coordinate row. It injects into the deduplicated catalog even when target values repeat. Equal-product labeled quadruples therefore map into E_mod. No unsupported distinct-target count is used. For a cover, partition source indices, retaining multiplicities; each assigned group's pair-product support has size at most 2T_i−1. Weighted Cauchy–Schwarz and Hölder give g⁴≤2E k²T. Since g≥2m/3, the displayed constant 1/162 is conservative. A cover of all native packet copies contains such a one-choice-per-tag witness; the report does not assert an energy bound for the whole multicenter union or that light-tag trimming preserves a useful collision.

## Arbitrary origins and scope

After subtracting a common origin, the phase span V≤(m−2)S+6m²+m²H is safe. Product equality permits at most W=2 floor(2V/D)+1 integer multiples of D. For every resulting residue displacement, translated pair-sum Cauchy–Schwarz bounds its catalog count by E_mod; repeated displacements only overcount. Hence the W penalty is correct, uniformly over advised choices. Native centers instead have a sharper no-wrap envelope and effective penalty one.

W=O(1+m²H/D) follows from S≤3m³ and D>16m⁴. Under polylogarithmic parameters, a nearlinear total length and polylogarithmically many progressions require H≥D/(m^(3/2) polylog m). The numerical-span consequence is explicitly not a bit-complexity lower bound: exponentially represented or otherwise cheaply acquired wide origins are not ruled out.

The new result genuinely removes the former small-relative-origin restriction for literal native centers via low-factor/two-high-digit averaging. It does not rebrand the compiled catalog setup or prior cone lemma as new, and does not prove a fast long query, an operation lower bound, an all-semiprime algorithm, or a Lean/controller theorem. Arbitrary nonlinear/shared implicit computations, tiny privately selected tag families, and sufficiently wide-origin escapes remain outside the conclusion. No new computational evidence, source edits, or broad builds were used in this review.
