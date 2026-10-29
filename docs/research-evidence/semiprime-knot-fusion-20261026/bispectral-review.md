# Independent review: bispectral-fusion.md

26 October 2026. Verdict: the terminal scalar, endpoint formula, finite-ring unit arguments, and stated non-advancement are correct. No substantive correction is required. Clarifications below make the executable scope precise.

**Primary check.** Downloaded the linked Koornwinder proceedings PDF and inspected the article's printed p.17, §3.5, equations (3.18) and (3.23): https://staff.fnwi.uva.nl/t.h.koornwinder/art/2017/2017_SSFA.pdf . The source defines the finite family through n=N and gives endpoint value delta^n (q beta,q alpha/delta;q)_n/(q alpha,q beta delta;q)_n. Substitution alpha=beta_R=q, gamma=q^(-m), delta=q^(m+2), N=m−1 gives exactly the report's (1) and (6). Their use here is algebraic; the source's complex orthogonality assumptions are not imported into R.

**Terminal constant.** In the cleared sum, for j<m the gamma-tail factor contains exponent (1−m)+j+(m−j−1)=0. Only j=m survives. The last-term scalar is

    (q^(−m);q)_m q^m/(q;q)_m
      = (−1)^m q^[−m(m−1)/2].

Moreover each paired factor satisfies

    (1−q^(r+1)X)(1−q^(r+2)/X)
      = −q^(r+1)[W−q^(−r−1)−q^(r+2)],  W=X+q/X.

Multiplying r=0,...,m−1 proves the report's (4)–(5), including the exact prefactor q^m(q^(m+3);q)_m. No additional X-power, sign, or monic leading coefficient is missing. This is a polynomial identity at collision inputs, not a canceled evaluation of an undefined R_m.

**Endpoint and self-duality.** The specialized endpoint factors q beta=q alpha=q² cancel as scalar units; q alpha/delta=q^(−m), and delta^n=q^((m+2)n). This verifies (6). Termwise upper-parameter interchange proves self-duality on 0≤n,x≤m−1, and hence (7). All terms terminate legally before the zero lower factor. Extending the canceled last legal hypergeometric series off this finite range is not justified; the report correctly does not do so.

**Unit ranges.** For legal j≤n≤m−1, the nonzero lower exponents lie in [1,m−1], [2,m], [m+4,2m+2], and [1−m,−1], using an empty range when its length is zero. Their absolute values are at most 2m+2. The leading-coefficient upper factors likewise have only nonzero exponents of absolute value at most 2m+2. The terminal prefactor uses exponents m+3,...,2m+2. The single strict guard ord_P(q),ord_Q(q)>2m+2 suffices; the report's stronger condition 2m+3 below both orders is safe. Distinct node differences factor as displayed; their second exponent x+y+3 is positive and at most 2m for distinct x,y in this grid (the report's looser bound 2m+1 is harmless). Therefore all required scalar inverses and the basis-change/Vandermonde inverses exist over R. No collision-dependent value is inverted.

**Small m.** The source's stated finite-family N≥1 corresponds to m≥2, exactly the report's assumption. For m=0 the prefix is 1. For m=1, C_1(W)=W−q^(−1)−q² is direct, and the cleared identity still reads T_1(qX)=q(1−q^4)C_1(W), if that identity is desired. There is no need to invoke a nonexistent two-row legal endpoint packet in these cases. On the stated order guard, q^4−1 is a unit. No new fallback cost is hidden here.

**Acquisition and scope.** The q-Racah parameters and R_0 require only binary powers and constant initial data, but a full m-by-m transform is not acquired. The scalar normalization (q^(m+3);q)_m is payable by the already licensed scalar q-Pochhammer routine in softly O(sqrt m) ring operations (or corresponding polylog-N bit overhead). Equation (7) at one *supplied integer* x has the same upper-bound cost. This does not yield the degree-(m−1) row residue at arbitrary native z, nor its coupled norm. A known beta exponent E does not provide the integer spectral label x: the condition z=q beta^E=q^(−x) is beta^(E+H+Hx)=1. It must not be solved or assumed for free, and may hold differently in the two residue fields.

The proposed useful next interface—two top legal row residues modulo the acquired degree-L quotient—is correctly labeled an additional, stronger-than-scalar acquisition requirement. In implementing its final recurrence, use the scaled spectral variable mu=qW, or absorb its known unit q into the coefficient multiplying W. The finite monic recurrence's coefficients should be derived with their scalar-unit normalizations rather than importing a normalized R_m recurrence through its zero terminal denominator; the report does not claim those coefficients are already acquired. This clarification does not affect its negative execution result.

No numeric campaign or repository edits. The report establishes an exact executed specialization and payable scalar normalization, not a new fast prefix algorithm; the existing softly O(L+sqrt(Lm)) bound remains unchanged.
