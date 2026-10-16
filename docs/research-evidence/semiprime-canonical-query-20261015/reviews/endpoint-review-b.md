# Independent endpoint-band counterfamily review — 2026-10-15

Reviewed report: `/tmp/semiprime-query-followup-20261015/cancellations/endpoint-band-counterfamily.md`

Reviewed SHA-256: `6e906928b99645254ed640877d5bf1085be4142d436d5e6b3e68908d3ddcc1f1`

Verdict: **PASS**, conditional on the explicitly frozen balanced-family supply, uniform local-order exclusions, selector-strip/menu envelopes, and historical joint loss. This review independently checks the new counting argument and its interfaces; it does not re-prove the historical prime-distribution input. No frozen report was edited.

## Detailed checks

1. **Uniform local K count.** Fix P,m, a width-at-most-m² half-open partner box, and one index i. The Q variation contributes at most m² and delta in [-3m²,m²] contributes 4m², so Q+delta-m²i occupies an interval of length at most 5m² across every tag. Since R_P>16m² there is at most one multiple K R_P (in particular O(1)). This remains uniform for negative or large i because i is fixed in this count. Each candidate m's catalog is public and independent of the varying partner Q.

2. **Quadratic source constraint.** Reducing Q+a-2aj=K R_P modulo m and multiplying by P, then substituting PQ=a j², gives exactly a j²-2aPj+aP-P K R_P=0. Its leading coefficient a is nonzero modulo the prime m, hence at most two j for each (a,K). There are m-1 slopes, so only O(m) states per index/box. No independent free-tag factor is missing.

3. **False-tag uniqueness.** Same a,j implies m divides Delta Q. The full source lift b=-I_j(PQ-a j²)/m modulo m gives m Delta b=-P I_j Delta Q modulo m². Subtracting the two exact K equations also gives Delta Q+m Delta b=0. Thus (1-P I_j)Delta Q=0 modulo m². For j!=P modulo m this coefficient is a unit, so Delta Q=0 modulo m². A half-open box of width at most m² cannot contain two different integers separated by m². The centered representative choice does not affect these congruences.

4. **Own-tag integrality and localization.** At j=P modulo m, multiplying aP+Q+ell by P gives a(P-j)²+(N-a j²)+m bP modulo m². The square term vanishes and bP=-D modulo m, so the numerator is divisible by m². At a local hit, m²(I-i)-a(P-1)=K R_P. Since R_P divides P-1 and is prime greater than m, it divides I-i.

5. **Own-tag bounds, including negative indices.** The fixed ratio <=3/2 gives P,Q<=sqrt(3/2)*m³; the delta bounds give I<=P/m+Q/m²+1 and I>=Q/m²-3-1/m. Uniform m~M and Q~M³ imply I>=cM-O(1), while its upper bound has leading constant sqrt(3/2)<2. Therefore w<=M^.970 gives w<I<L_m-w for all sufficiently large M. For every two-sided endpoint index -w<=i<=w or L_m-w<=i<=L_m+w, the difference |I-i|<4m²<R_P eventually. Thus the divisibility forces I=i, impossible in these bands. The reasoning is symmetric under exchanging P,Q.

6. **Selector and menu charging.** The stated selector envelope gives partner-strip length O(m²G_m), hence O(G_m+1) boxes. Summing O(m(w+1)) states per box over O(M³) allowed first primes and the envelope sum_m(G_m+1)=O(K_*M) yields O(K_*(w+1)M⁵). Counting all integers rather than only allowable partner primes is a valid upper bound. No cofactor enumeration is needed because fixing P fixes its actual R_P. The endpoint catalog has at most 4w+2 indices; the +1 correctly handles w=0.

7. **Retained supply.** K_*=O(M^.020), w<=M^.970 give O(M^5.990), strictly below M⁶/log²M. Its union with frozen soft O(M^5.994) is still negligible relative to the retained supply, so the simultaneous counterfamily remains infinite with the claimed order of mass. This conclusion is conditional on the frozen supply being uniform across the stated candidate menu, as the report explicitly assumes.

8. **All signed stencils without a coefficient union bound.** For every finite stencil supported in [-w,w] with zero augmentation, all length-L intervals share [w,L-w); there the multiplicity is zero. Outside the two endpoint bands the multiplicity is also zero. Every surviving factor in the two bands is a unit in both fields. Arbitrary positive or negative integer multiplicities therefore yield a unit. This proves the simultaneous multiplicative assertion for all coefficient choices directly; no enumeration or coefficient-size assumption is necessary for the coverage statement. It does not make arbitrarily large weights computationally free.

## Scope and qualification

The proof rules out acquiring the canonical collision certificate solely from these multiplicative boundary residuals and their inverses/gcds, even with polynomial-width endpoint bands granted for free. It does not exclude additions of observed units, unrelated starts, adaptive exterior shifts, nonzero-augmentation long interiors, or arbitrary factor-or-query algorithms. Polylogarithmic band width gives soft O(m) acquisition per candidate; polynomial width is expressly coverage-only, and a polynomial candidate menu is not claimed to be globally nearlinear.

No blocking mathematical error found. This is a new classical counting extension of the frozen source mechanism, not a new Lean endpoint or a universal scalar lower bound.
