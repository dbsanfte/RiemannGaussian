# Independent review: coarse colour phases and factor-cell budget

26 October2026. Read `farey-cover.md` against the actual coloured/native setup and the preceding coverage reviews. The primitive uniqueness, admitted nonaxis coarse-cell phase calculation and constructor cost are correct. Axis scope needs an explicit separate statement; the stated hypotheses already exclude axes. No tests or repository edits.

## 1. Primitive fixed-phase uniqueness passes

Equality of the two unit-colour lattices is equivalent to equality of j² modulo k. The unit square kernel of2·3^e is exactly{+1,−1}, so this only identifies two lattice bases. The canonical phases for those colours are negatives modulo H, by the already proved unit-lift independence.

For a primitive v=(a,b) in Lambda_j, a prime dividing k divides a iff it divides b; primitivity therefore makes both coordinates units modulo k. Reducing its canonical phase gives lambda=−2aj modk. Since2a is invertible modulo3^e, the fixed phase determines j modulo3^e; odd parity then determines its unique class modulo k. Thus a fixed primitive row/phase has at most one colour. Covering ALL public colours by such fixed rows requires Omega(k) rows, as stated. This is explicitly a full-colour constructor statement, not a lower bound for selecting the actual one/two factor colours. Primitive axes do not occur in these lattices, so they do not create exceptions.

## 2. Nonaxis coarse-cell calculation passes, conditionally on admission

Let d=3^r,d²|k,K=k/d, with j0 a unit. Coarse membership implies a0−b0N J0² is divisible by K, so u is an integer. Every j_t=j0+Kt remains a unit modulo k, and d*v0 belongs to all their lattices. The inverse-series remainder becomes divisible by H after multiplication by d because dK³/H=k/d² is an integer. The phase difference is therefore exactly

    (H/d)[−u t−b0N J0³ t²] modH.

The quadratic coefficient is a3-unit. Completing the square is legitimate modulo odd d, and the unit-square image has phi(d)/2=d/3 values. Multiplication by H/d embeds these residues injectively into phases modulo H, proving the stated distinct-phase lower bound. Distinct phases here also give unit-separated beta-powered points because their nonzero differences have magnitude<H<ord(beta) at both primes.

This theorem assumes the ONE chosen vector actually meets d²|a0b0|<k. A shortest coarse Gauss vector only guarantees |a0b0|<=K/sqrt3, which after scaling permits roughly d*k/sqrt3, so it does not prove admission for d>1. The report correctly flags this missing selection/admission proof and does not claim the coarse-cell construction covers every prepared semiprime. Completing a square on a nonadmitted row would not supply a valid native witness.

## 3. Axis scope should be separated explicitly

The hypotheses “v0 primitive with a0,b0 3-units” exclude every axis. Moreover, if v0=(+/-1,0) or(0,+/-1), then d*v0 is not one of the allowed native axes(+/-k,0),(0,+/-k), since d²|k gives d<k. Thus the parenthetical “or its explicit axis case” cannot mean that the same nonaxis theorem already proves axis admission.

There is an easy separate admitted-axis calculation. For v=(epsilon*k,0),

    lambda_(j_t)−lambda_(j0)=−epsilon*(H/d)t modH.

For v=(0,epsilon*k),

    lambda_(j_t)−lambda_(j0)
          =epsilon*(H/d)N J0² t modH.

The quadratic term in the latter expansion is divisible by H because k/d² is an integer. Both coefficients are units modulo d, so each native axis has EXACTLY d distinct phases in this cell. Equivalently its coarse v0 is(+/-K,0) or(0,+/-K), which is nonprimitive and falls outside the main hypothesis. Handling axes separately therefore strengthens the phase-count statement; it does not rescue one-phase-per-cell reuse. Existing factor-or-unit axis processing must still retain actual nonzero-lambda axis rows unless certified, rather than treating the four lambda=0 rows as all axes.

## 4. Factor-cell estimate and full accounting

For a length-L interval centred at p0 with L<=p0, p>=p0/2. Since g''(p)=2bN/p³, Taylor remainder is at most2|b|N L²/p0³; the report's coefficient8 is safely conservative. The linear derivative and all rational bounds are correct. Outward integer rounding adds O(1) indices per cell.

The weighted-Gauss bounds give |g'|L=O(sqrt(kN)/T) and quadratic remainder O(sqrt(kN)/T²) for relative cell width O(1/T). Dividing by H yields O(m/T+m/T²+1). Multiplying by O(kT) colour/cell incidences gives the claimed GUARANTEED UPPER budget O(km+kT), with polylogarithmic scale counts absorbed. A growing power-sized T also costs more than soft k just to acquire all these cells. These are costs of this explicit all-colour/all-cell algorithm, not a universal lower bound or proof that a sparse adaptive cover cannot improve it.

For a complete implementation, keep the existing finite horizon/deletion guard explicit. One convenient safe choice is to intersect each rounded cell interval with the original signed Gauss horizon: for p within this cell, its ratio to p0 is between1/2 and3/2, so the same factor2 norm comparison used by the preceding cover bounds |g(p)+lambda|/H by that original horizon. Clipping then loses no actual correct-colour witness and inherits its2M<16H deletion-survival proof. Without clipping, any enlarged rounded interval needs its stated order-window/nonzero-label ledger. The report already requires that ledger; the construction should not silently assign an off-window endpoint the old decoder.

The critical-derivative cancellation is a conditional favourable case, not a supplied critical representative for every colour/cell. Its existence and hyperbolic admission remain unproved, as the report says. No backwards Farey-subtree implication follows from the forward character identity.

## Conclusion and preserved reports

The nonaxis coarse-phase theorem is correct, with genuinely explicit arithmetic assumptions. The fixed-primitive full-colour count and factor-cell cost remain scoped constructor results. Add the separate axis formula/qualification above and retain the finite-window ledger; no uniform all-semiprime smaller cover or full-query gain is established.

The earlier quadratic formal-map correction was copied to this NEW scratch folder as `quadratic-orientation.md`, with an explicit reference to the older mixed-trace discussion. No frozen repository report was changed.

Integration note: the separate native-axis phase calculation and clipping to the inherited signed horizon have been incorporated into the report.
