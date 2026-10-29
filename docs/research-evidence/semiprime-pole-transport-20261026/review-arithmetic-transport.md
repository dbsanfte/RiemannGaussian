# Independent arithmetic-transport review

26 October 2026. Algebra and original-conductor product/localization cost PASS. One retuned-margin sentence needs qualification, and endpoint extensions should be stated explicitly. No report or repository edits by reviewer.

## Phase and carry

The inverse expansion is correct. With child r=j+s delta, delta=K/g, v=j^-1 modulo H and fixed scaled coefficients g(a_j,c_j), the linear phase difference is g delta(c_jNv²-a_j)s=(H/g)kappa s. The quadratic term is -(H/g)c_jNv³s². All higher terms vanish modulo H because g delta³/H=K/g² is an integer. Parent stationarity makes kappa an ACTUAL integer, not a modular division by delta.

Canonical ell_s,ell_0 lie in the same centered H-window, so their difference lies strictly between -H and H. Subtracting the FINAL e_s in[0,g) gives the unique carry k_s in{-1,0}; the displayed root identity and qhat^g=q are exact. The barpi exponent is fixed. This includes higher-content rows and axes. For vertical axes c_j is a multiple of delta, hence its quadratic coefficient vanishes modulo g under g²|K, as asserted.

The AP compiler exhausts the cases after common 3-power division. Unit-leading quadratic images have the stated square strata and multiplicities; a 3-divisible quadratic coefficient with unit linear coefficient gives a bijection by unit-derivative Hensel lifting. The zero-square multiplicity 3^floor(t/2) is correct. For each AP, v-Li enumerates precisely [-L(h-1),L-1], confirming the exact Lh string and its start. An explicit normalized implementation may set T0=q^M_g y0; its original signed clock index is i-M_g, with the canonical carry added on recovery. This is already required by the cited normalized endpoint contract and should not be omitted in code.

## Coverage and costs

Every factor colour has an own parent weighted Gauss row at conductor delta and one of its g child lifts. Scaling changes the squared weighted bound by g, giving the stated h_g=O(sqrt(g)*sqrt(N)/K^(3/2)). Completing child labels costs softK. This is a DIFFERENT covered bank, not an assertion that the retuned selected unique bank contains its monic triples or that this new bank is singleton.

Grouping parent APs by their power-of-3 stride gives common-base GP queries. At stride D, at most O(K/g) parents contribute, length at most(g/D)h_g; summing the square-root costs over the stride hierarchy is a convergent geometric sum. Hence soft(K+sqrt(K h_g))≤soft(K^(5/4)g^(1/4)) is a valid ORIGINAL-conductor upper bound, not a lower bound or automatically the cost at retuned K'. For retuned K' use sqrt(K' h_g) with the original-N horizon; in the maximal retuning this is at most the usual K^(4/3)g^(1/4) scale, subject to its guards.

The nonunique safe consumer is correctly restricted to product/nonunit plus actual leaf localization. Positive multiplicities can be omitted for that predicate. A saturated aggregate must be bisected; it is not an annihilator. Recover the AP index, a stored child representative of its phase and its actual carry before invoking the inherited mixed decoder. The nonzero second mixed label follows from the coefficient bound and N-dominance; no unit assumption about an auxiliary pivot is used.

## Requested scope fixes

1. Section4 says 'Fixed g fits the conservative retuned margin'. This is not true for an ARBITRARY fixed g without a constant check. At maximal conservative retuning m³≤K/1024, the same calculation gives h_g≤(sqrt(2g)/4)H+9. A sufficiently large fixed3-power can exceed16H. State an actual public h_g/endpoint test, or an explicit sufficient range (for example g≤729 with the existing divisibility and original-K margins); growing g also needs that check. No generic retuned family should be claimed from the original-conductor inequality.
2. The displayed original alias bound is for the physical window. The four endpoint gates may extend it by one physical step, adding H to that magnitude bound (and padding must use its actual index). This is harmless: replacing4H by5H still leaves the bound far below16H² for K≥54. State this extension rather than silently using the in-window constant for outside endpoints.

After these clarifications, ready to archive. No new query exponent is established, and the report appropriately identifies its remaining shared parent-string contraction.

## Final reread and additional checks

The author has applied both requested scope fixes: only the literal g=3 step is asserted safe under conservative retuning, every other fixed/growing g needs its actual original-K footprint check, and the extra endpoint H is charged. Final disposition PASS.

The O(gK) nonaxis coefficient bound is UNIFORM in the bin, not a balanced-size assumption. Parent parity Hermite gives a_j²B⁴+c_j²N²≤(4/sqrt(3))delta B²N. Since2|a_jc_j|B²N is at most the left side, |a_jc_j|≤2delta/sqrt(3). After scaling, |ac|≤2gK/sqrt(3), so each individual nonzero coefficient is at most that number. Shortest axes scale to±2K. Thus N-dominance in the actual mixed-label guard is justified.

After completing the square, arbitrary unit multiplication and translation preserve a FULL residue coset modulo a power-of-3 stride D. Compile that coset with its final canonical e0 in[0,D), length g/D; it is then one canonical AP without wrap. If an unsorted integer lift is retained instead, split its wrapped interval explicitly (at most two parts). The report's canonical-AP contract is sound with the former representation; an implementation must not use an unreduced translated start with the old length and silently drop wrap terms.
