# Independent review of direct-residue.md

26 October 2026. Paper-only review against the authoritative [frozen hybrid-handoff §5](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-axis-supplier-20261026/hybrid-handoff.md), and the frozen singular-solve contract. No tests or repository edits. **PASS for the weaker output target, consumer and charged baseline.** The report's old scratch handoff reference has been replaced by the frozen authoritative path.

## Short weighted contract and multiset semantics

The handoff gives at most K rows per public factor bin, a short physical clock, and exact-integer provenance only at the nonsplit good component in the correct bin. Nonaxis content g=gcd(a,K)=gcd(b,K) obeys g<=sqrt K, and every good-field hit has the common factor tag modulo n_g=K/g. Its axis argument gives the full K tag. The new report uses precisely these claims; it does not infer tags from arbitrary scalar-axis aliases or omit axes/deleted-row conditions.

The stronger all-component clock difference certificate is essential and is used correctly. Every 1-q^t for 0<|t|<=16H is a unit, and h<16H. Therefore each fixed row has at most one clock hit in every field component, including split components. Repeated rows may nevertheless all hit: they are a multiset, and their multiplicity is counted in d. Since d<=K<R, that integer is a unit at the good field.

The scalar Laurent sums have only simple poles: each summand is regular or exactly delta^{-1} at each field component. Thus V counts hit rows, and U sums their tags; at the good component they are (d,dr). No separation, distinct-root premise, or unknown Hasse precision is used. The direct product B^J implements these multiset statements. A quotient B[X]/F with repeated roots is not an interchangeable reduced algebra; the warning about nilpotents and potentially higher operator poles is correct. The short pair F,N_w can still be formed division-free by weighted product trees, with repeated rows kept, but does not supply its long clock sum.

## Consumer and whole palette

The norm gate for V is sound. A saturated norm cannot discard a nonempty correct sector, because d is nonzero at its good field. A unit norm supplies an actual inverse in the quadratic algebra. If the tau-coordinate of U/V has a proper coordinate gcd, factor; if it is a unit, reject; if globally zero, scan bounded scalar tags. On the correct sector that process either factors or reaches the actual tag, since the tau-coordinate vanishes at the good prime. False attempts return only checked factors, bounded candidates, or failure.

Across sectors sum n_g<=K sum_{g|K}1/g<=K(1+log K), plus the axis scan. Lifting one output modulo K/g gives g candidates modulo K. All bins and sectors must be retained. The resulting O(log N)(1+sqrt K tau(K)) palette bound matches the frozen handoff; the uniform epsilon=1/12 divisor bound and logarithmic absorption justify O(K^{2/3}), without asserting tau(K) is polylogarithmic.

One shared restricted-HH palette call at modulus K is legitimate. With S<=C K^{2/3} and its parameter proportional to K/S, the palette-start term is O(K), and the collision term is O(S^{3/2})=O(K), after increasing fixed constants. Complementing unit candidates by N/r mod K covers either factor. The scalar order premise is inherited from beta^H, not inferred from a torus order. Thus total-soft-K acquisition of all Laurent pairs would indeed finish uniformly, but that acquisition is not claimed.

## Baselines and block-residue cost

After all G_h(y_j) are acquired, proper norm/coordinate gcds factor. If no factor results, each row value is globally unit or globally zero: a saturated norm with a nonzero coordinate at some other component gives a proper coordinate gcd; otherwise all coordinates vanish. The all-component one-hit-per-row guard then makes its 0/1 flag exactly the desired residue, even if different components originally hit different clock indices. Repeated rows are counted again. This validates the old soft(K^{5/4}) fallback over all bins, with existing labelled saturated-row recovery and once-only extractor conventions retained.

For b-step blocks the denominator at delta=0 has degree b in the row root. Building its polynomial and evaluating it simultaneously at J supplied roots costs soft(J+b) per block. Component classification then gives that block's hit flags or factors; disjoint clock blocks cannot both hit a fixed row/component under the order guard. The residues therefore add without quotient or inclusion-exclusion. The charged soft((J+b)h/b) bound is an honest route cost including all block starts/products, not a new soft-K solver or a lower bound. Formal inverse notation has not hidden an uninitialized mixed-component inversion.

Minor notation clarification for §4: applying the linear q-antiderivative to N_w means its coefficientwise linear extension with the fixed ambient J, namely coefficient multiplier (q^J-q^h)/(q^r-q^h). It does not mean adding the monic z^J term to a degree-(J-1) tagged numerator. With that conventional extension the stated source-scope observation is correct and gives no Laurent mask.

**Disposition:** accept the simple-pole multiset target, all-component guards, correct-sector d-unit argument, validator/palette composition and explicit fallback costs. No faster Laurent projection or factoring exponent has been acquired.

## Applied disposition

The primary agent applied the fixed-J linear-extension clarification to direct-residue.md before archiving, explicitly omitting a monic leading term for N_w.
