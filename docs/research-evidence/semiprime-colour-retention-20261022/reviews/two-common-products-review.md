# Independent review: paid two-common-products reduction

22 October2026. Reviewed /tmp/semiprime-colour-retention-20261022/higher_conductor/two-common-products.md against the native-quadratic-colour derivation and the retained scalar query. Verdict: PASS for the original scalar q=gamma^(m²), with the explicit standard preprocessing gcd(N,m)=1 and nonzero row tags j, and with recovery justified by the actual retained bounds below. The two common long products remain uncomputed. No finite tests, backend, or repository edits were used.

## 1. Quadratic mask, translation and normalization

For a row the native identity is

    (b+2ah)²=Delta+4aj I mod m,
    Delta=b²−4ac,        a j²=N mod m.

Because m is odd prime and gcd(N,m)=1, a,j and4aj are units. The mask therefore equals I mod m in kappa+R_e, where

    kappa=−Delta/(4aj),
    e=Legendre(aj,m)=Legendre(a/j,m)=Legendre(Nj,m).

Zero is included in both R palettes, and each has exactly(m+1)/2 residues. This validates both the vertex sign and the report's sign simplification. Without gcd(N,m)=1, the claimed divisions and the two equal-size palettes are not the applicable branch; preprocessing first returns the factor m when proper. Native tags are j∈{1,...,m−1}.

Let V_j(X) be the product of X−q^i over the selected native indices 0<=i<L, each index once. Set x_j=gamma^E_j, y_j=x_j q^(−kappa). Writing i=kappa+r+mn is unique for r∈[0,m). For S=kappa+r∈[0,2m−2], the lower bound i>=0 is n>=0 if S<m and n>=−1 if S>=m. The upper bound is

    n<=K             if S<t,
    n<=K−1           if t<=S<m+t,
    n<=K−2           if S>=m+t,

where L=mK+t, 0<=t<m. For K>=1 this proves exactly the baseline n=0,...,K−1, plus A at n=−1, plus B at n=K, minus C at n=K−1. All inequalities in the three boundary polynomials are correctly strict or weak, including t=0 and kappa=0.

Thus the actual polynomial identity is

    C_j(Y) V_j(q^kappa Y)
      =q^(kappa D_j) H_e(Y) A_j(Y) B_j(Y),

with D_j=K|R_e|+degA_j+degB_j−degC_j. Evaluating Y=y_j gives the report's target normalization exactly. The q^(kappa D_j) scale is necessary and has the correct sign. This argument uses the actual scalar q and integer exponents; it does not replace q by a root of unity.

## 2. K=0 and every boundary index

When K=0, H_e=1. Both A and C use the same roots q^(r−m), and the C suffix is contained in the A suffix. Their symbolic cancellation leaves exactly m<=S<m+t. The B prefix S<t supplies the other selected indices. All other r supply no native index. Both surviving groups have i∈[0,t), and they cannot duplicate an index because distinct representatives r differ by less than m. If also t=0 the products are empty and V_j=1. No evaluation of a canceled denominator, 0/0, or actual inverse is needed.

For K>=1 the A leaves have original index i'=S−m∈[0,m−2], hence belong to the actual interval. The B leaves have i'=mK+S∈[mK,L), also in the actual interval. A C leaf has i'=m(K−1)+S, with

    L<=i'<=mK+m−2<=L+m−2.

It is an auxiliary scalar collision just beyond the native interval; it must use its own original exponent ledger rather than be called an original covered native index.

## 3. Paid boundary construction and all requests

Both ordered residue lists can be acquired in O(m) logarithmic arithmetic overhead, for example by marking squares and taking the complement, including0 in both. Powers for the three channels are built from q^(−m), q^(mK), q^(m(K−1)) and a length-m walk by q. These initial powers, negative powers, x_j and q^(−kappa_j), and all scale powers have O(log N)-bit exponents in the retained polynomial-size regime. Their total cost is soft O(m+J). Counts of each prefix/suffix can use precomputed residue-prefix counts, or binary searches, so no m-by-J mask table is formed.

For each of the constant six(channel,palette) pairs, build the balanced monic product tree on its O(m) roots. A prefix or suffix has at most one canonical cover node at each depth; a K=0 interval has at most two. At a fixed depth, the sum of degrees of tree nodes is O(m), and every row requests only O(1) nodes at that depth. Hence the total multipoint-request count per depth is O(J). Batched monic multipoint evaluation at each requested node costs soft O(m+J) per depth. There are O(log m) depths, absorbed by soft notation. All polynomial construction, points, descriptors, and requests are charged. Repeated roots or target points cause no inversion issue: the monic remainder trees do not divide by point differences.

The use of segment-tree covers and batched evaluations therefore proves soft O(m+J) boundary acquisition, not merely O(m+J) descriptions of uncomputed boundary products.

## 4. Unit screens and a nonzero annihilator in the actual retained regime

Take gcd with N of every acquired boundary value. A proper gcd immediately factors. If a requested interval product is saturated, inspect its O(log m) canonical cover nodes, then descend a nonunit node. At each descent a unit pair cannot have a nonunit product; either a proper child gcd factors or a saturated child can be continued. Evaluating uncached children by Horner is sufficient: the sum of degrees along one descending path is O(m). Thus one localization adds soft O(m+log m), within the boundary budget. There is no need to localize all saturated outputs, because the first useful collision ends the task.

At a scalar leaf, multiplication by the unit q^kappa identifies the original difference

    gamma^E_j−gamma^(m² i').

A proper leaf gcd factors. A saturated leaf gives the global annihilator exponent E_j−m²i'. Its nonzero property is required; a known identical integer exponent would give a useless saturated zero.

The report's sufficient public guard min_j E_j>m²(L+m) indeed makes every native and auxiliary boundary ledger positive. More strongly, the guard is discharged by the actual retained setup, rather than left as an unspecified large-N hope:

- Both hidden factors exceed16m², hence N>256m⁴.
- Canonical E_j=N+delta_j with delta_j>=−3m².
- The retained length satisfies L<=4m².

For m>=1,

    E_j>256m⁴−3m²
       >4m⁴+m³
       =m²(4m²+m)
       >=m²(L+m).

The strict middle inequality follows from252m²−m−3>0. Thus every possible boundary leaf here has a positive O(log N)-bit ledger. No hidden order is used as algorithm input: these are the retained setup guarantees. The inherited annihilator decoder costs soft O(log N+N^(1/12)), at most the native soft-m budget, and is invoked at most once.

Actual sources for the length promise are the repository packet:

- docs/research-evidence/semiprime-block-query-20261016/reports/block-transform.md, Section1, explicitly states L<=4m² for q=gamma^(m²).
- docs/research-evidence/semiprime-block-query-20261016/sources/independent-block-operator.md, opening paragraph, repeats L<=4m² with local orders>16m².

The canonical |delta_j|<=3m² anchor contract is also retained in docs/semiprime-factorisation-investigation.md at the selected-twist entry around line32002. The general two-product algebra can allow other E,L, but outside these contracts its nonzero-ledger guard or an explicit replacement is still required.

After the screens, all boundary divisions really are by units. No factor of a saturated product has been canceled numerically. If a common H evaluation is later acquired, a nonunit H value with unit boundaries implies a nonunit original masked product by the exact polynomial identity; localization still needs an evaluator/localizer for H, and is not supplied by the boundary reduction.

## 5. Degree, shared products and the exact remaining work

Each common H_e has degree K(m+1)/2, with K=floor(L/m). The two palettes cover every residue once except0 twice, giving precisely

    H_+(X)H_−(X)
      =[product_(0<=i<mK)(X−q^i)]
       [product_(0<=n<K)(X−q^(mn))].

The ratio cancels r=0 and has the stated exponents Legendre(r,m) on all nonzero residues. Its numerical use requires nonunit handling first, as the source report says.

The second factor has degree K, and it really is cheap to construct and evaluate at J targets in the actual retained regime: L<=4m² implies K<=4m. Explicit roots, a product tree and monic multipoint evaluation cost soft O(K+J)=soft O(m+J). For an arbitrary larger L, this comparison costs soft O(K+J); calling it soft O(m+J) without K=O(m+J) would be unjustified. The boundary reduction itself does not require K=O(m).

The first full geometric factor and the separate H_± evaluations have not been acquired in the target budget. Shared root descriptors and the paid boundary construction do not supply those degree-about-L/2 coefficients or values. The conclusion is therefore an exact paid row-translation reduction to TWO fixed character-period products, with native nonzero-ledger recovery fully justified. It is not a shortened seed-index congruence, a long-product evaluator, or an improved all-input factoring exponent.

Only this independent-review file was written for the audit. The source report and repository were not changed.
