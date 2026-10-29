# Constructive whole-bin singleton cover from the completed ellipse

26 October 2026. Paper-only native arithmetic proof and algorithm. Scratch only; no repository edits, code, tests or numerical campaign.

**Positive theorem:** the paid complete ellipse admits a coverage-preserving selected row family whose hypothetical hit supports PARTITION all unit colours modulo K. Consequently the ENTIRE selected family has EXACTLY ONE leaf hit at the good nonsplit field in every correct bin, with the ORIGINAL short weighted clock. Setup is soft K and the selected family has at most phi(K) rows. This is a stronger query interface, not a faster acquisition algorithm: the retained shared engine still costs K^(5/4). The selected moment is not numerically the old original-bank M1.

## 1. Paid inputs and the exact support theorem

Use completed-source.md §§1–7. Per bin its acquired list contains all nonaxis coefficient pairs in the public weighted ellipse, completed to every unit colour; it also contains the eligible four shortest-axis pairs. Total rows are less than 23K, and all canonical phases, numeric roots and incidences are acquired in soft K. Every selected row below remains in that ellipse and uses its ACTUAL beta-coupled normalized root and physical interval [-M0,M0].

For an admitted row j of pair v=(a,b), let f_j(X)=aX²+ell_j X+bN. Its hypothetical support is

    H(v,j)={unit r mod K: f_j(r)=0 mod H}.

The incidence theorem proves that this is exactly its good-bin hit condition at R mod K, and that a congruence hit has an integer index INSIDE the same physical clock. It also proves these two structural facts:

* For fixed (a,b), its supports are exactly the canonical equal-phase classes among the eligible unit colours D(v)={r: a r²=bN mod K}. Thus one actual row per distinct phase partitions D(v).
* If two nonaxis ellipse vectors share a support colour and both have coordinates divisible by a conductor prime d, they are parallel: a nonzero determinant would be at least dK, whereas the ellipse gives absolute determinant at most (2/sqrt3)K<2K.

A support is a set of PUBLIC hypothetical residues. The actual R modulo K is not acquired or used to perform any of the selections below.

## 2. Domain nesting within one primitive integer direction

Group pairs by their primitive rational direction v0=(a0,b0), with gcd(|a0|,|b0|)=1 and canonical a0>0. Both signs of any vector are present in the completed signed ellipse, and opposite signs have exactly the same eligible domain D(v). The construction chooses a positive multiple; it does not assume that an old negative row's numeric root is unchanged. Its new actual phase and symmetric clock are already supplied.

Write an admitted positive multiple as v=d*v0, d>0. Both a0,b0 are 3-units. Indeed if precisely one were divisible by3, the stationary congruence at a unit colour could hold only with v3(d)>=e. That is excluded by g²<=|ab|<=K/sqrt3. Both cannot be divisible by3 because v0 is primitive. Thus

    v3(gcd(a,K))=v3(d)=:v<e.

At the 3-part, eligibility is exactly

    a0*r²=b0*N mod 3^(e-v).                    (1)

At the 2-part, r is odd and N is odd. Eligibility is the scalar condition d*(a0-b0)=0 mod2, INDEPENDENT of r. It is automatically satisfied by any pair already admitted to the catalogue. Equivalently, if the core coefficients have opposite parity then admitted d must be even; if both are odd there is no parity restriction.

Choose from this direction ANY existing admitted positive pair v_max with MAXIMAL v3(d). Equation (1) proves

    D(v) subset D(v_max)

for every other admitted pair in that direction. No construction of a new Dmax vector or within-direction nesting of the FINER phase classes is needed. Only eligible domains nest. All chosen rows still come from the already paid ellipse.

## 3. Disjoint high-content directions

Call a direction high if its selected v_max has v3(d)>=1. Every coordinate of that vector is divisible by3. If two DIFFERENT high rational directions had a common eligible colour r, their vectors would both belong to Lambda_r and share conductor divisor3. The determinant/ellipse theorem would force them parallel, a contradiction. Therefore the domains D(v_max) of distinct high directions are DISJOINT.

For each high direction, group its complete v_max colour fibre by the actual centered canonical phase ell. Choose ONE representative row from each phase class. Its hypothetical support is that whole class. Classes within the direction partition D(v_max), and the preceding disjointness makes all supports selected in this step disjoint across directions too.

This step applies to ALL high directions, even if some or all of their individual phase classes happen to be singletons. It does not rely on identifying ambiguity by class size.

## 4. Fill the remaining colours with singleton rows

Mark every public unit colour covered in §3, using the acquired incidence lists. For each remaining colour r, inspect its ORIGINAL own-colour Gauss row. That row is retained in the completed ellipse or its filtered shortest-axis bank, so its support contains r.

If it is nonaxis and has v3(g)>=1, its primitive direction is high. Its eligible domain is contained in the already selected maximal domain, which would cover r. This contradicts that r is still uncovered. Therefore the remaining own-colour row is either an axis or has no 3-part in its content.

Axes have full-K singleton support by the original axis phase theorem. A nonaxis row without a 3-part has g=1 or2. Its support is singleton as well: g=1 gives r=j modulo K immediately; for g=2 the incidence proof gives K/2=3^e dividing r-j, and oddness of both r,j adds the missing factor2. Thus choose this one row for the remaining colour. It covers exactly r and cannot overlap any previously covered colour.

This completes a PARTITION of the unit residues. A selected high phase class is nonempty, and every remaining singleton is nonempty, so the number of selected rows is at most phi(K)=K/3.

The rule is completely public. Direction grouping, maximal-valuation lookup, phase grouping, coverage marking and original-own-row lookup cost soft K, since both the catalogue and TOTAL incidence list have O(K) size. Computing the primitive integer direction uses ordinary gcds and sorting of O(log N)-bit metadata. No unknown factor, numerical group order, native-root separation or field equality query is used.

## 5. Exact good-bin singleton and consumer consequences

Let r*=R mod K. Its unique partition support has exactly one representative row. At that row the incidence theorem and weighted bound give an integer physical hit in [-M0,M0]. Every other selected row fails its hypothetical support test and hence cannot hit in the good field, because the same every-row/order-margin theorem applies to ALL selected rows. The clock guard supplies at most one hit in the selected row. Thus there is EXACTLY ONE leaf hit over the ENTIRE selected bank.

The hit's canonical mark is u=[R²]_n, n=3^ceil(e/2), as before. Therefore:

* The selected bank's unweighted constant-clock residue is one and its u-weighted residue is u at the good field.
* A whole-bin Lambert pair with the certified unit clock coefficient c_I now has value (c_I,c_I*u) there. Arbitrary unit-amplitude cancellation cannot occur because there is one hit. The previous O(sqrt K) singleton blocks are unnecessary for this selected family.
* A whole-bin row-value gate product(G_j+delta+epsilon*u_j) has a zero constant and unit first derivative at the good field. The established norm/coordinate gates and ratio consumer apply, retaining their explicit wrong-bin branches.

These are NEW sufficient outputs for this selected family. They are not equality with the original bank's d*u moment or its packed d*(L+u), whose multiplicity may differ. Coverage and the bounded squared-tag HH recovery are preserved. The selected family also need not have globally separated numeric roots, nor unique hits at other components; the existing gates handle those branches without importing a global uniqueness promise.

Changing phase representatives, dropping negative geometric clock positions, omitting axes before the fallback, or selecting only actual ambiguous classes instead of all high domains would not be justified by this proof. None is done here.

## 6. Acquisition cost and exact scope

All public completion/selection and all actual roots/phases are acquired in soft K. The whole-query fallback on J_selected<=K/3 rows and the original h=O(K^(3/2)) clock is still

    soft(K+sqrt(J_selected*h)) <= soft K^(5/4).

A factor return or one useful whole-bin first-order/singular readout is now sufficient, but not acquired in soft K by this theorem. The class partition can reduce rows instancewise; it has not been proved to have a uniformly power-smaller number of parts. Primitive/singleton fallback colours can still contribute at the full row scale in this cost ledger.

The genuinely constructive advance is a short-clock WHOLE-BIN unique-hit family, obtained from native arithmetic and a paid regular completion. Domain nesting and disjoint high directions suffice; no assertion that every finer phase class across all directions is nested is needed. This stronger input may support a new scalar contraction, but it is not that contraction or a sixth-rate factoring result.
