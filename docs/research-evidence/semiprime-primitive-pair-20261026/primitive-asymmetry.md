# Primitive paired Askey–Wilson evaluation and even factor-tag outputs

26 October 2026. Paper-only primary-source investigation; no repository edits, tests, numerical campaign, implementation or Lean.

**Outcome.** A symmetric paired readout is sufficient: squared tags need only two public residue roots, so an odd orientation jet is not mandatory. There is also a swap-and-sign invariant primitive tag whose quartic decoder emits only soft sqrt(K) factor-residue candidates. These are proved consumer simplifications, not acquired pole coefficients. The strongest executed finite Askey–Wilson connection specialization reduces its sum to r+1 terms, but every term retains the SAME paired norm of length h-r. The short sum evaluates exactly the two removed fringes. Thus this concrete small-degree specialization has not acquired the long scalar/readout; normalizing away its common factor would erase the collisions.

## 1. Actual pair, clock normalization and input coverage

Use the frozen [pure weighted common-tag theorem](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-fused-readout-20261026/pure-weighted-common-tag.md): K=2·3^e, H=K², rho=q^-1, q=pi^H, h=2M0+1=O(K^(3/2)), n*=3^ceil(e/2)~sqrt K. Both primes exceed 16H; all short q-differences through 16H are units. The good nonsplit field has ord(pi)>256H². All original row labels, signed coefficients and phases are acquired in soft K. For the original Gauss bank J=phi(K)<R. If a completed chirp catalogue is retained instead, its actual public total-count guard J_completed<16H<R must also be retained; a soft-O(K) count alone is not a finite-characteristic certificate.

For a primitive nonaxis coefficient pair (a,b), g=gcd(a,K)=gcd(b,K)=1, the two unit colours are j,-j, with opposite actual centered phases ell,-ell. The phase relation is

    ell²=4abN mod H.

It is a 3-unit relation, excluding ell=0 and the centered half-period. The original deterministic Gauss inputs for j and -j coincide, so their chosen coefficient vector is the same. If working with a completed/rebased phase catalogue, retain its already paid q-carry/endpoint corrections; do not silently replace its roots by uncarried ones.

Put

    c0=barpi^(a+bN), x=pi^ell,
    c=q^M0*c0, y_+=c*x, y_-=c/x.

Thus the actual NORMALIZED clock product is

    P_h(c,x)=(c*x;rho)_h*(c/x;rho)_h.            (1)

The known factor q^M0 is essential: the unshifted arithmetic index is i=t-M0 for normalized 0<=t<h. Its quadratic kernel is

    P_h(c,x)=product_(i<h)[1-c*rho^i Z+c²*rho^(2i)],
    Z=x+x^-1.

This is exactly an Askey–Wilson interpolation basis, not merely a visual resemblance. A primitive subbank alone need not contain the guaranteed witness: the full weighted cover can choose a nonprimitive vector or an axis. Its separate handling/coverage cannot be discarded just because the current investigation focuses on g=1.

## 2. Positive weaker output: orientation-free squared tags

In the WHOLE good bin every actual hit has j=R mod n*, including all contents and axes. Hence marking each row by the canonical integer

    w2_j=[j²]_(n*)

makes every good-field hit carry u=[R²]_(n*). This mark is invariant under j->-j and does not need row-root separation. At a local component define the additive simple-pole pair exactly as before, now with w2 in place of j:

    V=[delta^0]delta*sum_leaves (leaf+delta)^-1,
    U2=[delta^0]delta*sum_leaves w2_j*(leaf+delta)^-1.

At the good bin it equals (d,d*u), 1<=d<=J<R. This definition remains componentwise Laurent extraction, not ordinary inversion with a nonunit constant term. It is an unacquired scalar target.

The norm/coordinate validator and scan through 0<=u<n* return a proper factor or the correct canonical u on the good attempt. Since u is a unit square modulo 3^ceil(e/2), it has exactly TWO unit roots +/-r. They are acquired by public Hensel lifting: from r²=u mod3^t, choose the unique digit d in {0,1,2} satisfying

    (r²-u)/3^t+2r*d=0 mod3.

There are O(log n*) digits and only O(log N)-bit integers; no order, field square root modulo an unknown prime or factorization of N is used. Reject a wrong candidate that is not a unit square. Complement the two roots by N/r modulo n* to accommodate either factor. A constant-size restricted-HH menu (or a constant number of single-residue calls) costs soft K since n*>=K^(1/3) and the beta^(n*²) order guard is inherited. The interval parameter may remain a fixed constant times K, so no extra power-sized threshold is introduced by the constant palette.

### The even paired pole is natural in the AW variable

For one pair set u_i=c*rho^i and

    D_i(delta)=(1+delta)²-u_i*(1+delta)*Z+u_i².

Then its total hit count is

    [delta^0]delta*sum_i [2(1+delta)-u_i Z]/D_i(delta). (2)

The numerator/denominator are symmetric in x,x^-1. Weighting (2) by w2 gives the squared-tag coefficient. Both can therefore be targeted by a symmetric paired AW computation; an antisymmetric derivative distinguishing +/-j is unnecessary for this consumer. Repeated pair roots or multiple clock hits across different rows cause no problem: counts retain their original multiplicities and remain below the good characteristic. Equation (2) is a formal residue specification, not a paid singular inverse.

## 3. Primitive four-root invariant and a proved quartic palette

For g=1 put m=3^e=K/2 and define the CANONICAL INTEGER weight

    kappa_j=[(j+N/j)²]_m
            =[N*(a+b)²*(ab)^-1]_m.              (3)

All inverses and reduction in (3) are public integer operations modulo m. The second formula follows from j²=bN/a mod m. Compute the canonical residue first, then embed that small integer as a weight in B. Replacing it by the rational expression in B would set N=0 at the hidden prime and destroy its arithmetic information.

The weight is invariant under BOTH j->-j and j->N/j, and hence under the corresponding coefficient swap a<->b. At a good primitive hit, the exact content-one theorem gives j=R mod K, so

    kappa_j=[(P+Q)²]_m=:kappa.

Consequently an acquired primitive-bank pair (V,U_kappa)=(d,d*kappa) with d nonzero has an orientation-free decoder. It does not require selecting one root from a formal four-root packet.

After the norm/coordinate/small-integer validator obtains kappa, enumerate the unit solutions of

    j^4+(2N-kappa)j²+N²=0 mod m.                (4)

Both true factor residues solve (4). To count and acquire them, first put y=j² and Delta=kappa*(kappa-4N). The substitution

    (2y+2N-kappa)²=Delta

is invertible between quadratic y-roots and square roots of Delta. Since N is a 3-unit, kappa and kappa-4N cannot both be divisible by3. For any residue Delta modulo 3^t, its square roots number at most 2*3^floor(t/2): a nonzero even valuation 2v<t gives at most 2*3^v roots; the zero residue gives 3^floor(t/2). Every unit y has at most two square roots j. Thus at level t the quartic has at most

    4*3^floor(t/2)

unit roots. An explicit 3-adic tree starting from j=1,2 modulo3 and testing the three next digits has total nodes O(3^(e/2)) by summing this geometric bound. All tests use O(log N)-bit integers. This is a worst-case soft sqrt K tree bound, including highly ramified Delta and kappa=0; intermediate roots can die at later levels, so no bound purely in the final output size is asserted. No nonsingularity assumption is hidden.

Each root modulo m has exactly one ODD lift modulo K=2m. The resulting palette therefore has S<=4*3^floor(e/2)=O(sqrt K) unit residues modulo K and contains the smaller factor P as well as Q. For a nonempty palette, retain an explicit fixed constant C>=4, so S<=C*K^(2/3) and, more sharply here, S<=4*sqrt K. Restricted HH with its actual order guard costs soft K: choose r=ceil(16*C*K/S), giving Sr=O(C*K+S). Its baby count is O(1+S^(3/2)/(16*C^(3/2)))=O(K^(3/4)), below the supplied native order range. An empty wrong-attempt palette is rejected before this parameter division. All lattice/label inputs and candidate generation are paid. No primitive pole coefficient was acquired by this decoder.

**Scope:** (3)'s full-m provenance uses g=1. The full weighted bank gives only j=R mod n* for arbitrary content; it does not automatically give kappa modulo m. Also formal invariance under swapping does not license adding coefficient-swapped rows with the same clock: they may violate the correct-bin weighted norm bound. A four-root norm algorithm must retain actual covered row/window metadata or prove coverage and tag correctness for its augmentation. The conditional decoder above assumes an actual good pair (d,d*kappa); invariance alone does not supply it. A primitive subbank can have d=0 and then must be declined/handled by the full cover.

## 4. Execute the finite AW connection identity

Primary source read at the formula: Ismail–Stanton, [*Expansions in the Askey–Wilson Polynomials*, 21 March 2014 author PDF](https://www-users.cse.umn.edu/~stant001/PAPERS/AndrewsFormFinal.pdf), equation (2.4), page5, and Proposition2.1/Theorem2.9 for the surrounding finite basic-hypergeometric expansions. The exact source relation becomes, after clearing its row-dependent normalization,

    (c*x,c/x;rho)_h
      =sum_(k=0)^h binom(h,k)_rho*(c/d)^k
           *(c*d*rho^k;rho)_(h-k)*(c/d;rho)_(h-k)
           *(d*x,d/x;rho)_k.                    (5)

All remaining q-binomial divisions are only by factors 1-rho^t, t<=h, which are actual native units. In particular the source's (c*d;rho)_h normalization is NOT inverted. Clearing the finite identity makes it valid at the very collisions under investigation, over the composite ring. No orthogonality, positivity, analytic q-limit or auxiliary root of unity is imported.

### Force a known short spectral index, rather than assuming the unknown hit index

Choose any known 0<=r<=K with r<h and set d=rho^-r/x. This is an acquired unit. Then (d*x;rho)_k=(rho^-r;rho)_k is identically zero for k>r, so (5) is a genuinely short r+1-term expansion. This avoids supplying an unknown q-logarithm as a q-Racah spectral index.

However, write y_+=c*x, y_-=c/x. Every surviving term has the SAME factor

    L_r=(y_+*rho^r;rho)_(h-r)*(y_-;rho)_(h-r).    (6)

Indeed its first long factor has exponent interval k-r,...,h-r-1 on y_-, and its second r,...,h+r-k-1 on y_+. Their shared intervals are 0,...,h-r-1 and r,...,h-1 respectively.

Removing this common factor FORMALLY before native specialization gives the exact short identity

    sum_(k=0)^r binom(h,k)_rho*(y_+*rho^r)^k
         *(rho^-r,rho^-r*x^-2;rho)_k
         *(y_+*rho^h;rho)_(r-k)
         *(y_-*rho^(k-r);rho)_(r-k)
      =(y_+;rho)_r*(y_-*rho^(h-r);rho)_r.         (7)

The formal cancellation proves a polynomial identity; it does not authorize dividing by a possibly zero L_r in B. Thus the small q-Racah/AW expansion computes exactly the two FRINGES of the original product. The remaining paired norm (6) has horizon h-r, still Theta(h) for r<=K and h~K^(3/2).

This uses the actual c0,ell and normalized root pair, including their stationary conic relation. That relation does not remove L_r from (5); the displayed factorization is exact for those values. A different arithmetic identity exploiting the conic may still help, but cannot be credited to this connection formula alone.

## 5. Execution cost, pole preservation and remaining handoff

For one pair all short coefficients and factors in (7) can be acquired by q-binomial recurrences and prefix/suffix product arrays, with only certified short q-factorial inverses. Row-dependent factors are multiplied, never divided out. Building its full r-term evaluation costs soft r by these finite methods; a two-point q-product evaluator may compute its RHS in soft sqrt r. Across the actual J-row bank, the two fringe products/flags have a shared engine cost soft(J+sqrt(Jr)). At r<=K this is soft K, including exact endpoints. Proper norm/coordinate gcd branches are classified; a global nonaxis endpoint equality has the explicit nonzero scalar label ell+a+bN-H*i (with i the ORIGINAL signed index), using the same |b|N dominance as the already paid nonaxis carry screens. Such a terminating extractor, if used, is paid once. Alternatively a correct-bin fringe hit gives the actual factor-tag consumer; wrong bins retain bounded validation.

If all fringe values are certified units, removing them preserves original zero/nonunit and additive residue predicates, but it does not evaluate L_r. The short transform therefore gives paid boundary removal, not a contraction of the residual bulk. Taking r of order h to shorten that bulk would require a correspondingly long sum/fringe query and restore the old scale. Iterating fixed-r stripping has its repeated-query cost and yields no proved exponent gain.

For the new even target, a collision inside the common factor still contributes to (2) with its squared tag; discarding L_r discards that contribution. The source normalization cannot be treated as a harmless unit at such a point. The four-root kappa consumer can likewise accept an actually acquired invariant pole statistic, but does not turn the symmetric norm value or its unevaluated connection coefficients into that statistic.

The completed baseline for the original pure weighted bank remains soft K^(5/4), via all row values, exhaustive norm/coordinate flags and the common-tag HH consumer. The new output alternatives here are **even squared tags** (all contents/axes, two-root decoder) and **primitive swap/sign kappa** (soft-sqrt-K quartic decoder). The executed AW short-index specialization still retains its long collision-bearing factor. No faster whole-bin pole supplier or sixth-rate factoring algorithm is established.
