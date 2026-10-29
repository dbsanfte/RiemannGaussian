# Cartesian Gauss-basis projection: a carry-free complete edge query

26 October 2026. Read authoritative `formal/AGENTS.md` tail and `dense-box-coverage.md`. Scratch paper derivation; no tests, code, or repository edits. **Constructive result:** replace each unknown-index rectangle by a public Gauss-basis Cartesian grid, with no per-point canonical phase in the QUERY. An elementary public cell filter removes every literal short-shift leaf and preserves a guaranteed cell. The close edge has shift 0..4k uniformly, including unbalanced factors. Descriptors cost soft k, but explicit incidence count remains soft k² and scalar evaluation is UNPAID. No faster factoring/query bound is claimed.

## 1. Public basis cells and exact acquisition

Use N=PQ, P<=Q, N<=k⁶, k=2*3^e>16, H=k², N>256H², P,Q>16H, and the prepared unit beta, q=beta^H with both local orders above16H. Enumerate unit colours j mod k and powers of two p0 in [8H,sqrt N]. Set q0=N/p0. At least one scale has P/2<p0<=P, hence actual and public weighted norms differ by at most a factor2.

Gauss-reduce the known index-k lattice Lambda_j in the rational norm

    ||(a,b)||_0²=(a*p0)²+(b*N/p0)².

Obtain a reduced basis u,w with lengths ell1<=ell2. Its weighted covolume is kN, and its angle lies between60 and120 degrees. Thus

    kN <= ell1*ell2 <= (2/sqrt3)*kN.

This uses BOTH reduced basis vectors; it does not assert both meet the old hyperbolic cutoff. These are new auxiliary rows.

There is NO thin stage to evaluate. For a nonaxis lattice vector, norm²>=2|ab|N>=2N. An axis vector has coordinate divisible by k. With p0>=8H and p0<=sqrt N, its norm is at least8k³>=8sqrt N horizontally, or ksqrt N vertically. Therefore every basis vector has length at least sqrt(2N).

Put R=2k*sqrt N and acquire exact integers

    A=ceil(R/ell1), B=ceil(R/ell2).

These ceilings are computable from rational squared norms by exact integer comparisons/square roots; no real arithmetic oracle is needed. Then A,B<=ceil(sqrt2*k)<2k and the Cartesian coefficient box has

    2sqrt3*k <= n=A*B <= (4+2sqrt2)*k+1 <7k+1.    (1)

Indeed the lower bound uses R²/(ell1 ell2), while the upper uses the product lower bound and the individual length lower bounds.

Acquire ONLY the generator phases lambda_u,lambda_w canonically in [0,H), their labels E_u,E_w, and units X=beta^E_u,Y=beta^E_w. The implicit nodes are

    Z_(r,s)=X^r Y^s,
    0<=r<A, 0<=s<B.                              (2)

All basis/phase/power data cost polylog N per cell. O(k log N) cells therefore have soft-k total descriptor acquisition. Expanding (2) still has Theta(k) nodes per cell and soft-k² incidences overall; that is not counted as acquired input.

## 2. Uniform stationary close edge, with no pointwise carry

At the true colour and a correct factor-size scale, the generator phases give actual INTEGER stationary indices

    H I_u=a_u P+b_u Q+lambda_u,
    H I_w=a_w P+b_w Q+lambda_w.

Consequently each node (2) has exact local equality Z_(r,s)=q^J_(r,s) mod P at the UNWRAPPED integer

    J_(r,s)=r I_u+s I_w.

No canonical phase of each grid point is used or needed. This is a linear character on a Cartesian index box, not the old Beatty carry representation.

Using actual norm <=2 times guessed norm gives

    |I_u| <=2sqrt2*ell1/H+1,
    |I_w| <=2sqrt2*ell2/H+1.

Since (A-1)ell1<R and (B-1)ell2<R, the entire J-span is strictly less than

    8sqrt2*k*sqrt N/H+4k <=8sqrt2*k²+4k.          (3)

Among n>=2sqrt3*k integer values, either two coincide or an adjacent difference is less than4k, for k>16: multiply by n-1 and use 8(sqrt3-sqrt2)k²-8k>0. Thus distinct grid points have an ordered integer difference

    0<=h<=4k, q^h Z_(r,s)=Z_(r',s') mod P.         (4)

This proof covers arbitrary prepared balance via the factor-size scales. It does not sort unknown indices operationally. Also (3)+4k<16H for k>16, so any attempted literal-identity contradiction stays inside the short-order guard.

## 3. A public nonliteral filter, without fixed-dimensional ILP

For the cell acquire the exact coordinate span

    a_span=(A-1)|a_u|+(B-1)|a_w|,
    g=gcd(j-1,k).

Retain it only if

    a_span<=H and a_span<H/g.                     (5)

This uses just descriptor arithmetic. The correct cell always passes: actual coordinate span is at most twice its public norm bound divided by P, hence

    a_span<4R/P=8k*sqrt N/P <H/2,

using P>16H and sqrt N<=k³. Moreover q^((P-1)/g)=1 mod P implies g<P/(16H). Therefore g*a_span<sqrt N/(2k)<=H/2. Both inequalities in (5) follow strictly.

To prove zero-safe scope for EVERY retained cell, write a grid point's canonical phase as lambda_v, and its acquired algebraic carry as tau_v=floor((r lambda_u+s lambda_w)/H). This is a proof device, not an expanded query input. Then its unwrapped exponent is Etilde_v=rE_u+sE_w=E_v+H*tau_v, with 0<=tau_v<4k.

For two points with different b, canonical E difference has magnitude greater than N-a_span-H>=N-2H. Subtracting a shift Hh and the carry difference, for 0<=h<=4k, leaves magnitude greater than N-(8k+2)H>0. For equal b, the difference Delta a is a nonzero multiple of k. Modulo H their unwrapped label difference equals (1-j)Delta a. Divisibility by H would require |Delta a|>=H/g, contrary to (5). Thus every retained distinct-point comparison in (4), at EVERY tested h, has a nonzero integer beta-exponent gap.

At a proper gcd it factors immediately; a saturated equality uses a nonzero O(log N)-bit label and the inherited T_ext=soft N^(31/192), at most once before termination. This is an AUXILIARY leaf decoder, not an invented extension of the old low-product physical window. No whole-row deletion or self-comparison at the origin is needed; exclude only identical coefficient pairs.

## 4. Exact pure difference predicate; omit transposes

Do NOT add transposed cells to a bare product. In a general Gauss grid b_span can reach k or larger, so original differences with Delta a=0 may exist and their transposes can give literal edges. No Q-side global-zero guarantee is asserted. The original filtered cells already supply a guaranteed P-local NONUNIT, which is sufficient for the factoring/localization contract.

The complete current formulation uses ONLY the original cells for factor-or-nonunit coverage: (4) guarantees a P-local nonunit, sufficient to factor by the permitted proper/saturated consumer after localization. No global-zero guarantee at both primes is needed for that scalar NONUNIT predicate. Its pure difference form is

    product_(retained cells) product_(h=0)^(4k)
      product_(|r|<A,|s|<B,(r,s)!=(0,0))
                (q^h-X^r Y^s).                    (6)

Every coefficient difference occurs between actual box endpoints; its multiplicity in the ordered-pair product is positive. Dropping multiplicities preserves local zero bits over squarefree N. Thus (6) is a carry-free 3-dimensional finite geometric-box predicate with proved NONUNIT coverage and fully nonliteral leaves by (5). Equivalently use factors 1-q^(-h)*X^r*Y^s; the q^h prefactors are units. Omit the ENTIRE line (r,s)=(0,0) directly: its h=0 factor is the tautological zero, so it must not be removed by numerical division of a complete-box value. All other differences are realized by actual Cartesian endpoints (choose the positive and negative parts of each coordinate), and there are at most (2A-1)(2B-1)-1<4AB=O(k) of them per cell. No expanded point-pair table is present. Its original-cell filter is complete and sufficient for factorization; no transpose or Q-side equality is needed.

## 5. Cost and remaining acquisition

Descriptors, (5), and both generator roots cost soft k. The implicit difference roots in (6) are O(AB)=O(k) per cell, still soft-k² if all expanded. Enumerating every shift and difference gives soft-k³ candidates, not the target. For a supplied noncancelling difference (r,s,h), its integer stationary equation gives the already paid quadratic factor test; an accidental modular alias instead uses the existing factor/extractor consumer. Neither method selects that difference from (6).

The constructive reduction removes the canonical carry from the TARGET INPUT and turns the weighted coverage theorem into a Cartesian two-generator box norm with O(k) shift horizon. It does not yet evaluate that norm, find a sparse universally covering set of differences, or establish a faster query. A scalar nonunit oracle for cell-list and shift prefixes would allow logarithmic localization, followed by materializing only one O(k) cell and the old fixed-shift consumer. A global equality-to-zero bit alone is insufficient.

No new external theorem was needed beyond the inherited exact two-dimensional Gauss reduction. Ordinary Farey/shortest-vector coverage remains prior credit. The new finite grid, exact span/carry removal, and public filter are derived here, with the target scalar explicitly unacquired. This does not claim a universal lower bound against sparse projection, sail, tangle, or joint box-norm algorithms.
