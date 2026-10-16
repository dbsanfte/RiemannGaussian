# A denominator-m redesign gives one geometric carrier but a cubic-length stream

2026-10-16. Exact classical redesign and failed fast-clock promise. Allowing a denominator divisible by m can bypass the literal denominator-one carrier obstruction: there is a single length-m geometric target carrier with guaranteed own-factor coverage. Its complete rectangular product, however, tiles a single stream of length mL=Theta(m^3), whose established acquisition cost is softly O(m^(3/2)). No improved query bound or lower bound against a new evaluator is claimed.

## 1. Explicit family, setup and coverage

Let m be an odd prime not dividing the balanced semiprime N=P Q. Put d=m^2 and h=(m-1)/2. Let gamma be the routed unit base and g=gamma^m. For each original tag 1<=j<m choose

 t=m, a=0, b_j=centered(-N j^(-1) mod m),
 c_j=(N+j b_j)/m.

The inverse is public modulo the prime m; c_j is integral. These values instantiate the general native denseRow/liftRow constructor at denominator t=m, positive branch. They satisfy the exact quotient relation

 m^2 c_j-j m b_j+j^2 a=N t.

The current denseRows list emits only 1<=t<m, so this is a REDESIGNED generator using the already defined constructor, not a claim that its existing list theorem already emits these rows. The public giant exponent is

 E_j=tN+a+mb_j-2aj=m(N+b_j).

Since j inversion and multiplication by nonzero -N permute F_m^*, the b_j run over all nonzero centered residues in [-h,h]. Consequently the actual target powers form ONE geometric progression with one omitted point. This structure is exact and input-dependent; it does not contradict the denominator-one energy theorem.

For the own tag j=P mod m, b_j=-Q modulo m. Hence

 i_P=(Q+b_j)/m is an integer,
 E_j-m^2 i_P=mQ(P-1).                              (1)

If the local gamma order divides P-1, this is a genuine P-field collision. The analogous Q-field collision uses j=Q mod m. Under the inherited balanced condition max(P,Q)<=sqrt(3/2)*sqrt(N) and N<=m^6, both indices are positive and less than L=2m^2+2. Thus this redesigned family has actual arithmetic coverage with the same public long length, not merely convenient examples.

Constructing all inverses and centered b_j costs softly O(m) modular arithmetic; alternatively the full centered interval below needs no inverse list. Powers g and g^(-N) cost O(log N) ring multiplications. All exponents and row coefficients have O(log N) bits. Group inversions are of known units; an initial gcd with gamma is factor-aware. The dense row construction uses exact integer divisions, not inversions modulo the hidden fields.

## 2. Exact product tiling and the cost it exposes

Add the missing b=0 as a supplementary target, obtaining all m centered residues. This is an enlarged collision query, not asserted equality with the native m-1-row norm; the additional leaves are handled separately below. For i=0,...,L-1 set n=mi-b. These pairs biject onto the single integer interval

 -h <= n <= mL-h-1.

Indeed successive i blocks are adjacent, disjoint intervals of m integers. With K=mL and normalized factors, the complete product is EXACTLY

 product_(b=-h)^h product_(i=0)^(L-1) (1-g^(-N-b+mi))
       = product_(r=0)^(K-1)(1-g^(-N-h+r))
       = P_K(g^(-N-h);g).                           (2)

The unnormalized collision factors differ only by explicitly known unit powers. Equation (2) is not a nearlinear acquisition algorithm: K=Theta(m^3), so the established division-free geometric baby-step/giant-step product evaluator costs softly O(sqrt K)=softly O(m^(3/2)). It constructs a degree-O(sqrt K) block polynomial and evaluates it at O(sqrt K) geometric points using monic multipoint trees. No full length-K coefficient vector is required, but the square-root cost remains.

This implementation can be ring-safe without assuming 1-g^k is a unit up to K. Build the small block by product trees and use monic division/evaluation; giant-point differences are not inverted. Geometric block construction/evaluation has the usual polynomial-multiplication soft cost. If coefficient formulas using geometric denominators are substituted, their unit conditions must be checked and a proper gcd returned; the long prefix can cross a hidden order and its denominators are not globally licensed. The deterministic monic implementation avoids that issue. With arithmetic multiplication cost for O(log N)-bit residues absorbed, the bit bound is soft O(m^(3/2) log N), not soft O(m log N).

There is also a safe exact relation to the original missing-point product: its missing class is a separate length-L q-product at b=0. Dividing (2) by that class is licensed only if its value is a unit; a proper nonunit can give a factor, and a saturated class needs the leaf analysis. No cancellation by a possibly zero product is assumed.

## 3. Additional and saturated leaves on the retained large-order branch

Every enlarged leaf is of form 1-g^(n-N), with n in the interval above. A proper gcd is a factor. To check that an added b=0 leaf cannot introduce an unrecoverable GLOBAL zero on the retained branch, let D be the global order of gamma. The inherited exact local orders are distinct primes R_P,R_Q>16m^2. Thus D=R_P R_Q>256m^4, gcd(D,m)=1, and D divides (P-1)(Q-1).

A global zero gives D dividing m(n-N), hence D dividing N-n. Subtracting phi(N) gives

 D divides P+Q-1-n.

For balanced N<=m^6 and L=2m^2+2, the absolute value on the right is O(m^3), less than D for sufficiently large m. Therefore n=P+Q-1. The factor sum is n+1, and the quadratic with product N recovers P,Q by an exact integer square root. Thus ANY global-zero leaf in the enlarged interval has the required arithmetic recovery on this retained branch. A product/splitting controller can use the scalar interval product and logarithmic restrictions; every restricted interval is another single geometric product. This observation does not supply that product at a faster clock.

The exact global-order and prime-order premises are inherited proof-side facts. They are not given to the algorithm. Outside the retained large-order branch this paragraph does not replace the original routing/short-order analysis or prove a new universal factoring algorithm.

## Outcome

The t=m redesign really yields cheap setup, one geometric carrier and guaranteed own-factor coverage. The carrier-cover obstruction is bypassed by changing the arithmetic family, rather than by reindexing its old rows. But the scalar norm becomes a length-Theta(m^3) q-Pochhammer query, so the established clock remains softly O(m^(3/2)). A genuinely faster evaluator for (2), or a different redesign with a shorter acquired stream, would still be required. There is no operation lower bound here: structured or factor-only algorithms could improve it. No prior bundle, native file or backend was modified, and no build or numerical experiment was run.
