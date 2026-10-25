# Independent gauge and paired-recovery review

23 October 2026. Scratch only. Reviewed `quadratic-carry-gauge.md` and equation (10) of `paired-label-selection.md`. No repository or frozen entries changed; no row scan or new examples were run.

**Result.** The integer gauge and endpoint identity are exact. The common row-center congruence produces separated translated rectangles, rather than an overlap/telescoping theorem. I did not acquire a new norm or multiplicative convolution in soft r. The paired arithmetic recovery is valid even for false candidate factors; its needed r-unit condition follows from the public labels, and can also be avoided in the divisibility proof altogether.

## Exact gauge and center separation

For fixed observed (a,b), write q(x)=a x^2+b x+e, B_C=2a t_C+b, D_C=d_b+4a k_C. Expanding the report's definitions gives

    q(t_C)=CN+M k_C,
    K=q(t_C+c)-M(k_C+sigma).

Thus j in [t_C+1,t_C+r-1] and tau in [k_C-4r,k_C+4r] retain the exact leaves, including canonical B and discriminant carries. The inverses involved are modulo 4a, where M is a unit; no group-exponent division is used. The O(r) observed branch metadata has O(log N)-bit entries and is legitimately acquired in soft r.

The report's fixed-branch congruence is correct:

    t_C=-1-b(2a)^(-1) modulo r.

Distinct fixed-a catalog descriptors have distinct B_C: equal B would imply C=C' modulo M, while |C-C'|<M. Hence distinct fixed-(a,b) row starts differ by a nonzero multiple of r, and their j-intervals are disjoint. This rules out literal horizontal interval overlap; it does not rule out a different shared norm algorithm.

The two center coordinates satisfy the sharper exact identity

    M*(k_C'-k_C) = (B_C+B_C')*(t_C'-t_C)/2 - N*(C'-C).

Here C'-C is a nonzero multiple of r and |B_C+B_C'|<=M. Consequently

    |k_C'-k_C| + |t_C'-t_C|/2 >= N*r/M >256r,          (1)

using N>256M from P,Q>16r^2. In particular, consecutive possible j-block starts differing by r have vertical-center distance greater than 255.5r; conversely, intersecting seed intervals require |t_C'-t_C|>496r. So the canonical ranges do not join neighboring rectangles along common short edges. All terms in (1) use exact integer carries. This is a source-specific support statement, not an operation lower bound or an acquired product.

The gauge reduces balanced a=1 to at most two clock formulas, but the translated two-coordinate mask still has one observed center per descriptor. Supplying those centers costs soft r; evaluating the resulting multiplicative translated-window query is a separate operation. The finite-cycle test in the sibling report is correctly restricted to its attempted root-of-unity norm and does not exclude noncyclic contraction. I found no additional source-preserving telescoping or native norm evaluation beyond that report.

## Paired equation (10): every candidate is a unit at r

Use the paired report's exact public labels

    d=nu*c^(-1) modulo r,  nu=N^(-1) modulo r,
    k_c=c*d,  H*ell=b_t*k_c+s,
    h=c*tau-ell,  P_cand=H*tau-b_t*d.

Since t=1 modulo r, b_t=-N modulo r. Therefore, for EVERY integer tau,

    P_cand=N*d=c^(-1)!=0 modulo r.                   (2)

Thus gcd(H,P_cand)=1 for false as well as true candidates. Also exact substitution gives Hh+s=c*P_cand.

More directly, the gcd recovery does not need to divide by H. Equation (10) gives P_cand|g(h), and the original integral identity is

    M*g(h)=a(Hh+s)^2+B(Hh+s)+CN.

Together with Hh+s=c*P_cand it implies P_cand|CN immediately. If P_cand is in the genuine positive factor window [P0,2P0), then P_cand>=16H>|C|. Assuming gcd(P_cand,N)=1 would force P_cand|C, a contradiction. The same window gives P_cand<N, so the gcd cannot be saturated. A proper gcd therefore follows from any acquired bounded integer solution of (10), irrespective of whether its candidate P_cand is prime or the original hidden factor. No prepared-base collision is needed for that consumer. Acquiring such a solution over the full family remains unproved.
