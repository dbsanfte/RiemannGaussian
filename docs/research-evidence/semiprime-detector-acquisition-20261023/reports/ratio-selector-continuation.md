# Ratio-selector continuation for the explicit AP catalog

23 October 2026. Scratch only. This tests specific choices in the acquired catalog, rather than assuming the unrestricted fraction alphabet must be enumerated. No all-input arithmetic selector was obtained. There is a precise limitation for selectors preserving the catalog's residue-wise universal coverage, as distinct from a lower bound for an N-specific factoring algorithm.

## 1. The denominator is a coefficient invariant

Use M=r^4 and the explicit true-row relation

    M sigma=a c^2 P+B c+C Q,
    1<=c<r, P,Q>16r^2, C!=0.

Reducing modulo c gives M sigma=CQ modulo c. Both M and Q are units modulo c. Consequently

    gcd(c,sigma)=gcd(c,C),
    denominator(sigma/c in lowest terms)=c/gcd(c,C).       (1)

The equality of gcds is stronger than just saying gcd(c,sigma) divides C. It holds in the signed-C convention too.

For a fixed a,C,s, every legal integer lift is B'=B+kM. Its true seed is sigma'=sigma+kc, hence

    sigma'/c=sigma/c+k.                                 (2)

Thus choosing a different centering of B cannot change the fractional part or denominator at all. It can bring the ratio into any specified interval of length one only if the required k is acquired; even that does not turn a noninteger ratio into an integer.

In particular, a selector aiming at integer ratios must arrange c|C. A selector aiming at reduced denominators <=D must arrange c/gcd(c,C)<=D. These are additional exact arithmetic conditions, not consequences of the original Dirichlet bound.

## 2. Different Dirichlet representatives: the exact additional index

For a fixed AP residue s, put alpha=s^2*N^(-1) modulo H=r^2. All Dirichlet candidates lie in

    L_s={(a,C): C=a*alpha modulo H}, det(L_s)=H.

Requiring an integer ratio additionally restricts to C=0 modulo c. This sublattice has index c in L_s, hence determinant cH: the vector (0,H) makes the C-coordinate surjective modulo c because gcd(c,H)=1. For a prescribed noninteger fractional part, the corresponding condition is an affine congruence in C modulo c, of the same index when its numerator/denominator is compatible with c.

The original rectangle has A*T<H and guarantees a point using the A+1 circular-gap argument. Repeating that argument for C=cD gives only

    |C|<=c*floor(H/(A+1)),

rather than |C|<=T. The corresponding area comparison would take A'+1=c(A+1), hence A'=c(A+1)-1, to restore the old C scale. Its straightforward coefficient-box enumeration grows from O(r) to O(cr); for c comparable with r that is O(r^2). This is only a box/index charge: once A' reaches r, it also loses the original unit-a and unique-AP-label guarantees, so it is not a proved replacement source. Determinant alone is not a nonexistence proof; the counting result below supplies the precise residue-wise limitation.

Changing C by jH while retaining a and s gives another legal root row after recomputing B. For an integer ratio one now needs

    C+jH=0 modulo c,
    j=-C*H^(-1) modulo c.                               (3)

A common short list of j therefore still needs an additional covering proof. Computing the right j from the unknown c would already select the multiplier. Taking j through c consecutive values works, but pays c variants; a polylogarithmic lift bound does not follow from the original gap argument.

## 3. A finite exact failure of integer forcing inside the original box

The balanced window A=1 is especially rigid. It has a=1 and a unique signed representative 0<|C|<=floor(H/2) for each s. There is no alternative Dirichlet representative within the stated box. Reversing both signs, if allowed, does not change the denominator.

An exact semiprime instance is

    r=43, H=1849, M=3418801,
    P0=59168, P=59447, Q=59747,
    N=3551779909 <=r^6,
    A=floor(sqrt(N)/P0)=1, T=924.

Both primes exceed 16r^2 and lie only in this covered dyadic factor window. This same instance also satisfies the strong prepared-base premises: beta=4 has exact prime local orders (P-1)/2=29723 and (Q-1)/2=29873, both odd and greater than 16H=29584. They are coprime, their product is the exact global order and exceeds 256r^4, and raising beta by H or M preserves both local orders. Thus the counterexample lies in the prepared hard-order regime, not just the source geometry. The true rows in the two orientations are:

    factor    c     s      C        B       sigma   sigma/c
    59447    41    345    331    1082824      48      48/41
    59747    28   1420    116    -453996      12       3/7

Each row satisfies CN=s^2 modulo H, the two exact root/derivative congruences, and M*sigma=c^2*factor+B*c+C*other_factor. No B lift makes either ratio integral. This refutes the proposed conclusion that the original representative freedom and centering alone always force an integer ratio, even for actual semiprimes. It is one algebraic counterexample, not a runtime experiment, an asymptotic hardness claim, or a proof that another menu cannot be tailored to N. An exact replay is retained in `replay_ratio_counterexample.py`, with its output in `ratio-counterexample-replay.json` in this directory. It recomputes all row data, verifies zero root/derivative/source residuals, verifies the two reduced denominators, and checks both displayed factors and both prime local orders by complete trial division. It also asserts the exact base-4 local/global orders and all displayed strong setup bounds. The replay passed.

## 4. Precise residue-wise limitation for any common polylog menu

Here is a stronger count for the exact selector class being attempted. It does not treat row metadata as independent.

Retain the AP catalog s=1+rt and its residue-wise guarantee: for EVERY pair (s,c), 0<=t<r, 1<=c<r, at least one descriptor over that s should give a ratio from one common menu R. The original coverage proof indeed covers all these unit-residue labels, not merely an already known divisor of N. Each descriptor is assigned ONE AP label s, as in the actual catalog with a a unit modulo r; if a polynomial is reused at several labels, count each labeled instance. Allow any such unit a, any legal B lift, and any number of labeled descriptors per s, but require nonzero |C|<=V, with V<=r^2*(log r)^K for a fixed K. This includes the original catalog and polylogarithmically enlarged C lifts. Let J be their total number, L=|R|, and Pi be the number of primes ell in (r/2,r).

For c=ell prime, (1) says the ratio denominator is either 1 or ell. At most L such primes occur as reduced denominators in R. For every remaining ell, a successful descriptor must have ell|C.

One nonzero C has at most

    b_V=floor(log(V)/log(r/2))

distinct prime divisors in (r/2,r). Hence the number J_s of descriptors over any particular s must satisfy

    b_V*J_s >= Pi-L,
    J >= r*(Pi-L)/b_V, if b_V>0.                       (4)

If b_V=0, use the undivided inequality 0>=Pi-L instead; no division by
zero is intended.

For the stated V, b_V<=2 for sufficiently large r; the finite threshold is explicit from (r/2)^3>V. Since Pi is of order r/log r, a common polylog-sized R and residue-wise coverage require J=Omega(r^2/log r), beyond soft O(r). More generally (4), with its actual finite Pi and b_V, requires no asymptotic estimate to check a concrete scale.

The count also extends to descriptor-specific menus R_v, with no common-menu assumption. A labeled descriptor v can cover a large prime multiplier c only when c divides C_v (at most b_V primes), or when some fraction in its own menu has reduced denominator c (at most |R_v| primes). Summing these capacities over the labeled descriptors gives the necessary finite inequality

    b_V*J + sum_v |R_v| >= r*Pi.                       (5)

Thus descriptor volume J and explicit root-test/menu volume sum_v |R_v| cannot BOTH be soft O(r) under this stronger universal coverage requirement and polynomially bounded V. The choices of descriptors and menus may depend arbitrarily on N: the count still applies if they are required to cover every AP-residue/multiplier label. It does not apply to an N-specific selector required to cover only an actual divisor. This is a representation/coverage limitation; it is not a lower bound for arbitrary quadratic polynomials, implicit menu algorithms, or a factorizer.

This applies to simultaneous approximation just as to the one-dimensional gap rule: even a clever selection of (a,C) within this coefficient bound cannot give the STRONGER residue-wise universal small-menu assertion at soft-r descriptor volume. B lifts add no denominator freedom. A common scalar divisible by every c can remove denominators, but then |C| grows exponentially in r, outside this coefficient bound; it can produce exponentially large integer ratio values and supplies no small-menu bound.

Crucial scope: fixed N has only its actual two hidden prime divisors. An algorithm exploiting arithmetic restrictions of those actual divisors might select successful rows/menu without covering every unit-residue label. Equation (4) does not rule that out, and is not a general factoring or circuit lower bound. It shows precisely why the original universal Dirichlet/AP coverage argument cannot simply be strengthened to a common polylog fraction menu by these representative, centering, or bounded simultaneous-approximation choices.

## 5. What would still be constructive progress

A useful selector must now do at least one of the following concretely: exploit N to identify a thin subset of the possible (s,c) labels; use a decoder that handles the varying denominators without an explicit common menu; or change the representation enough that (1)/(4) no longer describe the acquired family. Merely centering B or adding a bounded number of Dirichlet lifts does none of these.

There is a quantitative positive partial consumer. If one witness has c>=r/L0 and c/gcd(c,C)<=D, then |sigma/c|<3.5L0 and its reduced denominator is <=D. Acquire the common menu of all reduced u/v with 1<=v<=D and |u|<=ceil(3.5L0*v). Its size is O(L0*D^2), and the preceding direct quadratic-root decoder factors in soft O(r*L0*D^2). In particular polylogarithmic L0,D give soft O(r), with an actual explicitly acquired menu rather than an unspecified one. The case D=1 and c comparable to r needs only finitely many integer ratios, or finitely many B shifts making sigma=0. No coverage theorem forcing this large-gcd condition was obtained. The exact limitation above concerns its universal selector, not the usefulness of its consumer.

No new primary theorem is needed for these elementary identities and counts. The primary small-root and rational-divisor references, and the distinction from the inherited one-fifth centering route, remain in arithmetic-detector.md. No repository edits were made.
