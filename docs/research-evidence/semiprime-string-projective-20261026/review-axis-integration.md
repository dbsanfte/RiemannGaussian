# Primary-agent review: axis transport and integration

26 October 2026. Independent symbolic review of the axis report, plus
integration against the projective and singular-recurrence reports.
Scoped PASS after the open-interval and exact odd-gcd clarifications.

For a=k, lambda=tk, the normalized original leaf is
1-beta^(k(t+1-kI))=1-rho^e. Odd t is coverage-safe because the actual
prime P is odd and k even. The stationary t=[-P]_k has e=1-P !=0 and
I=(P+t)/k<=ceil(B/k)+1 for P<=B. The new query explicitly omits literal
exponent zero; all other leaves retain their own short integer decoder.
It need not equal a smaller retained original scalar family.

For odd m|k, odd t=v modm means t=v_odd+2mj. Since 2m divides k,
j-(k/(2m))I runs through consecutive integer blocks with no gaps or
repetition. There are (k/(2m))(2M_B+1) exponents. Thus the common-base
product has length O((B+k)/m); at most one literal exponent is omitted.
Joint evaluation of S such progressions has the stated soft
S+sqrt(S(B+k)/m) cost. Restricting I modm instead keeps O(k) starts
and O(B/(km)+1) clock length, giving soft k+sqrt(B/m). Both charge
the supplier separately and make no factor-tag inference from aliases.

For any useful odd-axis leaf, e is even and q^(e/2)=(rho^e)^(k/2)=1.
The original kernel leaf 1-q^(-e/2) differs from 1-q^(e/2) by the unit
-q^(-e/2), so its nonunit predicate is preserved. The literal label stays
nonzero. The bound |e/2|<=(B+3k)/2 follows from M_B<=B/k+2. Modulo any
odd m|k, e/2=(t+1)/2, with 2 inverted only modulo that odd integer m.
No hidden local group order is inverted or assumed coprime to k.
The proof applies to accidental aliases and saturated global hits as well
as stationary ones. It is a one-way transport, not equality of the whole
axis/kernel predicates and not acquisition of a residue.

The public +/-1 controller uses m powers of 3 and cap c k²m. Its exact
certified subclass uses g_odd=max(gcd(P-1,k/2),gcd(P+1,k/2)); the even
version differs by the harmless factor two, now stated explicitly. Each
query costs soft k, and there are logarithmically many. The same operation
already follows from known-residue integer AP products, so no novelty or
all-semiprime coverage is attributed to it.

The mod9 seed table has correct products and only seeds 2,4,5,7. Lifting
one unit seed and taking the complementary factor residue preserves both
seeds, so N modk alone does not force large +/-1 ramification. This is
only a necessary-congruence statement. The actual prime family 23 mod36
has v3(p-1)=0,v3(p+1)=1 and remains 11 mod12, so the prior size and
odd-order compatibility proof applies unchanged. BMOR Theorem 1.2 with
phi(36)=12 gives a dyadic increment eventually greater than log(2x),
ensuring a prime in the OPEN interval. The old native-k and P/k² growth
bounds remain exact. This defeats the specific coverage certificate, not
all AP tests: a multiple or accidental alias may still produce a factor.

Integration: the PGL2 matrices close exactly but their cocycles are
formal units and endpoint data. The covariance identity has the correct
orientation: P_(y/q)(delta,qY) is the product over clock indices 1..h,
so f(x_h)P_y=f(x_0)P_(y/q)(delta,qY). All interior marked factors cancel
identically, not merely their zeroth values. No positive collision count
or row mask follows from that identity alone.

The Hasse gradient identity has coefficient d-1, sign - and factor y_j/A
as required. It is evaluated by the actual scalar circuit, with y_j formal
and q fixed; derivative through the beta-label construction is not used.
All formal inverse constants are units. The full-mask refinements retain
the scalar baseline; one nonunit path already factors at that baseline.
The README therefore distinguishes exact compatibility/overhead progress
from the still-unproved whole-family softly linear acquisition target.
