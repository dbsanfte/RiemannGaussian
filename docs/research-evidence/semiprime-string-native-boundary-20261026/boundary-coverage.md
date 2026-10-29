# Native Young/Farey boundary coverage: executed scaling and axis tests

26 October 2026. Read the protected string-theory proposal, the frozen
scalar catalogue/swap contract, and trace-recurrence. Paper-only;
no tests, numerical campaign, implementation or repository edits.

**Outcome.** No covered soft-sqrt(k) phase bank with the original
O(k^(3/2)) clock was proved. Two specific missing implications were
executed rather than assumed: radial scaling does not land on a Young
corner and can enlarge the clock; in a precise actual unbalanced-factor
regime EVERY nonaxis stationary certificate is outside the original
window. A primitive corner bank also certifies only a small subset of
PUBLIC colours, but that is not a lower bound for the one actual factor
colour of a fixed N. These distinctions prevent treating the small
uncoloured Young boundary as a proved factoring cover.

## 1. Exact target and what the proposed saving would require

Use the authoritative scalar-catalogue hard branch:

    k=2*3^e>16, H=k^2, N=PQ<=k^6, P<=Q, P,Q>16H,
    D=ceil(sqrt(kN)), M=ceil(4D/H)+2.

Both beta and q=beta^H have odd local orders >16H. Roughness or a
Legendre/nonsplit orientation is NOT assumed. The original source
explicitly does not need cross-prime coprimality for this cover or its
leaf decoder. The complete signed clock is [-M,M], length<16H.
Rows have 0<|ab|<k or are the four axes (+/-k,0),(0,+/-k), and carry
ALL canonical phases 0<=lambda<H with lambda^2=4abN mod H.

At the correct stationary colour j=P mod k, a row certificate obeys

    a*j^2=b*N mod k,
    lambda=-a*j-b*N*jinv mod H,
    H I=aP+bQ+lambda,
    E-HI=(P-1)(bQ-a), E=a+bN+lambda.                 (1)

The j inverse has precision H. The phase is independent of the lift
of j under the lattice condition. A root of the conic alone is not
proof that this PARTICULAR phase is stationary at P.

Any nonzero short label E-HI, including from a new safe overset, has
the proper-gcd/once-only T_ext consumer. Public literal-zero deletion
is done BEFORE evaluation; the old witness-survival argument uses the
actual short signed interval and does not automatically extend to a
larger window. A boundary bank of total phase multiplicity soft sqrt k
and clock O(k^(3/2)) would fit the old joint engine inside soft k.
Neither the corner count nor a short descriptor proves its coverage.

## 2. Execute radial scaling, including its canonical phase carry

Given an admitted NONAXIS stationary row (a,b,lambda), scale by an integer d>0
with d^2*|ab|<k and put

    a'=d*a, b'=d*b,
    lambda'=d*lambda-H*floor(d*lambda/H).

This is a legitimate stationary conic row, with exact equations

    E'=d*E-H*c,
    I'=d*I-c, c=floor(d*lambda/H).                  (2)

It preserves the Fermat gap up to multiplication by d. Thus a literal
nonzero old gap stays nonzero at the scaled physical hit; it is not
safe to replace I' by dI while dropping the carry. The bound supplied
by the original certificate is only

    |I'| <= d*|aP+bQ|/H+1,

or, directly from (2), d|I|+d. To preserve the old horizon one needs
a new bound on d*|aP+bQ|. The original Gauss norm bound is for the
UNSCALED vector and does not supply it.

Maximal admissible d pushes |a'b'| into a thick boundary band, roughly
[k/4,k), but not onto a staircase corner. If a target Young corner is
(A,B), radial scaling requires

    A=d*|a|, B=d*|b|,
    A*|b|-B*|a|=0

and simultaneous divisibility. The small Young corner list contains
only its prescribed rays. Neither shortestness nor the stationary
congruence in (1) supplies this ray equation. Adding dyadic scales to
the SAME corners leaves their rays unchanged; adapting a corner to a
known witness assumes the unknown witness has already been located.

For nonzero coefficients, the maximal-scale size estimate is

    d*(|a|P+|b|Q)
       approximately sqrt(k)*(sqrt(|a/b|)*P
                                +sqrt(|b/a|)*Q).

It retains the old O(sqrt(kN)) size only under an additional slope/
balance bound. Gauss shortestness alone permits very unbalanced
coordinates, especially the axes treated next. No proof excluding a
different correlated boundary construction is inferred.

## 3. A precise actual-factor regime where nonaxis stationary rows fail

For EVERY actual signed nonaxis catalogue row, |a|<=k, |b|>=1 and
0<=lambda<H. Therefore

    |aP+bQ+lambda| >= Q-kP-H.                       (3)

Consequently, on any actual prepared semiprime satisfying

    Q-kP>H*(M+1),                                  (4)

NO nonaxis row, including every signed nonaxis Young corner and every
admitted radial multiple, has its stationary I in [-M,M]. This is an
actual N=PQ inequality, not a generic-root example or dimension count.
The old complete Gauss proof must then furnish an AXIS witness.
One convenient sufficient threshold is Q>=25kP: using
H(M+1)<=4sqrt(kN)+4H+4 and P>16H, the margin is positive.
The hard-branch upper bound Q/P<k^2/256 does not exclude this regime
for large k. A smaller-factor controller through only a constant
multiple of H would not exclude it either.

This does not prove that a nonaxis row has no ACCIDENTAL modular hit
in the short window. It proves that the existing all-semiprime
STATIONARY coverage theorem cannot justify deleting the axes there.
Proving useful accidental-hit coverage would be a new theorem, not a
consequence of the Young boundary identity.

The regime is not merely a formal choice of factor residues. Fix ANY
0<gamma<1/2, for example gamma=1/4, and take primes

    P in (64*k^(2+gamma),128*k^(2+gamma)),
    Q in (k^(4-gamma)/32768,k^(4-gamma)/16384),
    P=Q=11 mod12.

These dyadic intervals contain such primes for all sufficiently large
k by the explicit primary theorem below. Their products still lie
between k^6/512 and k^6/128, so the native least 2*3^e above N^(1/6)
is exactly this k. Also

    Q/(kP) > k^(1-2gamma)/4194304 -> infinity,

so (4) holds eventually. These examples have P/H tending to infinity;
they cannot be dismissed by enlarging a FIXED constant-times-H ordinary
small-factor prefix. This replaces the weaker constant-times-H example
in the initial draft.

Both primes are 11 mod12. Their odd-part generators have orders
(P-1)/2 and (Q-1)/2, respectively, with neither order divisible by 3.
CRT therefore supplies possible beta and q=beta^H with the same odd
local orders, both exceeding 16H. This asserts no forced continuing
outcome for a particular stronger controller, and no cross-prime
coprimality construction; the scalar stationary contract in Sections
1-3 does not require the latter. Nor does it exclude accidental useful
modular hits of a selected boundary. It is an actual-semiprime
obstruction to the claimed nonaxis STATIONARY-certificate proof.

Primary existence input: Bennett--Martin--O'Bryant--Rechnitzer,
*Explicit bounds for primes in arithmetic progressions*, Illinois J.
Math.62(2018),427-532, [Theorem 1.2, (1.10)-(1.12)](https://arxiv.org/pdf/1802.00085),
[author's published PDF](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf).
For modulus12 and x>=8*10^9 it gives

    |theta(x;12,11)-x/4| < x/(840 log x).

Thus theta(2x;12,11)-theta(x;12,11) is at least
x/4-3x/(840 log x)>log(2x) for all sufficiently large x. The increment
therefore cannot consist only of a possible prime at 2x, and each OPEN
dyadic interval contains a prime. Applying this to the two lower endpoints proves
existence in exactly the displayed factor intervals, not merely
infinitely many primes somewhere in that progression. No computations
of example primes, numeric campaign or unproved distribution hypothesis
are used.

## 4. Axis phase cost cannot be counted as four rows

For a horizontal axis a=epsilon*k,b=0, every phase is lambda=t*k,
0<=t<k. Its physical certificate is

    I=(epsilon*P+t)/k,
    t=-epsilon*P mod k.

Thus the correct phase depends on the actual factor residue. Before
pruning the complete scalar catalogue has k phase rows per horizontal
sign, not one. A stationary-colour subfamily may retain only unit-tag
phases, and public literal deletion removes ENTIRE rows; the following
tiling is therefore NOT asserted to be literally that family's scalar.

There are two precise legal interpretations. For the old complete
all-phase catalogue, restore the NONLITERAL leaves of any deleted row:
if E=H*i0 with i0 in [-M,M], then at every i!=i0 its difference is a
unit times 1-q^(i0-i), and 0<|i0-i|<=2M<16H. Those restored leaves
are certified units. Omit the literal leaf i=i0 BEFORE evaluation.
Restoring them consequently preserves both zero and nonunit predicates,
although it changes the scalar by a unit.

For a smaller stationary-colour/unit-tag phase family, completing to ALL
k phases is instead a SAFE FACTORING OVERCOVER. Every added literal
index is explicitly omitted; every other added leaf has its own nonzero
short beta label k*(epsilon+t-k*i). Added nonunits may be accidental,
but have the legal proper-gcd/global-annihilator decoder. Thus the
completion retains the guaranteed witness and licensed recovery; its
zero/nonunit bits need not equal those of the smaller family.

After this specified completion, rho=beta^k and q=rho^k give the exact
finite exponent tiling

    {epsilon+t-k*i : 0<=t<k, -M<=i<=M}
      =[epsilon-kM, epsilon+k-1+kM] intersect Z.

Each exponent occurs once. Directly omit exponent zero and split the
interval there. Up to the explicit monomial units of the original
differences, this is the completed product, of length O(kM). Vertical
axes similarly have the acquired offset epsilon*N in place of epsilon.
The inherited geometric engine therefore gives the METHOD cost

    soft sqrt(kM)=soft k^(5/4).

For the actual factor family above, an adaptively supplied axis horizon
is I=Theta(P/k)=Theta(k^(1+gamma)). The same tiled-factorial method then
costs soft sqrt(P)=soft k^(1+gamma/2), still above soft k for fixed
positive gamma. This is the CHARGED COST OF THAT METHOD, not a lower
bound on every possible small-factor or axis-residue supplier.

This is prior axis/content-tiling credit, not a new procedure. The four
lambda=0 axis rows can be paid separately; that does NOT discharge all
nonzero-phase axes. A claimed soft-sqrt(k)-phase Young boundary must
therefore supply a better axis substitute/controller or a cheaper
factor-residue supplier, not simply append the words “plus axes.”

Extending a nonaxis clock to reach (3) can require a scale Q/H rather
than M. At maximal imbalance this is O(k^2); even an assumed covered
soft-sqrt(k) phase bank at that horizon has the old joint upper cost
soft sqrt(sqrt(k)*k^2)=soft k^(5/4). This is an accounting tradeoff
for that enlarged-window constructor, not an optimality theorem.

## 5. Public-colour deficit and the square-row alternative

For a primitive admitted row at a unit colour, the 3-adic valuations
of a and b agree. Primitive content one therefore forces both to be
3-units; parity compatibility forces both odd. Its fixed stationary
phase satisfies

    lambda=-2a*j mod k.

Dividing the known even lambda by two modulo k/2=3^e fixes j uniquely
modulo 3^e, and the canonical odd representative fixes it modulo k.
Thus each primitive fixed-phase certificate covers at most ONE public
colour. A bank of soft sqrt k such certificates does not certify all
Theta(k) public tags. Higher content can cover more tags and needs
its actual phase multiplicity; it cannot be credited as constant.
This is ONLY an all-tag certificate count, not a proof that the one
actual P tag of a fixed N avoids a publicly chosen correlated bank.

A concrete alternative with the right descriptor count is

    a=s^2, b=t^2, lambda=+/-2stR mod H, R^2=N mod H.

It is available only on the stated square-root branch, not every N.
Row admission requires |st|<sqrt k. Stationarity at a unit colour
requires, after valuation reduction,

    s*j=+/-t*R mod 3^e.

The ordinary Dirichlet/Gauss congruence lattice has index Theta(k)
and supplies a product bound O(k), not the required sqrt k. For
3-unit s,t, the admissible O(sqrt k log k) pairs cover only that many
public tags up to a constant. If v_3(s)=v_3(t)=u, dividing by 3^u
leaves O(sqrt k*3^(-2u) log k) primitive pairs and at most 3^u tag
lifts; summing u still gives soft sqrt k. Unequal valuations do not
solve the unit-colour congruence. Hence the ramified completion does
not turn this particular small square-row family into an all-tag cover.
Again this does not refute a fixed-N prime-correlated selection theorem;
it exposes exactly the extra theorem that ansatz would require.

## Outcome and next constructive obligation

The finite Young boundary is a valid algebraic cancellation support,
but no proof that it contains a useful native stationary certificate
has been supplied. Scaling has an exact ray/carry/clock requirement;
the explicit unbalanced regime (4) forces the existing proof onto
axes; and small primitive/square banks do not certify all public tags.
These are scoped arithmetic gaps in the tested modifications.

A genuinely new covered soft-sqrt(k) bank could still exploit the
actual global factor relation to select few tags, or replace the axis
regime with a paid stronger controller. Neither is obtained from the
Young identity, Gauss scaling, or the square-row parametrization here.
Every proposed replacement must retain its own nonzero short labels,
finite signed windows and at most one T_ext. The complete sixth-rate
query remains open; no numerical evidence or general lower bound is
claimed.

Sources read: the proposal Sections 2.2-2.4; frozen scalar-catalogue.md
Sections 2-6 in `semiprime-recurrence-checkpoint-20261025/evidence/
semiprime-paired-weighted-query-20261024`; trace-recurrence.md and the
scalar swap-erratum. All identities and bounds above are derived from
those finite contracts. No additional knot theorem is imported.
