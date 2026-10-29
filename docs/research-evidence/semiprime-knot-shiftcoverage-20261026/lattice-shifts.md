# Stationary lattice combinations and guaranteed shift coverage

26 October 2026. Bounded paper investigation, no numerical tests or repository edits. Inputs and current coverage are the authoritative trace and colour-query packets. **Outcome:** the proposed operation of forcing a public index difference by cancelling stationary lattice coordinates gives only literal global exponent relations, for every actual prepared input. An actual difference between distinct stationary rows would instead be enough to factor N by a fully initialized integer quadratic test. This sharpens the arithmetic coverage target; it does not supply the required public shift list or improve the full query.

## 1. Actual stationary rows and the useful pair equation

Let N=P Q be a prepared semiprime, H=k², and j=P mod k. A same-colour row u=(a,b) in Lambda_j has canonical phase lambda_u in [0,H), with

    H I_u=aP+bQ+lambda_u,
    E_u=a+bN+lambda_u.

Its physical local equality beta^E_u=q^I_u holds at P because

    E_u-HI_u=(P-1)(bQ-a).

This is an actual-input identity, not a statement about arbitrary polynomial roots. For two such rows u=(a,b), v=(c,d), put

    A=c-a, B=d-b, L=lambda_v-lambda_u.

Their physical index difference s=I_v-I_u satisfies

    Hs=A P+B Q+L,
    A P²+(L-Hs)P+B N=0.                            (1)

Conversely, for a supplied integer s, (1) is completely testable without an Ore recurrence, beta, or the long clock. If A!=0 compute the exact integer discriminant

    Delta_s=(L-Hs)²-4ABN.

If Delta_s is a nonnegative square, test the at-most-two rational quadratic roots for integer divisibility and a proper factor of N. If A=0 and B!=0, equation(1) is linear in P, so test P=-BN/(L-Hs). Handle a zero denominator directly; it cannot be a physical solution with B!=0. For A=B=0 the equation is only L=Hs and gives no factor.

For two distinct coefficient vectors in the original bounded family, the promised same-field overlap is genuinely NONLITERAL. Indeed

    E_v-E_u-Hs=(P-1)(BQ-A).                         (2)

On the prepared branch Q>2k and |A|,|B|<=2k. Thus BQ=A implies A=B=0. Consequently a physical difference between distinct native coefficient vectors forces either a useful nonliteral p-local edge, or factor return before this edge is used. At s=0 it forces a same-field node collision, which the existing separation prepass already detects. For |I_u|,|I_v|<=M the shift is at most2M and the original exponent-gap/short-label bounds remain valid. The cheap integer quadratic test avoids even the saturated-annihilator consumer when its promise holds.

This gives a concrete sufficient complete-coverage statement:

> Acquire soft-k many (pair,shift) candidates. For every continuing prepared semiprime, at least one candidate must be two distinct actual stationary rows in one physical colour, both in the inherited window, with its supplied shift equal to their physical index difference.

Under that statement, the candidate list factors N in soft k by(1), without evaluating any shifted polynomial. It is sufficient, not asserted equivalent to all possible modular-alias shift mechanisms: an accidental local edge need not come from two physical stationary rows.

## 2. Execute sums, opposition and multiples, including all carries

On one acquired colour, canonical phase addition is

    lambda_(u+v)=lambda_u+lambda_v-H*c,
    c=floor((lambda_u+lambda_v)/H).

Whenever the sum is retained and in its licensed window,

    I_(u+v)=I_u+I_v-c,
    E_(u+v)=E_u+E_v-H*c.                            (3)

The carry is public. Equation(3) is stronger than a local identity: its exponent equation is an exact integer relation before any reduction modulo either prime. Therefore the attempted forced-overlap test

    beta^E_(u+v) / (beta^E_u beta^E_v) = q^-c

is globally true for every N. It gives no nonzero annihilator and no localization. The physical index relation has merely reproduced that same literal relation.

For d>=1, with c_d=floor(d*lambda_u/H), the corresponding exact equations are

    lambda_(du)=d*lambda_u-H*c_d,
    I_(du)=d*I_u-c_d, E_(du)=d*E_u-H*c_d.             (4)

The desired difference between u and du is (d-1)I_u-c_d; it is not a public shift until I_u or an equivalent new arithmetic condition is acquired. Native nonaxis multiplication also requires d²|ab|<k; it is not a free long string. New rows outside this bound require an independent coverage, horizon, deletion and acquisition ledger.

For opposition put epsilon_u=1 when lambda_u>0 and0 otherwise. Then

    lambda_(-u)=-lambda_u+H*epsilon_u,
    I_(-u)=-I_u+epsilon_u,
    E_(-u)=-E_u+H*epsilon_u.                        (5)

Again the forced sum is literal, while the useful difference epsilon_u-2I_u remains unknown. This keeps the lambda=0 convention separate instead of assuming unconditional I ->1-I.

Swapping coordinates is not automatically an operation within Lambda_j. The actual swapped witness lies in the physical Q-colour N*j^-1, with the SAME I but at the other local prime. Its cross-prime promise does not force a same-field overlap between the original and swapped node. Treating that equality as if it held at P would discard the central coverage distinction in the colour-selector packet.

## 3. General cancellation theorem for this construction

Let a finite collection of same-colour rows have phases lambda_l and indices I_l. For ANY acquired integer coefficients n_l, set

    A=sum n_l a_l, B=sum n_l b_l, L=sum n_l lambda_l.

Then exactly

    H*sum n_l I_l=A P+B Q+L,
    sum n_l E_l=A+B N+L.                            (6)

If the lattice operation cancels BOTH coordinates, A=B=0, the forced index sum is the known integer L/H. The identical GLOBAL relation is sum n_l E_l=L. Any multiplicative q-overlap derived from that relation has exponent gap zero. This holds for every actual input, every chosen colour, every legal intermediate canonical carry, and arbitrary integer coefficients of manageable bit length. It is not an independent generic-root example or a complexity lower bound.

If A or B survives, assigning the sum a supplied value s leads to the same explicit factor equation (1), with those combined A,B,L. The construction has not forced s: it has reduced its acquisition to an arithmetic assertion about AP+BQ. Iterating (3)-(5), taking a determinant-k basis relation, or applying Bezout coefficients to row coordinates does not remove this distinction. A basis has no nonzero rational coordinate-kernel relation, so it leaves two unknown index states. Extra rows provide known relations among those states, but all relations obtained by coordinate cancellation are precisely the literal identities in(6).

Thus the SPECIFIC proposal "manufacture a nonliteral edge by cancelling P and Q through stationary sums/opposites/multiples" fails unconditionally: its cancellation branch is literal on every actual semiprime. A noncancelling combination may be useful, and is not excluded. It needs a proved shift-value coverage theorem rather than the cancellation identity itself.

## 4. Count candidates honestly; do not assume many physical witnesses

The full native catalogue's soft-k total incidence bound does not imply that the sum of squared colour-list sizes is soft k. No such unproved bound is used here. Nor is a square-root-k count of physical witnesses assumed.

There IS a paid public family suitable for attempting pair coverage: the trace packet's Gauss construction selects O(log N) short rows for each of O(k) colours, one per dyadic factor-weight scale, with inherited opposites and swaps. Keeping within-colour original/opposite lists gives O(log N) rows per colour. All within-colour ordered pairs therefore number O(k log² N), hence soft k. Compute A,B,L for all these pairs in soft k. Some pairs can be literal duplicates or opposites, and a colour may have only one distinct useful physical row in the licensed window. The Gauss coverage theorem guarantees one correct short row and its coupled swapped witness; it does NOT guarantee a second independent same-colour short row. A second reduced basis vector cannot simply be inserted as a native short row when its norm/product exceeds the proved bounds.

For any supplied polylogarithmic shift set S, testing(1) for every selected pair and every s in S costs soft k bit operations. All coefficients, discriminants and integer square-root tests have O(log N) bit size, provided the supplied shifts have that size. For original admissible rows in the original window, local exponent gaps have the old nonzero-label and horizon guarantees. With factor validation by gcd/divisibility, no false quadratic candidate is returned as a factor. This is a complete ACQUISITION/CANDIDATE-TEST algorithm conditional on the stated shift coverage, not a complete factoring algorithm.

A simpler specialization tests pairs u and -u: it needs a supplied set containing epsilon_u-2I_u for one useful physical row. That is essentially an affine reparameterization of the old unknown clock position, not a known shift. A coordinate-kernel construction forces no additional value.

The axis formulas make the same issue explicit. For the horizontal row (k,0), write j=P mod k, 0<j<k. Then lambda_h=H-kj and I_h=(P-j)/k+1. For the vertical axis put r=Q mod k=N*j^-1 mod k; lambda_v=H-kr and I_v=(Q-r)/k+1. The public inputs know j,r and the axis nodes, but not these indices. Recovering the two index parameters amounts to the exact known-input equation

    N=(j+k*(I_h-1))*(r+k*(I_v-1)).                 (7)

For balanced factors these axis indices are Theta(k²), outside the Theta(k^(3/2)) native horizon. Appending many axis translates does not silently turn them into short-window physical witnesses. There are special easy inputs on which axis-index arithmetic helps; no uniform assertion is made against those branches.

## 5. Narrow remaining arithmetic target and full-query scope

The useful next theorem would provide a PUBLIC soft-k candidate list of noncancelling coefficient triples (A,B,L) together with supplied values s, containing one identity AP+BQ+L=Hs with a valid distinct stationary pair, or otherwise a proof that a nonphysical modular alias gives a factor. All candidate integer tests are already paid. A polylogarithmic shift list is sufficient, but not necessary if a more economical joint acquisition is proved.

No stationarity/covolume argument above forces such values. Determinant k controls the row lattice; it does not assign its projection AP+BQ onto the unknown factor direction. Known canonical carries preserve that projection instead of evaluating it. Publicly manufacturing all coordinate-kernel relations supplies only globally literal overlaps, exactly as(6) shows.

No lower bound is claimed for acquiring the shift list, for nonlinear index relations, for modular aliases, or for the original whole query. No assertion that arbitrary polylogarithmic shifts fail is made. The actual complete query bound remains soft O(J+sqrt(Jm)); the desired soft O(J+sqrt m) is open. The executed outcome is the exact failure of the proposed linear cancellation mechanism, plus the initialized quadratic factor test that any successful native shift-coverage theorem would immediately enable.

## Sources and prior credit

This report uses derived integer identities rather than a new literature theorem. Primary research-evidence inputs are the existing semiprime-knot-trace-20261026/trace-recurrence.md and farey-query.md (stationary phases, explicit soft-k colour enumeration, Gauss acquisition, and signed-window proof) and semiprime-knot-colourquery-20261026/colour-selector.md (paid nonliteral modular-edge consumer and its missing coverage). The arithmetic integer quadratic test is proved in section1; no black-box field gcd, unknown-order exponent reduction, or extra root-of-unity premise is invoked.
