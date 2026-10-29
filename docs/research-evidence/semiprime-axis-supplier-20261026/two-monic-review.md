# Independent review: two monic families and the stronger old weighted-sector handoff

26 October 2026. Read the frozen symmetric supplier and signed-weight
query sources, checked finite arithmetic and palette composition. No
implementation, tests, examples or repository edits.

**PASS with scope.** The two-monic wrapper has the stated good-family
unique-hit theorem. However the older weighted signed family already
has unconditional ANY-nonsplit-factor coverage with all factor bins.
Its additional content-sector residue provenance, including an axis
exception with FULL tag precision, is the more general useful hybrid
interface. A target-cost readout of the required weak pairs is still
unacquired. Neither construction alone supplies that readout.

## 1. Exact old sources and prior orientation credit

The authoritative sources read are

- `semiprime-recurrence-checkpoint-20261025/evidence/
  semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md`,
  Sections1-5, especially (1)-(8).
- The same directory's `symmetric-supplier-audit.md`, and
  `semiprime-weighted-recurrence-20261024/hyperbola-cosets.md`,
  Sections1-2,5, in the same recurrence evidence tree.
- `semiprime-unique-acquisition-20261024/unique-gcd.md`, Section1,
  and `semiprime-norm-sharing-20261024/implicit-evaluation.md`,
  Section6: these narrower monic unique-hit claims were explicitly
  restricted to the smaller nonsplit prime.

The signed-weight source ALREADY uses one unconditional Jacobi-minus
D0 and builds all public factor bins, with beta,W both odd k-rough
and >16H. At whichever factor R is nonsplit, their orders divide
R-1,R+1 and are coprime, so ord_R(pi)>256H^2 and pi^R=barpi.
The source explicitly says R may be P OR Q and needs no QRH
smaller-orientation palette. Thus removing orientation for a general
covered query is prior credit; a new unique-hit or common-residue
weak-output theorem is a refinement, not a newly unconditional setup.
The narrow search found no old two-monic unique-hit wrapper itself.

## 2. Check the two-monic alternative

For every unit j mod k define either

    A: b=1, a=[N*j^(-2)]_k,
    B: a=1, b=[j^2*N^(-1)]_k.

Both coefficients are positive units modulo k. With
D_j=(a*j^2-bN)/k, t=[D_j*j^(-1)]_k and centered
ell=[-2aj+kt]_H, f(X)=aX^2+ell X+bN satisfies
f(j)=0 modH and f'(j)=0 modk. Thus f(j+kz)=0 modH.
The own j=R modk gives integer

    I=(aR+bN/R+ell)/H,
    V=pi^ell*barpi^(a+bN)=pi^(aR+bN/R+ell) modR.

At smaller nonsplit R=P use A, at larger nonsplit R=Q use B.
For EVERY row of the good family,

    0<aR+bN/R<=kP+Q
              <k^4+k^4/16=(17/16)H^2.

The original hard branch gives P<=sqrtN<=k^3 and Q<N/(16H)<=k^4/16.
With |ell|<=H/2, the own |I|<2H. Therefore [-2H,2H], length
4H+1<16H, covers it. At ANY hit in this good family,

    K=aR+bN/R+ell-HI,
    |K|<(49/16)H^2+H/2<4H^2<ord_R(pi).

So the equality is an INTEGER K=0, not a hidden-order alias.

Writing d=R-j and using f(j)=0 modH,f'(j)=0 modk gives
`0=f(R)=a*d^2+k*t*d modH`. Because a is a unit modulo k, if
v_p(d)<v_p(k) the quadratic term has strictly lower valuation than
the linear term and less than2v_p(k), contradiction. Thus k|d.
There is exactly ONE hit tag, and one index by the q-order guard.
The hit is simple in the root polynomial even if other roots have
unresolved off-clock multiplicities: no other row shares that clock
root in the good field. Global unit root separation need not be
assumed merely to prove this local gcd-degree-one fact.

Both families have soft-k acquired metadata, and the old full query
cost soft(k+sqrt(k*H))=soft k^(3/2). Wrong-family attempts remain
bounded verified-factor-or-failure attempts. The same tag marker in
Section4 below has d=1 in the good family, yielding an especially
simple FIRST-variation target, but no target-cost readout is inferred.

## 3. Old weighted rows: exact content and axis provenance

Use the original ONE shortest vector per unit tag and public bin,
not an arbitrary untagged completion of all conic roots. In the
correct nonsplit-factor bin the source proves for EVERY row/index
that a local hit forces the exact integer f(R)=0: its bound is
`|aR+bN/R+ell-HI|<3H^2<ord_R(pi)`. This all-leaf guarantee is the
reason the following residue claims apply to accidental hits too.

For a nonaxis shortest vector let g=gcd(|a|,|b|). Then g divides k.
Indeed division by a prime outside k, or beyond its valuation in k,
would preserve the colour lattice and strictly shorten the vector.
Also g^2<=|ab|<k, hence g<sqrt k.

Put n_g=k/g. If p^e||k and v=v_p(g)<e, the congruence
`a*j^2=bN modk` and unit j,N force v_p(a)=v_p(b)=v.
With u=v_p(R-j), suppose u<e-v. In

    f(R)-f(j)=a*(R-j)^2+f'(j)*(R-j),

term valuations are v+2u and at least e+u. The first is strictly
smaller and below2e, contradicting H|f(R). Thus u>=e-v and

    R=j mod n_g.                                  (1)

Primes with v=e contribute no condition, exactly as n_g says.

Axes must NOT be assigned n_g=1 just because their content is k.
The source shortest-axis forms give a stronger exact result:

- Horizontal a=epsilon*k,b=0 has ell=-a*j modH.
  From f(R)=0 and R a unit modH, aR+ell=0 modH, hence k|(R-j).
- Vertical a=0,b=epsilon*k has ell=-bN*j^(-1) modH.
  The same equality gives N/R=N/j modk, hence again R=j modk.

Thus ALL axis hits in the correct bin carry the FULL factor tag
modk. This uses exact nonsplit/weighted-bin provenance; the scalar
axis alias of the separate ordinary-beta family does not have it.

## 4. Marked first slice gives a common-residue weak pair

For each bin and nonaxis content sector mark every row/clock factor
by

    1-y_j/x_i+delta*(1-Y*[j]_(n_g)).

For the axis sector use n_axis=k. At the nonsplit field in the
correct bin, all hit tags equal r=R mod n_g by (1), including the
special axis precision just proved. There is at most one clock hit
per row, so the local hit count d<=J<=k. If d>=1, the first nonzero
delta slice is EXACTLY

    Q(Y)=A*(1-Y*r)^d, A!=0.

Consequently

    V=d*A, U=-[Y]Q=d*A*r,
    U/V=r at the good field.                       (2)

The integer d is a unit because d<=k<P,Q; characteristic cancellation
cannot kill the linear coefficient. This is a polynomial identity
through collisions and needs no inverse of a hit factor. An earlier
nonzero slice at another component instead yields the existing
proper-coordinate/norm gcd branch. Wrong bins/sectors with d=0
can return bounded failure; they do not justify an inverse of V=0.

The report MUST treat obtaining this first slice, its d, or any
sufficient projective pair satisfying (2), as the MISSING acquisition
operation. Specifying the marker and proving (2) do not compute it.
The old full-product/jet circuits still pay their existing degree-
dependent cost. No orientation or uniqueness is silently added.

## 5. Fully paid validation and one shared HH palette

For an ACQUIRED candidate pair, apply the existing rank-two
coefficient classifier/inverse: V is nonzero at the promised field,
so its norm is a unit or gives a proper factor, never saturated there.
The tau-coordinate of U/V is zero at that field, hence gives a proper
factor or a global base-ring scalar. The old bounded integer-tag
validation costs at most soft O(n_g) and returns a verified factor,
one residue r in[0,n_g), or failure. This is safe on wrong attempts.
All sector attempts cost at most

    sum_(g|k) soft(k/g)=soft O(k),

with axes a separate n=k attempt and logarithmically many bins.
The actual modulus has at most three distinct prime factors, and
even the elementary divisor bound suffices for this accounting.

Lift a validated nonaxis r modulo n_g to its g residues modulo k.
Filter nonunits modulo k; the correct R residue survives. An axis
output has one lift, not k. Retain ONE validated output per
(SECTOR,BIN), and union outputs from ALL bins. A valid-looking wrong-
bin result cannot justify discarding the correct later-bin output.
The list before factor-swap complement has size at most

    O(log N)*(1+sum_(g|k,g<sqrt k)g)
       <=O(log N)*sqrt k*tau(k).

Do not call this soft O(sqrt k) for arbitrary k. The elementary
uniform bound tau(k)<=C_epsilon*k^epsilon at epsilon=1/12,
together with log N=O(log k)<=C*k^(1/12), makes it at most
C*k^(2/3), including the log-bin factor. Its
acquisition/lifting cost fits soft k. Since R may be larger, add each
unit residue's complement N/r modk; this doubles the paid list and
guarantees a correct SMALLER-factor residue for restricted HH.
The new n=k shared-palette consumer therefore finishes in soft k
IF those candidate weak pairs have been acquired within soft k.
No separate per-sector HH query or separate correct-bin advice is
needed. Wrong residues are tolerated by its bounded verifier.

## Verdict

The weighted content-sector/axis marker target is a valid UNIFORM
alternative to the older smaller-nonsplit unique-hit target and is
stronger than using the two-monic wrapper alone. It exploits actual
old acquired coefficient/phase data and the new HH palette tolerance.
Its remaining mathematical/computational obligation is precisely a
soft-k acquisition of the sufficient sector/bin projective pairs;
the current review proves their provenance and paid consumer, not
that missing operation or a new full factoring rate.
