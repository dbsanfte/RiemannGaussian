# Projective closure, collision indicators and axis transport

26 October 2026. **The complete query exponent is unchanged.** The previous
turn made progress by proving a collision-retaining deformation and its
consumer, and by identifying the native boundary's coverage limitations.
This continuation executes the proposed projective closure, improves the
full-divisor acquisition overhead, and proves a specific axis-to-kernel
transport. The full deterministic classical all-semiprime sixth-exponent
goal remains open, including acquisition, recovery, bit complexity and Lean.

The results resolve some representation mismatches, but do not supply the
missing arithmetic information. In particular, neither a closed small
matrix action nor differentiation of the existing expensive circuit gives
a softly linear complete query.

## Current contract and results

Use the original signed native rows, axes, canonical colours/carries,
public deletions, source labels and paid unit guards. J=soft O(k),
h=O(k^(3/2)), k of order N^(1/6), H=k², q=beta^H. The continuing
branch has distinct local row roots and clock points. The retained route is

    C(J,h)=soft O(J+sqrt(Jh))=soft O(k^(5/4)).

This is this route's cost, not the best general factoring record. No hidden
order coprimality, roughness or unique-hit orientation is added. All legal
saturated branches keep at most one T_ext=soft O(N^(31/192)).

| Executed step | What is now proved | What it does not supply |
| --- | --- | --- |
| Projective colour action | Exact commuting 2-by-2 matrices, canonical carries and unit normalizations | The product of row-clock comparisons or its collision slice |
| Covariant marking parameter | Exact weighted endpoint recurrence, including the whole marked factor | An interior hit: that marked factor cancels too |
| Univariate Hasse gradient | All row-hit indicators at linear, rather than quadratic, precision overhead | A faster scalar acquisition circuit |
| Odd-axis transport | Any useful alias maps to a genuine nonliteral kernel leaf and transports its coarse phase residue | The coarse residue itself |
| Public residue controllers | An explicit soft-k algorithm for a quantified ramified subclass | Coverage of all remaining unbalanced semiprimes |

## A small projective action really does close

The [projective report](projective-closure.md) puts a=1-delta,
b=delta Y, kappa=b/a and psi(y)=ay/(1-by). Multiplication by any
supplied character c becomes the exact matrix

    T_c = [[c,0],[kappa(1-c),1]],  T_c T_d=T_(cd).

Its automorphy factors have known unit constant terms, and source carries
are exactly T_(q^-tau). Thus the earlier failure of scalar multiplicativity
has a constructive projective repair. The mixed action with the ordinary
clock also closes in a small triangular matrix group.

But the executed group loop gives endpoint data. The one-row comparison
product still contains the finite Pochhammer at psi(y). Moving BOTH row and
clock through psi makes an original hit identically zero in delta, so it
cannot supply the regularized collision slice.

Allowing the marking variable to move is another exact repair:

    f(cy,x;delta,Y/c)=f(y,x/c;delta,Y).

For x_i=q^(L+i), P_y=product_(0<=i<h) f(y,x_i), it yields

    f(y,x_h;delta,Y) P_y(delta,Y)
      = f(y,x_0;delta,Y) P_(y/q)(delta,qY).

The interior factors cancel as entire marked polynomials, including
 delta(1-Yx) at a hit. This excludes the hoped-for inference from these
specific cheap weighted endpoints to the positive interior divisor. It is
not a general obstruction to projective or finite-state algorithms.

## A better initialized full-divisor algorithm

The [singular recurrence report](singular-recurrence.md) uses only

    P(delta;y)=product_(j,i)(1-(1-delta)y_j/x_i)=sum a_n(y)delta^n.

If the first nonzero coefficient modulo N has a proper gcd, it factors.
Otherwise the local hit counts agree at d, A=a_d is a unit, and

    e_j = -y_j A^-1 partial_(y_j) a_(d-1)

is exactly 0 or 1 at each prime according to whether row j hits the clock.
The row roots are independent formal inputs for differentiation. A mixed
CRT indicator factors; if there are none, product_(e_j=1)(1-Yy_j) is the
reciprocal monic gcd at both components. No unique-hit promise is required.

The explicitly initialized monic block circuit and its reverse pass over
R[delta]/delta^(d+1) cost soft O((d+1)C(J,h)+T_ext). The elementary reverse
gate proof uses only certified unit inverses and avoids factorial division.
This improves the preceding triangular jet's quadratic precision overhead.
An output-sensitive restriction algorithm alternatively acquires the full
mask or a factor in soft O(J+sqrt(max(1,t)Jh)+T_ext), where t is the union
hit-row count. Both still pay the old scalar-query scale. For factoring,
one nonunit restriction path already suffices at C(J,h); listing every hit
is unnecessary. This is a full-output refinement, not exponent progress.

The primary q-holonomic bound retains the coefficient-degree cost. The
inspected Ore desingularization theorem removes leading singular factors;
our forward scalar recurrence is already monic. Neither source supplies
a cheaper acquisition step.

## An exact bridge between the two covered queries

The [axis report](axis-controller.md) takes a public factor cap B and
M_B=ceil(B/k)+1. Retain odd horizontal phases t, rho=beta^k, and the
nonliteral axis exponents

    e=t+1-kI, |I|<=M_B.

The true smaller-factor witness has e=1-P. More generally, ANY useful
local alias rho^e=1 maps, without a stationarity assumption, to

    q^(e/2)=1, h_kernel=e/2 !=0,
    h_kernel=(t+1)/2 mod m  for odd m|k.

The original b=0 kernel leaf has the inverse exponent and the same
nonunit predicate. Its bound is |h_kernel|<=(B+3k)/2. It belongs to the
original universal kernel when that public bound is <=W; otherwise the
report explicitly treats a bounded b=0 extension. A phase residue thus
transports safely to a kernel clock residue without pretending the alias
phase is a factor tag.

Given one useful phase residue modulo m, its axis or shorter-kernel
consumer costs soft O(sqrt(B/m)+sqrt(k/m)+T_ext). An S-residue palette
costs soft O(S+sqrt(S(B+k)/m)+T_ext), PLUS palette acquisition. Thus
m of order B/k² suffices for one supplied residue. Keeping the full W
kernel window instead requires m of order W/k²; the bounds are not
interchangeable. Trying all residues restores the old square-root cost.

The report also executes logarithmically many public +/-1 residue
controllers, integrating old AP factorial machinery. They cover
P<=c k² max(gcd(P-1,k/2),gcd(P+1,k/2)) in soft k. This coverage
certificate misses actual infinite gamma families with both primes
23 mod36, where the odd gcd maximum is 3 while P/k² tends to infinity.
This does not prove that accidental modular hits cannot make those tests
succeed, and does not refute other residue suppliers.

## Decision and verification

The projective closure and marking covariance are now executed; additional
normalization of those same actions is not the next missing step. The most
concrete unresolved arithmetic target from this pass is to SUPPLY a useful
axis phase/index residue, with its cost included, or obtain a genuinely
new circuit for the collision-retaining row statistic. The axis-to-kernel
bridge gives a valid way to reuse such information once acquired.

Two independent cross-reviews and the primary-agent arithmetic/integration
review checked the identities, boundaries, normalization and costs. Primary
source qualifications are recorded in [sources.json](sources.json).
These are paper proofs, not Lean or numerical coverage evidence. Prior
work and the user's string proposal were preserved. No factoring code,
benchmark campaign, commit or push was performed.
