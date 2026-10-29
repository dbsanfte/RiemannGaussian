# A scalar prefix decision suffices for the complete collision query

25 October 2026. Conditional algorithm interface, with an unconditional
reduction proof. The fast prefix primitive is **not supplied** by this note.
This specializes the project's existing weak-selector and bisection consumer
to the acquired Alexander polynomial; generic bisection is not new credit.

## Input and central screen

Let R=Z/NZ, N=PQ with distinct odd primes, and retain the already acquired
native rows x_j=beta^(E_j), j=1,...,J. Put q=beta^H and use the centered
index window [-M,M]. The existing catalogue deletes every whole row for
which E_j=Hi for an integer i in this window. It retains a promised local
collision at one or both primes, with all coverage and preprocessing costs
charged in the prior controller.

First scan gcd(x_j-1,N). A proper gcd factors N. A saturated gcd gives
beta^(E_j)=1 globally, with E_j nonzero because index zero was deleted;
invoke the existing licensed short-annihilator extractor. On the continuing
branch all x_j-1 are units. This screen costs soft O(J). These inverses,
and those of x_j, can be batched.

Acquire

    z_j=x_j+x_j^-1,
    G(Z)=prod_j(Z-z_j),
    Delta(T)=G(T+T^-1)/G(2).

Here G(2)=prod_j[-(x_j-1)^2/x_j] is a unit. Every retained row remains in G;
duplicates may be retained and inverse closure is unnecessary. This is the
modular reduction of the genuine knot Alexander polynomial constructed in
[the sparse Seifert report](alexander-realization.md).

## Exact scalar identity, without q-factorial denominators

For every unit t in R,

    Delta(t)=prod_j [(x_j-t)(x_j-t^-1)/(x_j-1)^2].          (1)

Indeed (x-t)(x-t^-1)=x[(x+x^-1)-(t+t^-1)], and the two
minus signs in G(t+t^-1)/G(2) cancel for each row. Consequently

    A_m=prod_(i=1)^m Delta(q^i)
       =prod_(j,i) (x_j-q^i)(x_j-q^-i)
          /prod_j(x_j-1)^(2m).                           (2)

All denominators in (1) and (2) are known units. The equivalence holds over
the actual composite ring, including saturated zeros and different local
signs. No division by a collision difference is used. For this reduction
alone, the local-order promise is unnecessary beyond q being a unit; that
promise is still available to algorithms using q-factorial normalizations.

The needed primitive can therefore be as weak as the following exact bit:

    PrefixNonunit(G,q,m) = [A_m is a nonunit in Z/NZ].      (3)

Returning the residue A_m is sufficient but unnecessary. No full polynomial
remainder, coloring vector, list of row values, or shifted-interval query
is required by the consumer below. An exact nontrivial-coloring decision
for the equivalent acquired Alexander presentation would also be useful
if it implements (3), with all its costs included.

## Localization using only prefixes of the same input

Let U(m) denote (3). U(0)=false. In a commutative ring a finite product is
a unit exactly when every factor is a unit. Thus U(m) is monotone. The old
coverage theorem and the central screen imply U(M)=true on the continuing
branch. Both endpoints are supplied by proof rather than oracle calls.

Maintain lo=0, hi=M with U(lo)=false and U(hi)=true. Query
mid=floor((lo+hi)/2), retaining the half consistent with the returned bit,
until hi=lo+1. This takes at most ceil(log2 M) calls, all using the same
G and q. For i=hi, the earlier prefix A_(i-1) is a unit while A_i is a
nonunit, so Delta(q^i) is a nonunit. This argument also handles A_i=0
globally; no assumption of a proper gcd at a prefix is needed.

Acquire q^i and q^-i by powering and scan both signed original leaves:

    gcd(x_j-q^i,N),  gcd(x_j-q^-i,N),   j=1,...,J.         (4)

Equation (1) guarantees at least one nonunit leaf. A proper gcd factors.
A saturated positive leaf supplies beta^(E_j-Hi)=1; a saturated negative
leaf supplies beta^(E_j+Hi)=1. Both integer exponents are nonzero by the
whole-row deletion rule. Their bit length remains O(log N) in the native
parameter regime, and they lie in the signed exponent range of the
existing licensed extractor. Invoke that extractor on saturation.

If x_j=q^i at P but x_j=q^-i at Q, the two signed tests remain separate
and reveal the corresponding proper factors (unless a globally equal
signed leaf is encountered first, which already licenses extraction).
A trace equality is never treated as a choice of a global sign.

## The native promise also permits a zero-only prefix decision

The actual swap coverage is stronger than one local hit. Its two retained
rows satisfy, for the same index I,

    HI=aP+bQ+lambda,
    E-HI=(P-1)(bQ-a),
    E'-HI=(Q-1)(aP-b).

Thus x=beta^E equals q^I modulo P, and its retained swap x'=beta^E'
equals q^I modulo Q. The earlier zero-row, diagonal, and complete-swap
preprocessing preserves a pair with this property on the continuing
branch. If I were zero, the central screen would already have finished.
Consequently r=|I| lies in [1,M], G(q^r+q^-r)=0 modulo both primes,
and Delta(q^r)=0 modulo N. In particular A_M=0. Neither inverse closure
of the row list nor a global equality of one original leaf is assumed.

An even more restricted oracle output therefore suffices for this native
input:

    PrefixZero(G,q,m) = [A_m = 0 in Z/NZ].                 (5)

The Boolean predicate is monotone because zero remains zero under
multiplication. Binary-search its first true index i using known endpoints
A_0=1 and A_M=0. Now A_(i-1) is nonzero, though it need not be a unit.
If Delta(q^i) were a unit, multiplying by it could not turn this nonzero
element into zero. Hence Delta(q^i) is a nonunit, and exactly the same
signed scan (4) finishes. This version needs no prefix gcd or prefix
unit decision. The cost contract is unchanged.

The zero-only version depends on both-prime coverage, which the actual
native family supplies. Merely promising a hit at one unknown prime is
insufficient. More generally, hits at both primes at different indices
would already give A_M=0; the common-index native promise is stronger.
The oracle must be exact, including distinguishing nonzero zero divisors
from zero. It is not implemented at the desired rate here.

## Conditional cost and exact open question

If (3), or (5) with its stronger native promise, costs soft O(J+sqrt(m)) per requested
prefix, then at most logarithmically many calls cost soft O(J+sqrt(M)).
Central screening and the final signed scan cost soft O(J); exponentiation
is polylogarithmic; the already licensed extractor costs
soft O(N^(31/192)), below soft O(k) for k of sixth-root scale. Since
J=soft O(k) and M=Theta(k^(3/2)), the new primitive would close the current
whole-family query bottleneck at soft O(k). The complete executable and
Lean bit-complexity development would still have to integrate the proved
primitive and inherited controller.

The presently available evaluation bound soft O(J+sqrt(JM)) gives
soft O(k^(5/4)), including this localization. The reduction itself makes
no exponent improvement. Acquiring the sparse Seifert matrix in soft O(J)
does not compute its long partial product.

The concrete knot-theory target is therefore: **decide zero or nonunitness
of the partial geometric product of this acquired Alexander polynomial in
soft O(J+sqrt(m)), without knowing either prime or the local orders.**
It suffices to do this for the native family and requested prefixes;
a generic all-polynomial theorem would be stronger than required.

Independent review: [prefix-consumer-review.md](prefix-consumer-review.md).
The accompanying reference check uses a deliberately slow oracle on a few
CRT control-flow fixtures. It validates signs and saturation handling only;
it supplies neither a native coverage theorem nor the fast primitive.
