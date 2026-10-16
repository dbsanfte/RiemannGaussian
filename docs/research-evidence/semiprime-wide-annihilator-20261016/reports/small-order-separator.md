# A composite-safe small-local-order separator

2026-10-16. Classical baby-step/giant-step variant, with a self-contained proof. No external priority claim or new formal declaration is made.

## Contract

Let N=P Q for distinct odd primes P,Q, and let b be a unit modulo N. The algorithm receives only N,b and an integer m>=1. Promise that the exact multiplicative orders d_P=ord_P(b) and d_Q=ord_Q(b) both satisfy d_P,d_Q<=m. Neither factor nor order is supplied.

Deterministically, the algorithm returns either a proper factor of N, or the exact common order d_P=d_Q together with that integer. It uses soft O(sqrt(m)) arithmetic operations over Z/NZ and soft O(sqrt(m) log N) bit operations, including integer gcds, with ordinary logarithmic bookkeeping factors suppressed. As usual m and its indices have O(log m) bits; this bound can equivalently retain polylog(m,N) factors. Under the promised orders there is always a hit. Outside that promise it may report no hit; any factor or common-order output still has the proved meaning.

## Algorithm

Set H=ceil(sqrt(m)). Work in R=Z/NZ. Compute babies u_i=b^i, 0<=i<H, by successive multiplication. Build and retain the balanced polynomial product tree with leaves X-u_i and root

 F(X)=product_(i=0)^(H-1) (X-u_i).

Compute g_j=b^(Hj), 1<=j<=H, using one multiplication for b^H after the baby sequence and then successive multiplication by b^H. Evaluate F at every g_j using a standard monic subproduct/remainder tree. The evaluation tree has leaves X-g_j; every polynomial division is by a monic polynomial. No interpolation or inversion of differences is used.

Scan j=1,...,H in increasing order, computing gcd(F(g_j),N) as an integer gcd of a canonical residue and N. A proper gcd is an output factor. Skip gcd 1. At the first row with gcd N, locate within the retained baby product tree as follows.

Its leaves are ordered i=0,...,H-1. At each internal node inspect the child containing the larger i values FIRST, by evaluating that child's polynomial at the fixed g_j and taking its gcd with N. Return any proper gcd immediately. If the gcd is N, descend into that child. If it is 1, discard that child and descend into the other child, whose gcd is then N because the parent's gcd is N and the discarded child's value is a unit modulo N. Continue until a leaf is reached. If its value has gcd N, return t=Hj-i for that leaf i as the exact common order. The case H=1 is already a leaf and needs no traversal.

If every row has gcd 1, report no hit. This branch is impossible under the promised order bounds.

## Correctness

For every row and leaf,

 g_j-u_i=b^i (b^(Hj-i)-1).

Since b is a unit, this leaf is nonunit modulo N exactly when b^t=1 modulo at least one hidden prime, where t=Hj-i. Row j covers precisely the positive exponents

 (j-1)H+1,...,jH.

Thus all rows together cover t=1,...,H², which contains both promised orders. At least one row is nonunit. All earlier rows before the first nonunit row have every leaf unit: a product is a unit in a commutative ring if and only if every factor is a unit.

Within the chosen row, visiting larger i first visits smaller t first. A skipped child with gcd 1 contains only unit leaves. A child with a proper gcd already supplies a proper factor, so further localization is unnecessary. Consequently if localization reaches a gcd-N leaf, every smaller positive exponent t' has b^(t')-1 unit modulo N. At its exponent t, both b^t-1 vanish in their respective hidden fields. Therefore

 t=min(d_P,d_Q),  d_P|t,  d_Q|t,

which forces d_P=d_Q=t. This proves that a common-order output is exact, not just a common multiple. In particular, unequal local orders cannot reach a saturated leaf without an earlier proper-factor output.

The same proof validates a common-order output even without the upper-bound promise: it only uses the certified earlier unit leaves and the saturated leaf. The promise is needed to guarantee termination with a hit among the tested exponents.

Repeated babies, repeated giants and point collisions modulo either hidden prime do not invalidate the product identities, monic evaluation, or localization. Zero values are handled by gcd(0,N)=N.

## Arithmetic and bit cost

Generating babies and giants takes O(H) ring multiplications. Balanced product construction and ordinary monic multipoint evaluation at H points take soft O(H) ring operations with fast polynomial multiplication. Fast monic division follows by reversal and reciprocal of a series with constant coefficient 1; Newton's update g -> g(2-fg) uses additions and multiplications and is valid over any commutative ring, including rings with zero divisors. It never divides by a point difference.

The row scan uses H integer gcds. In localization, evaluate one sibling polynomial per level by Horner's rule. The sibling degrees decrease geometrically, so their sum is O(H); the path adds O(H) ring operations and O(log H) gcds. Retaining the trees uses soft O(H) ring elements of storage.

Represent residues by O(log N) bits. Fast integer polynomial arithmetic (for example Kronecker encoding followed by coefficient reduction), monic division, and product/remainder trees give soft O(H log N) bit work; the H row gcds and localization gcds fit the same bound. Index generation and manipulation contribute only ordinary logarithmic factors. Thus H=ceil(sqrt(m)) gives the claimed bounds. These costs concern the supplied unit b and do not include acquiring b or proving its promised order bounds.

This is a conditional separator subroutine. It is not itself an annihilator acquisition method, a factoring algorithm for arbitrary semiprimes, or a Lean/build certification.
