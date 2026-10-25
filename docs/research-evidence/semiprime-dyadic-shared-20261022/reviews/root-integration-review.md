# Root integration review: acquired sparse norms, scoped whole-family gap

2026-10-22. Reviewed all archived research reports, the independent
denominator/tangent/prefix reviews, and the stable reference implementation.
Root replayed all five test groups successfully. The proof is an algorithmic
acquisition result for one supplied direction; no sixth-rate claim follows.

## Independent proof outline and generality

The construction works for F=g(X)-z*X^s*f(X), with f,g supplied of degree
at most two, and one polynomial U of degree L<=2m. The report/program's
displayed squared rational base is one specialization. Norms are taken in
the finite free Laurent algebra

    (Z/N)[Y,Y^-1][X] / (X^p-Y).

Thus negative s is legal without silently assigning a negative power to
zero. Evaluation of returned negative Y powers requires a unit Y.

In a norm monomial with j choices of the z term, the original X exponent
is between sj and sj+2p. Norm invariance leaves exponents divisible by p,
equivalently as follows directly from the even-product recurrence.
Consequently each coefficient of z^j has at most three spatial slots.
In the epsilon coefficient there is exactly one U insertion, giving the
interval [sj,sj+2(p-1)+L]. No derivative of a cyclic representative is used.

At p->2p, remove A=floor(s/p) from the slope and put r=s-Ap. The complete
denominator product has normalized interval [rj/p,rj/p+4]; each tangent
cross-product lies in [rj/p,rj/p+4+L/p]. The opposite factor's sign is
(-1)^(e_stored+A*j), not merely (-1)^e_stored. Restore that actual exponent
before testing evenness and halving. This retains negative-shift carries.

For precision h, both inputs have degree at most q=min(p,h-1). Interpolate
the FULL product through degree 2q on its known candidate support, then
discard j>=h. Nonnegative z degrees ensure this preserves the requested
prefix. The radix 2q+1 is injective on this complete candidate. The coarse
exponent bound below 10m^2 follows from q<=p, p<=m/2 and L<=2m. Hence eta's
prepared local orders above 16m^2 make every distinct interpolation-node
difference a unit. There is no unknown-support sparse interpolation step.

Let alpha_i be these nodes. Moment values are coefficients of
sum_i c_i/(1-alpha_i*z), acquired by a rational product tree. For inverse
moments, D=product_i(1-alpha_i*z), P=D*M mod z^T, where M is the T supplied
moments. Then

    c_i = -alpha_i * P(alpha_i^-1) / D'(alpha_i^-1).

The derivative denominators are products of unit node differences and
unit factors. Monic remainder trees evaluate the numerator and derivative.
All these operations are valid over the composite ring. Multiplying
the two moment vectors pointwise therefore pays each sparse product.

The stage support is O((q+1)(1+L/p)); summing it gives the independently
reviewed O(h*(1+log(m/h))+L*(1+log h)) bound for h<=m. With h=1 the sum is
O(log m+L). Full output uses the geometric sum and costs soft O(m+L).
Startup reads O(L+1) coefficients. The tangent is linear in the supplied
U, so its transpose has the same arithmetic-circuit cost for a FIXED base.

The identity V/Q=Tr(U/F) follows by first-order determinant expansion over
dual numbers. It may be specialized at Y=1 and expanded as a series when
Q(0) is a unit. For U=B*g it gives Tr(B/(1-z*X^s*f/g)). Native g is a
cyclic unit by the prepared gamma-order promise. For arbitrary supplied
f,g, the norm constructor remains valid without this extra unit promise;
the trace-division application does not.

## Residue-bit and implementation boundary

Fast coefficient arithmetic need not be field-only. Polynomial products
over Z/N may be reduced to integer products by packing coefficients in
base 2^k with 2^k greater than the maximum convolution coefficient bound
n*(N-1)^2. Fast integer multiplication gives the usual softly linear
polynomial bit bound. Fast monic remainders use reversed series division
with constant one. Product trees, Newton inversions and monic multipoint
evaluation therefore require no inverses of arbitrary polynomial leading
coefficients. Scalar unit inverses use extended gcd.

Node exponents have O(log m) bits; removed and restored Laurent exponents
also charge O(log(2+|s|)) bits. A suitable explicit bit form is

    soft O((h+L)*(log N + log m + log(2+|s|))).

This includes the dyadic-depth and polynomial-arithmetic logarithms. The
native shifts have polynomial magnitude in N, giving the advertised soft
O(h+L) bit notation. The bound is not independent of reading an enormous
arbitrary s. Product-tree storage is softly bounded by the same data size.

The reference follows the actual sparse moment/interpolation architecture,
but uses schoolbook multiplication and monic remainders. Its correctness
tests are not a timing proof. Test factors are used only to prepare test
nodes; acquisition receives neither factor. Invalid separation may return
a proper gcd or a saturated error; the expensive invalid-input fallback
is not charged to the promised separated-node execution.

## Whole-family and source checks

The fixed-U theorem does not directly acquire
CT[rho_(u*a)(W^N) R^a]. Its weighted-log form has different shifted bases,
not coefficients of one common linear perturbation. A logarithm of a sum
introduces mixed powers of the weights and changes the target. Likewise,
the transposed circuit fixes the base and does not transpose an unacquired
discrete exponent parameter for free.

The proposed per-level scalar support ledger would be O(m) if every
folded direction were supplied in the required fixed-polynomial form.
The phase report correctly identifies the missing contraction. For dyadic
m=p*d, Y=X^p and zeta_p=X^d are dependent coordinates. Automorphisms of
phase data also move the rational base; R(X^sigma) is not R(X)^sigma.
At p=m the proposed terminal operation is the original diagonal again.
This is a precise unfilled algorithm interface, not an impossibility proof.

The additive fold is valid on its primitive component with normalized
trace weights. Lower-order components must still be included. The native
ell_j and long seed I remain outside the aligned H_a primitive. Relative
norms of target-minus-seed must retain both seed conjugates when the seed
is not fixed by the relative involution.

For the direct scalar route, the q-Newton formulas were checked on the
monic top basis vector: DC-qCD=(q^J*F-F(qX))*e_last^T. They pay the stated
sparse operators but do not compute the long determinant. The geometric
block-resultant and finite stationary compensation retain their original
source products, with no cross-difference inverse. Native half-tag
transport changes to odd seed phases; it does not supply their startups.

One scratch premise was corrected before archiving: gamma=t^2 having odd
local order does not by itself imply t has odd local order. The projection
equivalence needs only the even gap d: t^d=gamma^(d/2), and odd order makes
gamma^(d/2)=1 equivalent to gamma^d=1. The archived report uses this proof.

## Full goal and preservation

The authoritative original scalar controller already pays public
preparation and exceptional branches, including its unconditional
unbalanced short-annihilator extraction. Its bounded-leaf decoder has no
QRH premise. The broader long-annihilator route has a different contract;
those assumptions are not mixed here. Root read the paid setup report
and retains its distinction between classical bit proofs and noncomputable
Lean interfaces. No new number-theoretic preparation gap is invented.

The missing substantive theorem remains a deterministic restriction-stable
whole-source collision evaluator in soft O(m) bits, or a different complete
factor-or-witness algorithm. It must be integrated with original recovery
and a full controller bit proof before claiming the 1/6 goal. This packet
supplies a real arithmetic primitive and tests its implementation, while
leaving that theorem explicitly open.

All twenty imported artifacts were copied verbatim after their final
reviews. The seven earlier manifests and their 143 entries were checked
before new packet creation. Final source pins, links and manifest checks
are recorded in validation.json. No historical frozen entry is edited.
