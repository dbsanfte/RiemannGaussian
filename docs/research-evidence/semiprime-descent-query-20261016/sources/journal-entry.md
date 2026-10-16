## 2026-10-16 — Actual weighted-q descent loses unit rows; spectral and boundary solvers are paid

The [descent packet](research-evidence/semiprime-descent-query-20261016/README.md)
proves a new actual-source obstruction to regular homogeneous fixed-carrier
monodromy. It also pays the spectral uniqueness check and the normalized
boundary inverse. The whole-family soft O(m) collision query remains open;
the general soft O(m^(3/2)) acquisition bound is unchanged. Three authorized
Sol 6.1 agents investigated in parallel; the main proofs have independent
reviews of their final bytes. These are classical arithmetic results.

**Weighted closure fails for the actual carrier if it preserves unit rows.**
For H=prod(t-z_i), a regular rational weight w=A/B with B unit modulo H
gives a representative-independent operation f -> w(t)f(qt) modulo H iff

    H divides A(t)H(qt).

On the literal quadratic catalog, qz_i=z_j is equivalent to the integer
identity delta_i-delta_j=m^2. The local-order/span bound prevents wraparound;
the low-digit quadratic fibers have at most two tags. Thus adjacencies are
disjoint pairs and at least ceil(J/2) nodes have no successor in the set.
Every descending numerator must vanish there. A nonzero numerator requires
degree at least ceil(J/2), and any such closure kills Omega(J) of the actual
unit rows. The normalized degree-one weight (1-t)/(1-q^L t) therefore
cannot descend for J>=3 on its unit-denominator branch.

The boundary map on arbitrary representative changes H g, deg g<J, has
exact rank #{i:w(z_i)H(qz_i)!=0}. It is Omega(J) for weights preserving the
many unit rows. Closure on H^s requires weight zeros of order s at the
same dangling nodes and kills their entire regular s-jets. Rational gauges
with zeros at shifted nodes can repair formal closure, but F/G then has
genuine poles at those successors of unit rows. This is an escape with
unpaid rational boundary information, not a proof against every gauge or
all fixed-F q-syzygies. High boundary rank is not an operation lower bound.

**The normalized linear equation is inexpensive; its forcing is missing.**
Although the rational operator fixes F=P_L, its canonical compressed matrix
U_H has I-U_H invertible on the unit-boundary branch. For F=r+H G the
correct equation is

    (I-U_H)(F(z_i))_i=(w(z_i)H(qz_i)G(qz_i))_i.

Discarding this boundary would falsely force every row to zero, contrary
to the actual unit rows. A new explicit soft O(J) ring-safe inverse for
I-U_H uses off-diagonal unit pivots in a bidiagonal-plus-companion system;
it does not divide by its zero first diagonal entry or by row values.
Thus solving the equation is paid once the quotient-tail forcing is
supplied. No acquisition or density theorem for that fixed forcing vector
is claimed.

**The spectral uniqueness check is now paid.** A split-Newton product
acquires the full degree-J pencil determinant phi in soft O(J); monic
multipoint evaluation pays all complete-block tests in soft O(J+L/J).
Proper gcds factor N; unit values certify uniqueness on the unit-boundary
branch. Saturated cases are not resolved here. The first spectral value
is always a unit on the actual catalog despite the guaranteed original
collision; a terminal endpoint is also a unit under its stated condition.
A separate nonvanishing-grid theorem constructs forced hits with all tests
unit under the abstract subgroup promises. It does NOT impose the literal
quadratic tag map and is NOT an actual-source counterfamily. A catalog-
specific interior spectral forcing theorem remains open.

**A canonical rational index contraction has Omega(m) genuine poles.**
For dyadic J<=B<2J, JB<=L and local order>L+J(B-1), a reversal and sparse
forcing identity reduce residue support to coefficients of a q-product
times the reversed mask. Unit contiguous q-binomial minors force a nonzero
in each of J-1 blocks; one pre-multiplication coefficient reaches at most
two blocks. At least ceil((J-1)/2) poles survive in EACH hidden field.
The actual long-window constants satisfy the hypotheses without deletion.
This excludes a polylogarithmic total literal pole list, while allowing
an O(J)-size representation, finite-sample interpolation and other q-Ore
representatives. It gives no superlinear operation bound.

Fresh primary checks of rational preprocessing, elliptic butterflies,
truncated resultants and linearized/Ore algorithms did not pay the mixed
contraction. All nine predecessor packets and exact journal entries remain
byte-unchanged. No new Lean declaration or benchmark is substituted for
the missing acquisition theorem. The next required advance remains a soft
O(m), restriction-stable quotient forcing, channel remainder, collision
locator or sufficient factor query; full bit-complexity and Lean composition
remain after it.


