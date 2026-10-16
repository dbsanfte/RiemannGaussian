# Weighted q-descent fails on the actual carrier; boundary acquisition remains open

2026-10-16. **A rigorous obstruction to regular, support-preserving fixed-carrier monodromy, plus paid spectral and boundary diagnostics.** This does not prove the whole-family softly O(m) collision query or an improved factoring exponent. Three user-authorized Sol 6.1 agents investigated in parallel. The new main proofs have independent final-byte reviews.

The [previous extraction packet](../semiprime-extraction-query-20261016/README.md) supplies block inverses, a paid q-pencil and a conditional quasiseparable normalized operator. This packet resolves its weighted-descent caveat and pays the remaining spectral uniqueness check. It also proves a uniform pole count for one canonical contraction. The general acquisition bound is still softly O(m^(3/2)).

## 1. Actual weighted-descent obstruction

The [weighted-descent proof](reports/weighted-descent.md) considers a regular weight w=A/B, with B a unit modulo H=prod(t-z_i). The rule f -> w(t)f(qt) is well-defined independently of polynomial representatives modulo H exactly when

    H divides A(t) H(qt).

On the literal quadratic row catalog, qz_i=z_j is equivalent to delta_i-delta_j=m^2 as an INTEGER. The offset span and local-order promise make the equivalence exact in both hidden fields. Each low-digit quadratic fiber has at most two tags, so these adjacencies are disjoint pairs. At least ceil(J/2) nodes are dangling: qz_i is outside the supplied set.

Every descending numerator must vanish at those nodes. Thus a nonzero such numerator has degree at least ceil(J/2), and any descending weight kills linearly many of the actual unit rows. A multiplier preserving their zero/nonzero information cannot give this descent. In particular the normalized degree-one weight (1-t)/(1-q^L t) does not descend for J>=3 on its unit-denominator branch.

The exact universal boundary map on representative changes H g, deg g<J, has rank #{i:w(z_i)H(qz_i)!=0}; this is Omega(J) for a weight preserving the unit rows. On H^s, closure requires the weight to vanish to order s at every dangling node and kills its entire regular s-jet there. More homogeneous jet precision does not preserve the missing payload.

These are actual-source algebraic obstructions to the specified descent contract. They are not operation lower bounds. Canonical interpolation operators remain valid cheap matrices. A fixed F can have special syzygies. A gauge with zeros at shifted nodes can repair formal descent, but at dangling unit rows F/G then has genuine poles at those successor points. Rational finite parts, residues and inhomogeneous corrections remain possible, with their acquisition charged.

## 2. The linear boundary solver is paid; its forcing is missing

For the actual q-factorial, U_w F=F holds rationally. Its canonical compressed operator U_H has I-U_H invertible on the unit-boundary branch. If F=r+H G and f_i=F(z_i), the exact equation is

    (I-U_H) f = (w(z_i)H(qz_i)G(qz_i))_i.

The right side is not zero on the retained family. Discarding it would falsely force all row values to zero, despite the many unit rows.

The [explicit inverse algorithm](reports/boundary-inverse.md) pays (I-U_H)^(-1), including setup, in softly O(J) over the composite ring under the stated unit conditions. Its coefficient-basis solver uses an upper-bidiagonal matrix with one companion row. The first diagonal entry is zero, but off-diagonal unit pivots determine x_1,...,x_(J-1), and the last row determines x_0. No row value or zero pivot is inverted. Thus the row list and its quotient-tail forcing interconvert cheaply once either is supplied. Acquiring that forcing remains the query gap; its density for this fixed F is not claimed.

## 3. Spectral tests are cheap but lack the required arithmetic implication

The [spectral check](reports/spectral-check.md) acquires the full degree-J determinant polynomial

    phi(X)=sum_(k=0)^J h_k prod_(s<k)(1-Xq^s)
                              prod_(k<=s<J)(q^L-Xq^s)

in softly O(J), then all complete-block spectral values in softly O(J+L/J). Proper gcds give factors; unit values certify uniqueness of the normalized Sylvester equation on its unit-boundary branch. Saturated branches are not resolved here. The first spectral test is always a unit on the actual source; a terminal endpoint test is also a unit when its divisibility condition holds. The forced original collision therefore does not reach those endpoint tests.

A [separate avoidance theorem](reports/promise-level-spectral-avoidance.md) constructs a proper hit with every spectral value a unit under the abstract subgroup/order promises. **It does not satisfy the literal quadratic tag catalog** and is not an actual-source counterfamily. It shows that any successful spectral forcing theorem must use additional catalog arithmetic. The source-specific interior spectral implication remains unproved.

## 4. Canonical rational contraction has linearly many genuine poles

The [pole-count theorem](reports/pole-count.md) takes dyadic J<=B<2J, JB<=L, M=J(B-1), and local order greater than L+M. It proves that the canonical negative-index mask contraction has at least ceil((J-1)/2) genuine poles in each hidden field after all cancellations. The original long window and retained local-order promises satisfy these conditions without a new deletion.

Reversing the mask turns the residues into early coefficients of a q-product times the reversed mask. Multiplication by the reversed degree-J target polynomial exposes forcing only at multiples of B. Unit contiguous q-binomial minors force a nonzero coefficient in each of J-1 blocks; each coefficient before multiplication can influence at most two blocks. This gives the pole bound without generic nonvanishing.

It excludes a polylogarithmic total literal pole list. It allows an O(J)-size rational representation, which could fit the desired clock if acquired cheaply. It also allows different q-Ore representatives or finite-sample interpolants. No superlinear acquisition bound follows from this pole count.

## 5. Literature and verification

The [primary-source audit](reports/literature-audit.md) checks rational polynomial preprocessing (September 2026), elliptic butterflies (March 2026 revision, publication forthcoming), truncated resultants, and linearized/Ore operations. Their inspected interfaces require unacquired coefficients/basis data, different orbit promises, or degree-L work. No applicable mixed-contraction theorem was found. The primary PDF/text payloads and exact inspection scope are preserved; this is an applicability audit, not an exhaustive literature claim.

The manifest and source map pin the new proofs, independent reviews, inherited premises and primary payloads. All nine predecessor packets and exact journal entries remain unchanged. These are classical proofs; no new Lean theorem, benchmark or broad build establishes a whole-query improvement. The remaining substantive target is a restriction-stable softly O(m) acquisition of the quotient forcing, a channel remainder, the collision locator, or another sufficient factor-selective consequence. The full bit-complexity and Lean sixth-rate composition are still required after that.
