# Testing the selected geometric norm contraction

26 October 2026. This pass executes three proposed shortcuts for the
[compact norm](../semiprime-separated-selector-20261026/README.md).
It does **not** establish the required whole-family soft-K acquisition.
The retained uniform query bound is soft K^(5/4), and the all-semiprime
sixth-rate acquisition, full bit proof and Lean theorem remain open.

There is one useful paid operation: the first and last M coefficients of
the marked block polynomial are acquired in soft(J+M), so coefficient
strips of length sqrt(h) fit the target budget. The attempts to convert
these strips, known singular projectors, or a short boundary sum into the
selected residue leave an explicit interior rational functional unpaid.
These are scoped candidate failures, not a general impossibility result.

## Scalar formal solve: both coefficient strips are acquired

Let F_e be the acquired degree-J physical row polynomial over the fixed
three-dimensional jet algebra, and

    R_b(S)=prod_(u<b) F_e(q^u S).

Writing f=F_e/F_e(0), the exact finite-product identity is

    R_b(S)=F_e(0)^b exp(sum_(n>=1)
               (1-q^(bn))/(1-q^n) * [S^n]log(f) * S^n).

Formal inverse/log/exp gives its first M coefficients in soft(J+M);
reciprocal reversal gives its last M at the same cost. All integer and
q-gap inverses are certified in the stated precision range. This improves
the formal coefficient initialization, not the completed query bound.
See [the algorithm](qdifference-contraction.md) and [review](review-qdifference-contraction.md).

For the actual giant polynomial G_c, write R_b=r+G_c*t. The exact quotient
equation retains

    F_e(S)r(qS)-F_e(q^b S)r(S)
       =-F_e(S)G_c(qS)t(qS) mod G_c.

The shifted factor G_c(qS) is a certified unit when b>1. It does not
annihilate the omitted quotient. Obtaining this correction or the selected
norm directly remains necessary; a formal Taylor prefix cannot simply
replace values at unit giant nodes.

## A known singular projector and its actual contraction

The mixed higher-operator pencil det(I-uA-vM) has an explicit soft-J
formula on every fixed affine parameter line. On v=1-u its singular
modes are known short endpoint polynomials. The u=0 projector is exactly
evaluation at zero, with acquired row weights

    l_j=-D(0)/(T_j D'(T_j)).

Pairing this with the corresponding clock projector collapses all row
summands to a scalar Cauchy sum with denominator D(q^i); the reverse
contraction uses reciprocal W_h(T_j). All boundary normalizations are paid.
The remaining interior sum is still the selected long operation. Moving
the projector's center to the actual hit requires a long shifted-clock
ratio. See [the executed pairing](singular-pairing.md) and
[its review](review-singular-pairing.md).

## Boundary cancellation with the pole retained explicitly

For the two geometric axes x_u=q^u, y_v=q^(bv), acquire the unit weights

    alpha_u=x_u^(b-1)/B_b'(x_u),
    beta_v=y_v^(c-1)/G_c'(y_v).

Their short moments are products of two Gaussian binomial coefficients,
with paid finite recurrences. Exact double summation by parts reduces the
weighted rational sum to b+c-1 boundary evaluations and a mixed interior
difference. The boundary evaluations and their actual factor-or-unit
checks fit soft(J+b+c). On continuation their residues vanish.

The remaining rational numerator has degree O(J) and is also acquired.
Its four shifted denominators retain the entire good pole: the coefficient
at a unique hit is exactly alpha_(u*)*beta_(v*). Using the paired numerators
F' and H_w gives a common nonzero amplitude and the correct row-mark ratio.
The explicit [reduction](selected-condensation.md) and
[review](review-selected-condensation.md) record all boundaries and sources.

Combining this with the newly acquired coefficient strips gives an exact
test, rather than a degree heuristic. For p=F' or H_w,

    p/(F+delta)=P_<M+t^M E_M/(F+delta), deg E_M<J,
    theta^M E_M(theta)|_(delta=0)=p(theta)

at every physical hit theta. The acquired polynomial strip is regular in
delta. The remainder carries the full desired residue. The same holds for
the reciprocal strip. The transformed numerator pair is legal and cheap,
but its rational functional still needs evaluation.

Finally, the full-clock Pearson weighting was tested with an explicit
same-denominator Gosper numerator. The first forced numerator is acquired;
after the actual shifted-root and endpoint gates, the full certificate
would force its source numerator to vanish at the good hit. This rules
out that certificate while preserving the possibility of a different
pole-transport algorithm. The [root review](review-full-clock-certificate.md)
checks this limited conclusion and the required one-step endpoint.

## What this changes next

Coefficient startup and short boundary evaluation are now concrete paid
operations. In the three tested combinations, the unpaid information is
the selected pole of a rational functional, or the equivalent giant-grid
quotient correction. A further shortcut must compute that quantity or
transport its pole to an actually acquired boundary with nonzero amplitude.
Dropping the interior term, applying an uninitialized quotient shift, or
substituting the evaluation-at-zero projector cannot do so.

No additional native examples, certificates, benchmark campaign or backend
Lean lemmas were added. The validation here is independent paper review,
primary-source checking, and repository preservation. See [review.json](review.json)
for the exact scope. No commit or push in this pass.
