# Independent integration and journal review

2026-10-16. Verdict: PASS on the final bytes below, including the explicit fieldwise-valuation correction. No original or repository file was edited. Durable links are understood as planned publication links for the forthcoming extraction bundle, not as a claim that publication has already happened.

## Exact reviewed integration and report bytes

- `README.md`: 5773 bytes; SHA-256 `0e51ec8d28721c4aecfec1572adbfbbccb6fd2f698c534d209308bf96b9fd394`.
- `journal-entry.md`: 4671 bytes; SHA-256 `47d39431fd6daac5ba190c1b78ca9373a2447dfb025bf3c33acf3235c911a5ce`.
- `diagonal/report.md`: 6653 bytes; SHA-256 `ef999aa2cfbea33c29192035900542808532e906b70a95f55a8c7a30a3819433`.
- `diagonal/diagonal-followup.md`: 9041 bytes; SHA-256 `73685f5580b92375b7d3a9f09265c245125ebee6edf048243a4558b6d5f4e3a2`.
- `commutator/actual-qshift-power-defect.md`: 6120 bytes; SHA-256 `5e88b2b6b26310e535d959b6a4c3320adb25993c5e878fff8577708076007e5a`.
- `mask-separation-review.md`: 7060 bytes; SHA-256 `2077495ac4885bd7251e05b3a7828f096ff3e2879b13ee815fab8f09bbc42a22`.
- `channel_gcd/report.md`: 7714 bytes; SHA-256 `d1f346a636acedf975fb3584bab87b4b9803ade4622c20a90185303ea2803b84`.
- `structured-determinant-primary-note.md`: 2000 bytes; SHA-256 `9159b70bbdc126766ade5a756d89fbf8b56508c9552af2f9c08fd0e2b7ef826a`.

## Integration scope and provenance

The README and journal accurately classify this as partial structural progress with the whole-family acquisition open. They distinguish the newly paid block-pencil operators/generators and square coefficient-block inverse/determinant from the still unpaid compatible ordinary commutator, mixed diagonal, locator or channel remainder. The stated general query clock remains soft O(m^(3/2)); neither the sixth-rate factoring theorem nor a Lean implementation is claimed.

The q-pencil statement matches the independently reviewed exact report, including Q_row orientation, endpoint generators, shared selected-coefficient setup, and absence of 1-z or endpoint/row inversions. Finite degree<J interpolation closure is correctly distinguished from closure of the full degree-L polynomial or a Trummer generator. The ordinary powered-node defect formula and actual rank proof match their reviewed report: the sign is delta_i-delta_j=m^2 for a directed adjacency, the low-phase fibers have at most two tags, and the result does not claim high rank for YS-SY or high operation cost.

The mask conclusions retain their indispensable coefficientwise scope and the fixed-q-binomial syzygy escape. Channel-span rank after dividing H is a constant-linear span claim, not a cheap-gcd or operation lower bound. The local-channel paragraph now explicitly states FIELDWISE common valuation, avoiding a false single valuation in the composite ring at a P-only collision. Safe-center unit ideals do not imply that every individual value or pivot is a unit. The blind-probe failure is only for uniform target-value gcd probes; adaptive/global algorithms remain open.

The final all-restriction claim is a target, not an established result. In particular the new square inverse requires L>=J^2-1 and units through L+J-1; the drafts explicitly refuse to extend it to arbitrary native inputs or arbitrary row/interval restrictions. No additional analytic density or coverage premise is rebranded as new. Primary-source audits are described as prerequisite checks, not as imported successful diagonal/determinant algorithms.

All EIGHT predecessor manifests independently match the pre-entry baseline, and ALL 261 file entries recorded across them independently match byte lengths and hashes. The entire current pre-entry investigation journal also matches its baseline: 1543640 bytes, SHA-256 `046312501e28916020e99b0b510afb1599bb8fb0d6a18455e32748ece7b02ace`. Thus the old packets and journal are unchanged at review time. The new entry reviewed here is still a standalone proposed append; this review does not assert that it is already inserted in the repository journal.

## Independent coefficient-block inverse/determinant proof check

The square followup was independently read in full, rather than accepted only through its other review. All FIVE files and THREE source entries in followup-manifest.json match their recorded sizes and hashes. Its stronger unit premise is essential: c_(Jn) seeds and Q(X_n) use exponents through L, whereas the basis splitting/interpolation uses exponents up to L+J-1. The actual R_P,R_Q>16m^2 promise supplies these units with J<=m-1 and L<=4m^2. This is not merely generic determinant nonvanishing.

At alpha_k=q^(L-k), p_s(alpha_k)=0 for s>k, and the remaining product is exactly

    (q^L)^k product_(h=1)^k(1-q^(-h))
       times product_(h=1)^(J-1-k)(1-q^(L+h)).

All factors are units. Both alpha and X_n=q^(Jn) Vandermondes have unit differences. The triangular evaluation therefore proves a UNIT coefficient-basis determinant and a unit det C0 over Z/N.

The recursive inverse conversion has the correct split boundaries: U_left uses A_l,...,A_(p-1), while V_right uses B_(p-1),...,B_(r-2). Evaluation at alpha_l,...,alpha_(p-1) kills U_left; every V_right value uses factors 1-q^(L+h+1-k) with exponent in [L+1,L+J-1]. Unit-difference interpolation reconstructs N_left; N-N_left V_right is exactly divisible by U_left, whose leading coefficient is a known unit. Every recursion level has total soft O(J) work; parameter inversions, product trees and selected seeds are included. Formal transposition of this parameter-only-inverse linear circuit pays C0^(-T), without weight-dependent pivots. Storage and bit costs are appropriately soft O(J+sqrt L) and the usual log N factor in the intended size regime.

The determinant sign in formula (3) is correct. If P is the coefficient matrix of p_s, then eval_alpha(P)=V(alpha)P is triangular while eval_X(P)=V(X)P. Hence det C0 contains V(X)/V(alpha), not its reversal, and no row reversal sign is missing. The geometric Vandermonde exponent J(J-1)(J-2)/6 equals sum_(i<j)i. The weighted diagonal factors are correctly collected. The Q(X_n) products cover exactly exponents 1,...,J^2-1 except nonzero multiples of J, giving the stated q-factorial ratio. A scalar block acquisition computes this horizon-J^2 q-factorial in soft O(J), with no expansion of a J^2 table. Together with the shared seeds, all determinant constants and unit inversions are genuinely paid at soft O(J+sqrt L).

Finally, M=C0 W has unit determinant on the actual nodes, so a short ordinary separable representation of that specified block kernel is impossible. This is not a Cauchy/displacement-rank bound and does not survive arbitrary multiplication as a rank theorem for S. Cheap det C0 also does not compute det(I+diag(theta)S): multiplicativity does not remove the added identity, independent row weights, ragged correction or rectangular factors. The integration drafts preserve all these limitations.

The primary-text audits and their saved payload hashes were checked for provenance; no claim of independent full-paper re-verification is made by this integration review. The constructive algebra, costs and scope above were independently verified directly. No correction beyond the already applied word “fieldwise” is requested.
