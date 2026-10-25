
## Implicit coefficient access and dense recurrence action, 2026-10-24

Positive initialized primitives, no whole-query exponent improvement.
For P_b(X)=prod_(i<b)(1-q^i X), native q=z has all short q-differences
through C=16k^2 certified units, b<=L=2k^2+2. ANY T requested factorial
prefixes cost soft(sqrt b+T): shared coarse blocks plus one actual MPE
per dyadic tail size. Selected coefficients follow by q-binomial unit
divisions. One fixed sparse digit mask and ALL R consecutive clock
values cost soft(sqrt b+t+R), with actual fraction-tree initialization
and constant-one series inversion; aliases and zero outputs are safe.

Stronger dense action: reshape M[rho,r]=c_(D rho+r)*x^(D rho+r), with
D,H~sqrt b and final padding explicit. Arbitrary supplied v gives ALL
H entries M v in soft sqrt b, including row-start coefficient acquisition.
Ratio (1-q^(r+1)U)M[rho,r+1]=x(q^b-q^r U)M[rho,r], U=q^(D rho),
reduces all rows to ONE acquired rational Newton expression. Balanced
(P,Q,S) prefix-sum tree and MPE pay degree D plus H actual row nodes.
Do not invert x, coefficients, or final sums. Respect final denominator
indices/tails. This also pays ONE arbitrary separable row/column mask,
even dense digit-product masks; it is not a low-rank coefficient claim.

Transpose of this fixed-input linear circuit is also paid. For ONE outer
vector u, acquire M^T u and then ALL 6^m inner singleton/pair masks by
6-by-4 tensor transforms in soft(sqrt b+H+D+6^m), D=4^m. Balanced
D,H give soft b^0.6463; this standalone balance is not automatic in the
actual thin layout. No per-mask square-root repetition. Actual tensor
outer weights still vary with Q. ONE complete fixed-Q mixed-radix
coefficient-band box is soft sqrt b via a balanced digit cut (or direct
selected coefficients for a short block). All-Q/full-leaf sharing is open.

For original P_b(y), BOTH u_rho=y^(D rho) and v_r=y^r vary with y.
The remaining constructive target is simultaneous paired moving-vector
contractions across the original target family (or its zero-safe restricted
product). Fast action for one vector is NOT that acquisition theorem.
Current complete query remains soft(J+sqrt(JL))=soft k^1.5; one-sixth
and full executable/Lean bit composition remain open, goal active.

One residue's T AP coefficient-prefix sums also cost soft(sqrt b+T),
via actual degree-D order-two q-blocks or sparse enumeration for large D.
Exact thin-tensor encodings still sum active Q and ternary outer boxes.
One active Q collapses to matching singleton products; full preencoding
writes too many leaves. Both tested literal output reductions retain
unpaid native weighted contractions or excessive explicit outputs.
These are scoped costs, never a generic lower bound.

Exact native block: prod_(r<b)(V_j-q^(ab+r))=V_j^b P_b(q^(ab)/V_j).
Preserve all original row/block/tail labels and saturated-leaf consumer;
auxiliary mask or box zeros are not factoring witnesses. Proofs/reviews/
validator: /tmp/semiprime-implicit-thin-encoding-20261024. Preserve prior
shared prefixes, all 270 frozen entries and concurrent RH work.
