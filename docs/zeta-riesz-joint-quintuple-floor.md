# A signed bound for five-prime labels with two small factors

[`ZetaRieszJointQuintupleFloor`](../RiemannGaussian/ZetaRieszJointQuintupleFloor.lean)
proves a sign and amplitude bound on the actual retained five-prime
coefficient. This extends the small-factor cancellation to the first
class with a surviving pair boundary. It does not complete a prime sum,
average its phase or establish the whole joint floor.

Let `n = p*q*r*a*b` be on the smaller-count core after the already paid
60.1% prime-share deletion, where all five factors are prime and
`a,b <= N_j^2`. The existing masks imply

\[
\log(ab)\le N_j/2048,\qquad
1.95N_j<\log n\le2.03N_j,\qquad
\log p,\log q,\log r<0.601\log n.
\]

The actual length eventually satisfies `1.37N_j <= L_j <= 1.4N_j`.
The lower bound is proved on the same restricted radius interval; it
is not an additional open estimate.

## Surviving signs and their quantitative cost

Three prime insertions against the small composite `ab` leave exactly
the three pair-boundary responses:

\[
\mathcal R_L(n)=
\mathcal R_{L-\log(pq)}(ab)+
\mathcal R_{L-\log(pr)}(ab)+
\mathcal R_{L-\log(qr)}(ab).
\]

Every displayed response is the existing nonnegative two-prime tent.
The original unit and single-prime terms vanish by complete small-factor
cancellation; the triple term has a nonpositive cutoff. No terms are
discarded by absolute value.

The core gives `2 log n + log(ab) <= 3L`, which forces at least one of
the three pair tents to vanish. Therefore

\[
0\le\mathcal R_L(n)\le 2\min(\log a,\log b).
\]

Writing `theta_N(n) = boundedShare ...`, `five_residual_bounds_core`
proves the literal allocated coefficient satisfies

\[
-\frac{\log n}{L}(1-\theta_N(n))\,2\min(\log a,\log b)
\le \operatorname{Re}(\mathrm{residualCoefficient}(n))\le0.
\]

All factorization, count, physical, squarefree and allocation conditions
remain in the theorem. Unlike earlier owner-based sign tests, no
distinguished prime above `sqrt(n)` and no unpaid pair-separation
hypothesis are needed here.

## Phase correlation remains essential

`re_five_residual_nonneg_core` proves that these atoms contribute
nonnegatively when the **actual complex observation** has nonpositive
real part. The observation can include the full factorial kernel and
source scaling. Thus their arithmetic sign opposes the positive
three-prime coefficient on that same phase sector.

This is a sign estimate, not a population comparison or a free positive
reserve. The opposite phase sector remains in the signed core. The
theorem does not match five-prime labels to troublesome triples or
bound their joint sum at source scale.

The [optional rational probe](../scripts/probe_riesz_joint_quintuples.py)
records its [exact finite diagnostics](riesz-joint-quintuple-probe.json).
The example with large logarithms
`37/50, 63/100-3/16384, 63/100-5/16384`, small logarithms
`1/8192, 3/8192`, and cutoff `137/100` has tent values
`1/8192, 1/8192, 0`. Lean also checks this equality. It shows why a
smaller universal scalar cost is unavailable from these inequalities
alone. These rational logarithms are **not asserted to be logarithms
of actual primes**.

The independent joint `-79/1000-o(1)` floor, the cancellation across
actual labels and prime counts, and the RH contradiction remain open.

The subsequent [small-descendant audit](zeta-riesz-small-descendants.md)
checks the quantitative limitation: away from the pair boundaries,
appending composite small factors to a balanced triple gives exactly
zero, and all surviving prime insertions together supply only a vanishing
fraction of that triple's weight. Their favorable arithmetic sign alone
therefore does not close the joint estimate.
