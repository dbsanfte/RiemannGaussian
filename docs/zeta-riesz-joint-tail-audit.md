# The actual central binomial tails grow

[`ZetaRieszJointTailAudit`](../RiemannGaussian/ZetaRieszJointTailAudit.lean)
strengthens the earlier scalar-tilt audit. At the upper radius
`U = 10001/20000`, the **actual binomial tails**, with both integer
unpaid-order endpoints retained, grow under the scalar source scaling.
This is not a bound or a divergence theorem for the signed prime sum.
No new carrier is defined.

Write the existing allocation weight as

\[
b_N(k;x)=\binom{N+1}{k}x^k(1-x)^{N+1-k},\qquad
\mathcal U_N=\{k:k\le\lfloor13N/32\rfloor,\;5(N+1-k)<4N\}.
\]

For every `N=32m`, `m>=10`, Lean proves

\[
(2U)^{N+1}\sum_{k\in\mathcal U_N}b_N(k;41/100)
\ \ge\ \frac{(1001/1000)^m}{3(N+1)},
\]

\[
(2U)^{N+1}\left(1-\sum_{k\in\mathcal U_N}b_N(k;2/5)\right)
\ \ge\ \frac{(2001/2000)^m}{3(N+1)}.
\]

The first cofactor share corresponds to a 59% marked-prime share; the
second to 60%. Both lower bounds tend to infinity, including on the
original `dyadicMomentOrder` schedule. Thus even a cofinal constant scalar
allowance cannot pay these particular tails. The theorem is at `U`; it
does not assert these same numerical endpoints obstruct every smaller
radius.

## Proof and diagnostic

The proof uses an exact binomial balance identity. At an integer mean, a
modal atom has mass at least `1/(N+1)`. Changing the parameter from
`13/32` to the stated cofactor share retains the exact likelihood ratio.
The atom at `13m` lies inside the literal unpaid set, while `13m+1` lies
outside it. Two rational power inequalities certify the positive growth;
no floating-point logarithm, Stirling approximation or optimal-tilt
assumption enters the Lean proof.

The [optional probe](../scripts/probe_riesz_joint_tails.py) records the
[uncertified diagnostic](riesz-joint-tail-probe.json). It subtracts the
lower excluded tail for the assigned mass and adds both tails for the
missing mass. Full finite enumeration independently checks its endpoints
and recurrence at small orders.

The values below are **natural logarithms** of the scaled scalar tails,
not prime-sum values:

| N | Assigned tail at 59% | Missing tail at 60% |
|---|---:|---:|
| 1,536 | -0.8011 | -1.0294 |
| 8,192 | -0.5839 | -1.2706 |
| 65,536 | 2.8835 | -0.9544 |
| 262,144 | 16.2498 | 2.0957 |
| 4,194,304 | 293.7102 | 74.4721 |

The initial decrease, especially in the second column, is not evidence of
asymptotic decay. The displayed numerical values are exploratory; the
rational lower bounds above and their limits are the certificates.

## Consequence for the joint floor

The [outer radial bounds](zeta-riesz-joint-radial-floor.md) remain valid.
They retain total-log information and exclude the central saddle; this
audit does not invalidate their savings.

The [joint floor](zeta-riesz-joint-floor.md) still requires cancellation
in the retained raw Riesz sum and its allocated central transition. The
assigned and unassigned pieces must not be charged these tails as
vanishing scalar errors at the central saddle. Their signed arithmetic
correlations, full phase and complementary contribution remain available.

This audit does **not** show that an actual prime population realizes the
scalar lower bounds, does not evaluate the radial integral, and does not
give an independent floor for `J_N+C_N`. No RH contradiction or new zero
exclusion follows. No separate-component bound is added as a prerequisite
for the joint cofinal target.
