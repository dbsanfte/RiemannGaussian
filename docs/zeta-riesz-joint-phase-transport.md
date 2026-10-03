# Joint signed phase transport for the balanced-minus-head floor

The open arithmetic target is still the cofinal inequality
\(\operatorname{Re}S_j-H_j\ge-399/5000-o(1)\), with the SAME full signed
ordinary-prime correction \(H_j\). This slice bounds the error in a joint
signed transport estimate. It does not prove the required cofinal cap.

## Checked whole-population estimate

`ZetaRieszJointPhaseTransport` contains every original central balanced
label and every original head pair in one finite disjoint union. Its
amplitude is the original source-scaled Riesz amplitude, or the negative
of the original head amplitude. All physical, count, owner, radial,
allocation and rough-prime masks remain. The phase remains \(y\log n\)
(and \(y(\log p+\log q)\) on the head). No prime completion or zero
hypothesis enters the finite estimate.

For nonnegative pairing masses \(w_{ab}\), retain the signed unmatched
sum explicitly:
\[
U_j=\sum_a
\left(A_a-\sum_b w_{ab}+\sum_b w_{ba}\right)\cos\theta_a.
\]
A pairwise integer lift preserves the exact cosine. Write its phase
difference as \(\delta_{ab}\) and its midpoint as \(m_{ab}\). Keep
\[
M_j=\sum_{a,b}w_{ab}\sin(m_{ab})\delta_{ab}
\]
SIGNED, and charge only
\[
E_j=\frac1{24}\sum_{a,b}w_{ab}|\delta_{ab}|^3.
\]
The checked `central_joint_error` theorem proves
\[
\boxed{
\left|\operatorname{Re}S_j-H_j-(U_j-M_j)\right|\le E_j.
}
\]
In particular, the direct floor is \(U_j-M_j-E_j\). The proof uses the
global trigonometric inequality
\(|x-\sin x|\le |x|^3/6\), not a numerical Taylor approximation.

`cubicCost_le_small_gap` proves the whole-population bound
\[
E_j\le\frac{\varepsilon^2}{24}
\sum_{a,b}w_{ab}|\delta_{ab}|
\]
whenever every nonzero pairing has gap at most \(\varepsilon\).
Thus gaps at most \(1/10\) cost at most \(1/2400\) of their absolute
angular transport. No cofinal small-gap or total-mass estimate is asserted.

The module also defines a deterministic phase-ordered cumulative-mass
coupling with exact tie-breaking and a nearest-integer circular lift.
Its nonnegativity is checked. The native estimate uses the complete
row/column residual above; it does NOT assume complete coverage,
negligible imbalance or unproved marginal identities.

`eventually_joined_floor_transport` spends this estimate on the
existing `joinedPhysical`, keeping the previous high-owner,
allocation, radial and native-error payments. `price` takes the minimum
with the previous funded price. The two alternatives are not stacked.

## Optional finite go/no-go probe

`scripts/probe_riesz_joint_phase_transport.py` tests all-count,
opposite-arithmetic-sign quantile transport. It includes the original
phase and the SAME full prime correction. All 18 complex totals at
\(N=6,7,8\), heights \(54,65,100\), and the two toy radial windows
agree with the frozen critical-shell report.

The first, absolute-chord version improved none of the 12 \(N=6,7\)
previous optimized prices. Keeping the signed first moment improves
all eight genuinely adverse cases. In the four favorable cases the
new signed estimate retains a positive lower bound. An already-zero
old price is not counted as a new saving because of solver roundoff.

Across the 18 cubic tests, the cubic charge is about \(10^{-12}\) to
\(1.2\times10^{-7}\). This is FLOATING exploration, not an interval
certificate or an asymptotic rate.

One adverse example is especially instructive. At \(N=8,y=65\) on the
central toy window:
- the exact joint real total is approximately \(-0.000128091390\);
- the unmatched real sum is approximately \(-0.000068761392\);
- the paired signed first contribution is approximately
  \(-0.000059335782\);
- the cubic cost is approximately \(0.000000023803\).

Both retained signed terms are adverse. A tiny transport defect does
not make either term nonnegative or small.

The probe uses \(L=-2N\log(10001/20000)\), not the native damped
integer length. It does not use the native dyadic schedule or all
native deletion masks. No eventual budget is applied at these toy
orders. The floating greedy coupling is a diagnostic of the
cumulative-mass construction; no interval-certified equality between
its execution and an evaluated Lean sum is claimed. It stays outside
builds and CI.

## What remains

The required next estimate is on \(U_j-M_j\) together, including
unmatched phases. No native cofinal smallness estimate for \(E_j\) is
proved either. Proving only that the cubic charge tends to zero would
not close the floor. Neither another null-profile optimizer nor
a tighter cubic constant can change a genuinely adverse joint total.

The cofinal bound on the new whole price by \(399/5000\), the
multiplicity ceiling \(42/25\), restricted contradiction, zero
exclusion and RH remain OPEN. Preserve the critical-shell
classification and all previous positive/no-go audits.

Validation is local only: strict leaf, targeted build, frozen compiled
ordinary root plus explicit leaf, namespace lint and every-declaration
standard-axiom audit. No root registration, public endpoint changes,
commits, pushes, subagents or wider gates.

See [the focused audit](riesz-joint-phase-transport-audit.json).
