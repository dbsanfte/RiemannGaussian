# Arithmetic payment for per-leg pole removal on the signed prime correction

`ZetaRieszPrimeHeadPolePayment` proves a geometric source-scale bound for
the change made by applying the existing shifted-center pole killer to
each of the two actual prime legs of the correction. The original
correction remains signed and nonzero. The balanced main is unchanged.
The independent whole-sum floor is still open.

The proof keeps the same ordinary-prime pairs, physical owner cutoff,
polynomial cofactor sieve, moving Riesz length, complementary factorial
orders and full product phase. In particular, orders zero and one remain
in the exact finite sum. No cofactor is completed, and no complete-leg
phase limit is transferred through a hard mask.

## Checked estimate

Let `H_N` be `originalHead`, the complex version of the already
source-normalized native correction. Its real part is exactly
`nativeHead`. Let `C=(3/2+iy)/(1/2+iy)`. For every retained order `k`, the
new atom multiplies its original factorial mass by

\[
\left(1-\frac{C^{N+1-k}}p\right)
\left(1-\frac{C^k}q\right).
\]

`filteredMass_kernel` identifies this with the product of the two actual
shifted-center kernels. It is not a total-order polynomial filter.

On the original owner and cofactor support, `head_prime_logs` proves

\[
\log p\ge\frac{51}{50}N,
\qquad \log q>\frac7{10}N.
\]

The second inequality follows directly from the literal integer lower
endpoint; no rounding loss or prime-density estimate is assumed. For
`N>=64`, both leg orders are at most four times their respective prime
logs. The existing bound on `C` then gives the per-slot estimate

\[
|\text{multiplier}-1|\le3e^{-2N/3}.
\]

Summing the exact nonnegative factorial mass retains `ownerWeight` on
this error. Harmonic aggregation pays the whole operator change:

\[
\boxed{
\|\widetilde H_N-H_N\|
\le 10(N+1)^3e^{-N/2}
}
\]

for `0<=u<=10001/20000`, `54<|y|` and `N>=64`. The physical prime set
itself proves `log p<=length u N`; no eventual length premise is needed.
The estimate is uniform in the height. Only the error uses the positive
radial envelope; neither the head nor the balanced main is norm-paid.

`budget_lt_native` proves the rational bound

\[
10(N+1)^3e^{-N/2}<10^{-40}\qquad(N\ge256).
\]

This includes the first native order and all later native orders. It is
a Lean certificate from a finite exponential-series lower bound and
monotonicity, not an extrapolation from the small-order probe.

## Exact joint ledger

`tendsto_central_sub_filteredHead_sub_native` shows that

\[
\Re(\text{centralRest}_j)-\Re(\widetilde H_{N_j})
-\Re(u^{N_j+1}\text{coreResponse}_j)\longrightarrow0.
\]

`eventually_joined_floor_of_joint` transfers any actual independent
one-sided estimate for this combined quantity to `joinedPhysical`. It
retains the high-owner, allocation, radial and native-projection budgets,
plus the new operator-change budget, exactly once. Its signed premise is
explicit and remains unproved.

This theorem does not establish a masked spectral expansion or discard a
selected resonance. It also does not pay the small-prime legs of the
balanced main. The known hard-mask, low-order, fixed-cutoff and modal
counterexamples remain valid outside this particular arithmetic payment.

## Optional numerical regression

Run `../.venv/bin/python scripts/probe_riesz_prime_head_pole.py`. The
diagnostic retains the same full complex head and every complementary
factorial order, including the boundary orders. All twelve frozen
complex-total regressions pass at toy orders 6, 7 and 8, heights 65 and
100, and both existing total-log windows. The unchanged main and changed
head satisfy the exact signed difference ledger to floating precision.

The filtered correction changes the real joint total in either
direction; it does not eliminate the adverse bias. These toy calculations
use `-2N log u`, not the native damped integer length or dyadic schedule,
and never apply the `N>=64` Lean budget at their small orders. They are
optional, outside builds/CI, and are not an interval certificate or a
cofinal floor bound.

## Remaining mathematical obligation

The main target is still an independent cofinal lower bound of
`-399/5000-o(1)` for the whole balanced sum minus the same signed
correction, now allowing the paid per-leg operator. The actual signed
central bias and the prime correction must be controlled jointly.
Neither the floor, the multiplicity ceiling, a restricted contradiction,
a new zero exclusion nor RH is proved by this slice.

Validation is focused and local: strict leaf, targeted build, frozen
compiled ordinary root plus explicit-leaf namespace lint and standard
axiom audit of every compiled declaration. No root registration, public
endpoint update, commit, push, subagent or wider gate was performed.
See `riesz-prime-head-pole-payment-audit.json` for the frozen evidence.
