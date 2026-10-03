# Paid signed incidences in the native whole-floor price

This local slice puts the independently paid cubic crossing rows into the
**current whole-floor inequality**. It removes their signed cutoff increments
before pricing the joined remainder over complete periods. It does not
prove the numerical price needed to close the floor.

The checked module is
[ZetaRieszPaidIncidenceFloor](../RiemannGaussian/ZetaRieszPaidIncidenceFloor.lean).
The range remains `1/2 < u <= 10001/20000`, with fixed `|y| >= 54`.
There is no zero or bilinear-cancellation hypothesis in the arithmetic
payment or whole-carrier comparison. The final contradiction endpoint has
an explicit, still-open cofinal numerical premise.

## Exact original-incidence ledger

The already-paid row uses `n=p*(B*e)`, with canonical largest prime `p`,
the original rough sieve, squarefree/core/count predicates and moving
length. A selected divisor `delta | B` maps to the original incidence

$$
(n,(d,b))=\bigl(pBe,(e\delta,B/\delta)\bigr).
$$

`rowIndices_incidence_injective` checks that this map counts each selected
incidence once. `literalCutoffPacket_eq_divisors` joins them by their
original product label, retaining every Möbius sign and the full complex
factorial-kernel phase. No complete cofactor or additional label is inserted.

For positive `p,b` with `p*b <= X`, `pairHinge_eq_profile_diff` proves

$$
\operatorname{pairHinge}(L,p,b)=f_X(pb)-f_X(b),
$$

where `f_X = correctedProfile X L 1 0` is the actual cutoff profile.
Consequently each paid incidence has an exact two-endpoint prefix on the
same cutoff axis as the whole carrier. `sum_hingeIncrement` telescopes
this prefix back to its original hinge.

The allocation weights remain distinct. The current whole-carrier weight
uses `boundedShare A N n` with **all** intermediate primes; the paid row
uses `boundedShare (A.filter (fun p => p=largestPrime n)) N n`.
The proof retains both. This is an exact signed correction to the whole
increment, not a claim that identical whole-allocation atoms have been
deleted or that deletion always reduces the price.

## The native count crop is paid independently

The original cubic payment uses the original dyadic count cutoff. The
current native floor uses `countCeiling j = dyadicPrimeCount j / 864 + 1`.
`nativePaidPacket` restricts the actual paid incidence sum to that crop.

The crop cannot be justified by inferring decay of a subsum from decay
of the full packet. Instead, `partialCoefficient_majorant` bounds the
selected divisor coefficient by twice the original
`zetaMoebiusLogMajorant`. It reuses the existing partial-hinge majorant
from `ZetaRieszUnsignedDivisorError`. The current independent high-count
allowance then pays exactly the difference:

$$
\left|u^{N_j+1}
 (\operatorname{literalCutoffPacket}_j-\operatorname{nativePaidPacket}_j)
\right|\le \operatorname{allowance}_j
\quad\text{eventually}.
$$

Thus `eventually_nativePaidPacket_bound` gives the real signed payment

$$
\left|u^{N_j+1}\operatorname{nativePaidPacket}_j\right|
\le E_j,
\qquad E_j\longrightarrow0,
$$

where `nativePaidBudget` is the existing cubic-row, rounded-endpoint and
high-count budgets. `tendsto_nativePaidPacket` proves this real packet
tends to zero at source scale. It does not assert complex norm decay or
small absolute cutoff variation.

## The whole-floor inequality

Let `t_j(k)` be the current native cutoff increment, including its bounded
imaginary tilt and the previous joined null/tangent corrections. Let
`v_j(k)` be `nativePaidIncrement`. The exact identity
`sum_nativePaidIncrement` identifies its total with the scaled native
paid packet. Define

$$
D_j=\operatorname{blockCost}
 \bigl(t_j-v_j\bigr),
$$

using the **same complete cutoff-period groups**, count crop, labels and
physical masks. The general finite inequality `pruned_block_floor` pays
only the signed total of `v_j`:

$$
\operatorname{Re}\bigl(u^{N_j+1}
 \operatorname{joinedPhysical}_j\bigr)
\ge -D_j-E_j-\operatorname{nativeError}_j
\quad\text{eventually}.
$$

This is `eventually_joined_floor_pruned`. No norms of the retained main
increment are introduced before the complete-period sum.
`nativePaidIncrement_zero_early` also proves the new correction is exactly
zero when `log(k+1) <= L`; it adds no new early-cutoff debit.

Subtraction can increase the period price. The final `nativePrunedPrice`
therefore keeps the earlier credited price as an alternative:

$$
\mathcal D_j=\min\left(
 \operatorname{nativeCost}_j-\operatorname{nativeTangentCredit}_j,
 D_j+E_j\right).
$$

`eventually_joined_floor_with_pruned_price` proves the whole floor
`Re(scaled joinedPhysical) >= -mathcal D_j-nativeError_j`.
`nativePrunedPrice_le_previous` and `nativePrunedGain_nonneg` show this
valid price cannot be worse than the previous one. The two alternatives
are not independent credits that may be added twice.

`false_of_cofinal_pruned_price` connects the new price directly to the
simple exposed-zero contradiction **if**

$$
\mathcal D_j\le\frac{399}{5000}
\quad\text{cofinally}.
$$

That numerical statement is open. Under the existing exposed-zero
hypotheses the reused `nativeError` tends to zero; the arithmetic comparison
itself does not assume a zero. No unconditional floor or zero exclusion
has been proved here.

## Numerical regression and next obstruction

The manual [probe](../scripts/probe_riesz_paid_incidence_floor.py) uses the
previous five- and seven-prime original-core examples at `N=640,1536`,
with heights `54,65,100`. It enumerates all 160 original divisor incidences
and the two selected paid incidences, retaining the distinct whole and
owner allocations. It checks both Abel ledgers, the charged finite floor
inequality and the zero early increment. Floating residuals are below
`4e-12` after a common amplitude rescaling.

The regression gives an important negative diagnostic: some raw pruned
prices decrease, but **all six finite gains are zero after charging the
actual signed payment**. For example, at `N=640,y=54` the raw price falls
from about `31.71` to `12.59`, while the rescaled signed payment has
magnitude about `184.26`. The funded minimum retains `31.71`.
The eventual geometric budget has not been certified at these small orders.

Moreover, the native count ceiling is one at both tested orders and admits
neither label. These are original-incidence regressions, not native-price,
density, coverage or cofinal cost estimates. Probable-prime tests, floating
logarithms/phases and interpolated large period edges are diagnostics only.
Source amplitudes are recorded in logarithms rather than interpreting
underflow as cancellation. The probe stays outside ordinary builds and CI.

The next arithmetic obligation is to bound the **joined pruned cost** on
the actual native population, or establish a favorable signed correction
that meets the same numerical threshold. Rougher canonical crossings
and other unselected geometries remain. There is no quantified fraction
of the global deficit paid by this slice.

Validation is focused: warning-as-error Lean compilation/build, ordinary
compiled-root import plus the new module, namespace lint and transitive
axiom checks. No commit, push, full-root rebuild, wider CI, README or public
endpoint change is part of this iteration.
