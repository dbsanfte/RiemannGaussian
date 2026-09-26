# Exact head cancellation and a precision audit

The open arithmetic target is unchanged:

\[
u^{N+1}\bigl(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\bigr).
\]

**This slice does not prove its signed bound, a complementary floor, or a
zero exclusion.** It cancels the one-cofactor head exactly and checks which
parts of the high-order numerical diagnostic remain unresolved.

## Checked cancellation before numerical approximation

[`ZetaRieszJoinedHeadCancellation`](../RiemannGaussian/ZetaRieszJoinedHeadCancellation.lean)
proves, for the original finite `rectangleMass`,

\[
W_N(x,0)=W_N(x,1)=0\quad(N\ge101),\qquad
\int_0^1 c\,\partial_z W_N(x,z)\,dz=0
\]

for every complex `c`. This keeps an arbitrary full product phase. The
endpoints include both the empty least slot and the entire-cofactor slot.
The latter cannot satisfy the original owner and least-order conditions
simultaneously. No endpoint is estimated separately.

The same fact holds on actual integers: `markedWeight_two_primes` is zero
for every two-prime label, and `lower_eq_overflow_two_primes` identifies its
two actual boundary weights. `two_prime_extension_eq_zero` proves that
adding any squarefree two-prime support to the joined difference adds
exactly zero, with the actual carrier coefficient and phase retained.
The original support and the remaining count masks are unchanged.

This matters for the continuum diagnostic. The theorem
`coefficient_saturated_prime` requires a composite cofactor; it must not be
applied directly to a prime cofactor. The all-count exponential nevertheless
contains a one-cofactor term. Below its total cofactor share this head is
independent of the auxiliary least cutoff. Its cancellation uses both
factorial boundaries together, as above.

## Direct high-precision diagnostic

The optional [probe](../scripts/probe_riesz_joined_precision.py),
[helper](../scripts/riesz_joined_precision.cpp) and
[report](riesz-joined-precision-probe.json) compare the complete Euler
recurrence and **direct signed convolution** at 113 bits and 100 decimal
digits. Neither computation uses an FFT or lowers precision before the
convolution. These are still rounded computations, not interval enclosures.

The model modes are exactly the previous synthetic stress family:
`0`, `1/40000 +/- (3/500)i`, with multiplicities `1,3,3`.
They are not asserted to be zeta zeros. The owner share is `11/20`,
`T=(N+1)/u`, `u=10001/20000`. The probe uses the asymptotic moving length
`2*(-N*log(u)-log(N+1))`, not the integer-floor length.

At cutoff-grid size 2048, the fixed-point results are approximately:

| N | Least share | Direct 100-digit response | Relative discrepancy at 113 bits |
| --- | --- | --- | --- |
| 262144 | 0.01 | `-1.46382e-27` | `8.47e-4` |
| 262144 | 0.04 | `-6.82662` | `9.42e-31` |
| 1048576 | 0.01 | `6.85281e-20` | `3.14e-3` |
| 1048576 | 0.04 | `1.29189e9` | `3.45e-30` |

The tiny lower-face response loses visible relative precision in the
113-bit recurrence. The large upper-face value at a single point survives
the precision check. Neither observation decides the signed radial/share
integral. Grid refinement is a separate error, visible in the report.

Run outside ordinary CI:

```sh
python3 scripts/probe_riesz_joined_precision.py \
  --output docs/riesz-joined-precision-probe.json
```

The optional helper requires `g++`, `libquadmath` and Boost headers. Compiled
helpers are cached under `.lake/`, keyed by source, compiler and precision.

## Integrated diagnostic remains inconclusive

Further exploratory integrations retained the two finite factorial beta
faces, full synthetic phase, core radial window `1.95N..2.03N`, moving
length and all model counts. They did **not** enforce the literal arithmetic
count caps, prove model exterior errors, or transport anything to primes.

At `N=262144`, cutoff grid 4096, the joined value changed from approximately
`9.88e-5` with `(T,r,p)` quadrature orders `(160,24,1024)` to `1.0734e-4`
with `(256,32,2048)`. Earlier, coarser refinement gave `9.04e-5`.
These are numerical diagnostics, not confidence intervals or a bound.
The sampled integrand reaches roughly `3.9e6`; its cancellation matters.

At `N=1048576`, one insufficiently resolved run returned a joined value of
order `1e18` while sampled integrands reached `1e23`. **That result is not
accepted as evidence of growth.** Its oscillatory quadrature is unresolved,
and the FFT route converts recurrence outputs to long double before
convolution. The recurrence's internal precision is therefore not the
precision of the integrated result. Direct fixed-point precision checks do
not repair those separate errors.

The next mathematical requirement is still a signed estimate for the
coupled counts and both boundaries. A selected coefficient, large pointwise
model value, plausible exponent, or small sampled integral cannot substitute
for it. No result here reopens the older masked-transfer, independent-phase,
generic Abel/PNT, or diverging-allowance routes.

The subsequent [ball-arithmetic phase audit](zeta-riesz-joined-ball-audit.md)
identifies a concrete additional problem: the 12-node least-share rule at
million-order scale gives an error around `0.909` on a phase moment whose
independently enclosed norm is below `3e-43`. Refinement can also alias
non-monotonically. The coupled high-order run was therefore stopped as
unresolved; its outputs do not establish growth or decay. The new optional
diagnostics separate arithmetic rounding from that quadrature error and
leave the same signed prime-sum target open.
