# Gaussian square payment and the remaining signed source

2026-10-19. This continues the
[native square checkpoint](arithmetic-operator-square-native-odd-core-gates.md).
The new Lean result carries the actual square-sector bound through the
Gaussian integral and the central dyadic sum. The odd-core estimate remains
open. The source and marked-recovery audits below are deliberately separate
from that checked payment.

## Checked Gaussian payment

[`QuasiRHSquareGaussianPayment`](../scripts/QuasiRHSquareGaussianPayment.lean)
proves `central_square_gaussian_payment` for the original central windows:

```text
sum_j norm(original central square Gaussian dyad_j)
  <= C * Z^(5/72 + 255*epsilon + 2*epsilon_G).
```

Both the complex series and its norm series are summable. Every original
selected prime mark, cube, calibration factor, phase and physical mask
remains. No energy or integrability assumption replaces the arithmetic
bound. The inner Mellin multiplier `sqrt(Q)^(-1)/(2*pi)` occurs exactly once.

The outer integral is justified by first identifying the numerator
restriction with a finite sum of the original physical rows. The existing
selected-row Gaussian theorem then proves integrability of each term.
`gaussianSectorDyad_ledger` gives an exact split of `lowCommonDyad` into the
square and complementary sectors, with both integrability proofs in place.

The leading exponent is still `5/72`, a saving of `17/144` compared with
the old `3/16` cost on this population. Gaussian summation adds at most
`7*epsilon_G/6`, safely rounded to `2*epsilon_G`.

The **whole source/ray normalizer** is distinct from the Mellin multiplier.
Its existing inverse bound adds an arbitrarily small `nu_N`, under its
actual ray-pool, positivity and profile hypotheses. Joining those data and
the finite compensation-subset sum is recorded as a paper application;
this leaf does not claim a newly compiled whole-probe endpoint. The intended
unchanged ledger, with `P_raw` the original unnormalized probe, is

```text
P_raw / normer - F_all
  = centralSquare / normer
    + (centralOdd / normer - F_all)
    + remoteAll / normer.
```

The existing remote bound is used on **all** remote rows. It does not
provide a square-filtered remote estimate. No zero source is assigned to
the square subset.

## Principal source: an automatic cancellation is unavailable

The exact native `rowBand` used by `F_all` excludes the principal free row
`u=1`. The source chain gives

```text
P_raw / normer - F_all = U1 / normer + transport error,
U1 / normer = Signal + principal error.
```

The complete `U1` includes both contour exteriors and the reciprocal-
L-function source. It is not `F_all`. Subtracting it as a paid error would
remove the source that the argument must retain.

The imported `canonical_probe_exists_cube` requires `betaSup >= 7/8`.
The previously audited wider replay remains a paper result; the exact
partition alone does not extend that theorem's domain. See the
[pinned source audit](../.lake/arithmetic-operator-odd-core-exceptional-join/preflight.md).

## Marked inverse estimates: a real interface, but no new global saving

The native `padded_source_energy` already accepts coherent prime-divisor
slots. For one reflected inverse slot, its capacities translate to

```text
Y_inv * L < T,       Y_inv^2 * L^6 < T^3.
```

The large-frequency head satisfies these constraints. However, retaining
the low frequencies and the original recovery multiplier returns the
conditional upper-method cost

```text
K + D_g + K*L^2 + K*D_g^(-1/3)*L^3.
```

On the native head it reduces to `K+D_g`, while
`D_g/K = Z^(17/48-d+2*ell) >= Z^(3/16+2*ell)`.
Thus this application does not recover the needed row-scale `K` estimate.
This is a cost of the method, not a lower bound for the actual signed sum.
Profile, puncture and full-source transfer are still explicit obligations.
The [marked audit](../.lake/arithmetic-operator-odd-core-marked-inverse/preflight.md)
also explains why differentiating inside the fixed-period bounded-character
class cannot generate these marks for free.

## Literature applicability

The [harmonic Möbius recovery note](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates/blob/8c995528481f144debf70ffd25678a3fdf379fd4/methods/harmonic_mobius_ratio_recovery.md)
controls an internal reflected ratio, not our physical odd core. Growing
Euler punctures admit an exact recovery with subpower coefficient mass;
they are not, by themselves, an impossibility. But preserving the original
ratio partition, selected/cube coefficients and the large balanced-ratio
complement requires further work. No actual odd-core payment follows here.
The author's analytic result is not imported into Lean. The
[scope audit](../.lake/arithmetic-operator-harmonic-recovery-audit/preflight.md)
pins the source and retains the unpaid components.

Likewise the author's [hybrid character estimate](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates/blob/main/methods/hybrid_character_moment.md)
controls dense squarefree columns; it does not supply the complete marked
mixed moment needed by the native consumer.

## Remaining target and validation

The remaining arithmetic target is the original signed
`centralOdd/normer - F_all` covariance, with its prescribed companion.
Neither eliminating the principal source nor using the above recovery
cost proves it small. A useful next estimate must improve that actual
marked covariance rather than a freely chosen coefficient vector.

The new leaf passed warnings-as-errors, all 15 linters and an all-local
standard-axiom audit: 10 explicit theorems, 3 definitions, 29 declarations
including helpers. Independent review checked the integrals, exact
normalizers and summation. The three paper audits have 32,986 exact finite
checks; these do not certify their analytic applicability claims.
All 1,547 prior/new manifest entries matched before the shared-note append.
Evidence is in the companion JSON. No broad build, public registration,
commit, push, new zero-free region or RH claim is part of this slice.
