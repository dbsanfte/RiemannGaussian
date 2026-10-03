# Pay the counting error on joined rough owner rows

[ZetaRieszRoughOwnerComparison](../RiemannGaussian/ZetaRieszRoughOwnerComparison.lean)
proves a source-small **comparison error** for complete rough owner rows.
It retains the signed density main and ordinary-prime cofactor subtraction
together. It does not prove the native numerical floor or remove that main.

This uses the existing smooth-owner, rough squarefree counting and weighted
sieve theorems. The underlying counting estimate is not claimed new. The
additional result applies it jointly to the exact owner atoms with physical
prime exclusions through `N^3`, and retains the actual native count boundary.
It makes no new completion of an ordinary-prime or composite prime leg.

## Keep the arithmetic masks in the measure

For a forbidden prime set `S`, the exact measure is

$$
\mathbf1_{a\ \mathrm{squarefree}}\,
\mathbf1_{\forall q\in S,\ q\nmid a}.
$$

The smooth test weight is the existing `ownerAmplitude` times the full
product phase `cos(y*(log p+log a))` and reciprocal cofactor weight. Its
finite binomial owner selector keeps every factorial order. Squarefree,
coprimality and roughness holes are not charged again as adjacent weight
variation. This does not authorize smoothing arbitrary remaining masks.

Take a complete integer row `M<a<=X<p`, with owner `p` in the eligible
prime set, `log p<=L`, and put `b=L-log p`. On squarefree composite
cofactors, `literal_rough_owner_shell_eq` identifies the sum with the
**existing** owner `residualCoefficient` and `zetaPrimeLogKernel`. No
cofactor count is separated, no phase is frozen, and no factorial
rectangle or lower-order deletion is introduced.

Write `w_p(a)` for that smooth shell weight. The signed comparison is

$$
\mathcal M_p=
\frac{
  \left[\sum_{D=1}^{R_p}
    \bigl((b-\log D)_+-(b-\log(D+1))_+\bigr)
    \operatorname{roughDensityPrefix}(S,D)\right]\sum_a w_p(a)
  -b\sum_{q\ \mathrm{prime}}w_p(q)\,\operatorname{sieve}(S,q)
}{Lp}.
$$

The prime-cofactor head has its literal subtraction sign. It is not
an error and is not paid by an absolute norm. The unit correction is
retained in the generic theorem; it is exactly zero on `M>=1` shells.

## The quantitative payment

The declared row conditions are explicit:

- `N>=32`, `0<M<X<=2M` and `X<p`;
- `R_p<=M`, `R_p^4<=M^3` and `b<=log(R_p+1)`;
- `exp(N/2)<=M`;
- `0<=u<=10001/20000`.

Only the translated cutoff is compared; cofactor saturation follows from
`a<p` and `log p<=L`. The other owner geometries are not asserted covered.

The strict source-rate certificate is

$$
(2u)^N e^{-N/128}\le e^{-7N/1000}.
$$

All forbidden primes through `N^3` are paid with the existing weighted
intersection product, bounded by
`exp((64/9)*N^(27/32))`. Eventually this consumes at most `exp(N/1000)`.
After joining all owner rows, their outer cost is harmonic, not their
cardinality. With physical owner endpoint `log Q<=203N/100`,
`eventually_joint_rough_owner_error` proves

$$
\left|u^{N+1}\left(\sum_p B_p-\sum_p\mathcal M_p\right)\right|
\le
2uC(6+|y|)(N+1)(1+203N/100)e^{-3N/500}.
$$

Here `B_p` is the literal rough composite-cofactor owner row, and `C` is
the existing counting constant. The start of the eventual estimate is
existential. `comparison_budget_tendsto` proves this entire global error
tends to zero. This is not a polynomial improvement to a positive main
envelope: the factor `e^{-3N/500}` beats the source growth. Both signs of
the **difference** are controlled, so it gives a one-sided comparison
floor while leaving `sum_p M_p` signed.

## Retain the native count crop

`owned_rows_injective` proves that original incidences `(p,a)` with
squarefree `a<p` map injectively to `pa`: `p` is its unique largest prime.
Thus the comparison cannot spend a single physical label more than once.

`eventually_owned_count_boundary` applies the already checked independent
native count payment to these actual incidences. It keeps every supplied
mask in their finite set and pays their `omega>=countCeiling(j)` boundary
by the existing `allowance(j)`. It does not assume that a complete row
automatically satisfies the original prime-count crop. Nor does it
provide a second count credit to add to an already cropped ledger.

## What remains for the floor

The remaining quantity is the **joint signed** `sum_p M_p`, including
the density scalar and prime-cofactor subtraction. This slice does not
bound its arithmetic size by `399/5000`. It also does not establish that
all remaining core masks admit complete rows of this geometry. In
particular, the owner-smaller-than-cofactor population remains outside
this row theorem. Original radial, count and other support masks must
be aligned literally before the bound is used in a whole-core ledger.

The earlier median/null floors remain alternatives. This comparison
error is not an extra null-credit rebate, and the signed prime head may
not be deleted or counted as free completion cancellation.

## Optional finite diagnostic and verification

[probe_riesz_rough_owner_comparison.py](../scripts/probe_riesz_rough_owner_comparison.py)
exhausts twelve **toy** integer-cofactor cases with the actual finite
owner selector and correlated factorial/phase weight. It independently
checks the joined divisor expansion. The zero-extended masked weight's
variation is about 16–52 times the smooth variation in these examples.
The prime head changes sign with height and can exceed the corrected
comparison error; deleting it would not be a legitimate saving.

These toys do **not** meet the large-cofactor hypothesis or original core
window, and are not native cofinal points. No geometric theorem is applied
to them. Density, logarithms, phases and binomial probabilities are
floating, not interval-certified. No native saving percentage, population
coverage, cofinal floor or zero exclusion follows from these numbers.

The [local audit](riesz-rough-owner-comparison-audit.json) records the
focused strict Lean/build, compiled ordinary root plus explicit module,
namespace lint and transitive standard axioms. Wider gates, root-source
rebuild, README/explorer changes, commit and push remain postponed.
