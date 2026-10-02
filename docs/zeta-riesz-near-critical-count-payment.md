# A further global count-tail payment

The original `-79/1000` floor remains **open**. The additional payment
retains every original physical, radial, share, allocation and phase mask
and applies uniformly in height. It pays an actual original population;
it does not estimate the remaining signed energy or floor deficit.

Proof: [ZetaRieszNearCriticalCountPayment.lean](../RiemannGaussian/ZetaRieszNearCriticalCountPayment.lean).
Validation: [focused proof audit](riesz-near-critical-count-payment-audit.json).

## The unchanged native schedule has more count-tilt margin

Write `K=dyadicPrimeCount j=2^(j+3)` and
`N=dyadicMomentOrder j=8*(j+4)*K`. For `j>=1024`, Lean proves

\[
K\log K\ge\frac{173}{2000}N.
\]

Consequently every squarefree label with `864*omega(n)>=K` satisfies

\[
K^{\omega(n)}\ge
\exp\left(\frac{173}{1728000}N\right).
\]

The finite Euler count moment is summed over the entire selected support
before any price is taken. No countwise positive credits, supplier, cofactor
completion or prime-density comparison enters.

## A certified negative source exponent

Choose exactly

\[
q=\frac{499999999}{1000000000},\qquad
\sigma=\frac{1000000001}{1000000000}
=\frac32-q,\qquad U=\frac{10001}{20000}.
\]

The fixed convergent count mass at `sigma` gives the eventual Euler slack
`exp(N/100000000)`. Its value and the corresponding eventual starting
order are **not evaluated**. The schedule bound `j>=1024` alone is not
an effective starting order for the final tail estimate.

`count_rate_bound` verifies with exact rational arithmetic and
`log x<=x-1` that

\[
\frac Uq\exp\left(-\frac{173}{1728000}
                      +\frac1{100000000}\right)
\le\exp\left(-\frac1{10000000}\right)<1.
\]

Thus `eventually_nearCritical_count_sum_bound` bounds the source-normalized
whole selected sum, for any original correlated coefficients dominated by
the existing factor-two majorant, by

\[
\frac{203}{50}U(N+1)\exp(-N/10000000).
\]

No hypothetical zero or arithmetic cancellation hypothesis is used.

## Exact placement in the original floor

Define the natural-integer endpoint

\[
K_{\mathrm{new}}=\lfloor K/864\rfloor+1.
\]

The original `coreResponse` at `K` differs from the original `coreResponse`
at this endpoint by precisely the paid label sum. Nonsquarefree labels
vanish exactly. The complex difference tends to zero at source scale,
uniformly for varying heights and radii in `0<=u<=U`.

`eventually_joined_floor` bounds the **original** `joinedPhysical` at the
**original** count ceiling `K`, using the complete signed `nonOrbitEnergy`
of this smaller core. It retains one original core/joined bridge and each
of the existing four geometric pair prices once, then adds the new count
allowance once. It does not spend an auxiliary supply debit or a favorable
count credit.

Relative to the preceding `floor(K/768)+1` endpoint, the new count interval
is asymptotically **8/9 as wide**. Lean proves both endpoint ordering and
an exact bounded rounding comparison. This is about an **11.1% reduction
in the remaining count interval**, not 11.1% of carrier mass, signed cost
or distance to the floor.

The new exponential rate is **50 times slower** than the preceding
`exp(-N/200000)` rate. It pays a larger population in exchange. Both are
cofinal statements; neither certifies a practical finite starting order.

The original adverse cutoff set is selected once on the entire new core.
It differs from the previous core's adverse set. Signed cross terms can
change either way, so **do not infer that the smaller core has a smaller
energy**. The theorem pays the actual complex carrier difference instead.
The antiphase/aligned-negative credit identities remain available for any
such finite support; no native reserve lower bound is obtained here.

The independent remaining sufficient budget
`nonOrbitEnergy<=3/(320*(N+1))`, the numerical floor, multiplicity ceiling
and restricted zero exclusion are still unproved.

Fourteen public proofs pass focused Lean, root-import, namespace-lint and
standard-axiom checks. Earlier proofs and staged semiprime files remain
unchanged. The published README and explorer endpoints stay frozen.
Work remains local, without commits, pushes, subagents or wider gates.
