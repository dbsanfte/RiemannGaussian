# Literal triple/quintuple cancellation: two paid errors, open signed floor

This test starts from `3f19e314768d66c47ab4628d5a32570e59293b6d` and
works in the **direct finite carrier**. The proved rectangle reserve and
its exact ledger are unchanged. No new completion or use of a
hypothetical-zero prime phase is involved.

**Current result:** the algebraic signs pass. The full carrier tail above
`log(n)=2.03N`, the quintuple packet's old allocation, and an explicit
thin-cell phase error are independently paid at source scale. The requested independent
signed bound of `-1/1000` or `-1/500` has **not** been proved. The existing
Rosser endpoint bounds cannot supply the required cell counts by endpoint
subtraction. In addition, an unsigned density surplus does not itself
bound the signed cell main term. These are intermediate gaps in the
continuing floor campaign; do not count these identities as an arithmetic
floor or a zero exclusion.
This is not a general impossibility result for parity cancellation.

## Quantitative gains prompted by the numerical probe

The optional probe replaces prime counting by the continuous density
`dx/log(x)`. It does **not** enumerate actual primes or certify a source
constant. Its moving-window scan found a quintuple/triple ratio near
`1.1162` at the central slope, falling to `0.9934` at `log(n)=2.05N`.
At `2.03N` the sampled ratio is still approximately `1.0414`.

This led to an independent theorem for the actual carrier:
[`exists_core_window_error`](../RiemannGaussian/ZetaRieszParityWindow.lean)
gives constants `r<1`, `C>=0` such that

\[
\left|u^{N+1}(\mathrm{narrowResponse}_N-\mathrm{coreResponse}_N)\right|
\le Cr^N,\qquad 0\le u\le10001/20000,
\]

where the core is the original support intersected with
`1.95N<log(n)<=2.03N`. It keeps all other original restrictions and works
uniformly in height and prime-count cutoff. The strict upper deviation
inequality is checked using rational Taylor bounds. The same estimate
holds for the literal paired packet. No original Type-II target is changed.

The small log-share box also places every quintuple prime at share at
most `113/200`. Thus every complementary share is at least `87/200`,
strictly above the old allocated-order endpoint `13/32`.
[`quintuple_boundedShare_le`](../RiemannGaussian/ZetaRieszParityAllocation.lean)
proves the exact pointwise estimate

\[
\mathrm{boundedShare}_N(n)\le5e^{-N/2200}.
\]

`quintuple_allocation_bound` and `tendsto_quintuple_allocation` pay the
actual summed allocation error, with all support restrictions unchanged:

\[
\left|u^{N+1}\mathrm{quintupleAllocation}_N\right|
\le 5U r_A^N\,\mathrm{MajorantMass}(1+1/262144),\quad
r_A=\frac{U}{131071/262144}e^{-1/2200}<1.
\]

Here `U=10001/20000`. This bound is uniform even in moving heights and
uses no zero or prime-count premise. It controls the discarded old
allocation; it does **not** control the surviving unassigned packet.

## Reproducible exploration and its limits

Run the optional scripts in an environment with NumPy and SciPy:

```bash
python -m pip install -r scripts/requirements-riesz-probes.txt
python scripts/probe_riesz_parity_packet.py --power 20 --seeds 4 --output /tmp/packet.json
python scripts/probe_riesz_parity_cascade.py --power 20 --seeds 3 --max-primes 9 --output /tmp/cascade.json
```

[Recorded probe results](data/riesz-parity-probes.json) distinguish the
selected five-prime packet, its full ordered log-share box, and the
additional prime-count classes. The scripts are absent from normal
builds and CI. They independently check selected hinge formulas against
all 32 divisor subsets, and cross-check the triple integral using
Gauss-Legendre quadrature. Seed spread measures empirical stability;
it is not a certified integration error.

The finite-order model also retains the moving cutoff, the original
factorial rectangle, the old binomial allocation and `r>N^2`. It reports
the error in its stable expression for the literal length. It does not
replace those conditions by their limiting values without reporting it.
The limiting cascade diagnostic, in contrast, examines full ordered
log-share boxes without a finite-order rectangle or physical cutoff.
Both recorded probes use the upper radius `u=10001/20000`; they do not
certify uniform density inequalities throughout the radius interval.

Three findings matter for the next arithmetic estimate:

1. A replacement fixing both `p` and `r` fails pointwise in some corner
   boxes: the sampled local ratio falls to about `0.907`. Transport
   within a common **total-log** cell can mix those outer shares; a
   proof must not assume pointwise dominance at fixed `p,r`.
2. Capped matching leaves quintuple excess. Near the central slope the
   model excess is about `0.000566`, with real contribution equal to
   **minus** that excess times the common cosine. Its sign reverses
   when the cosine changes sign. These angular density numbers are
   not source-normalized error allowances.
3. In the same continuous-density model, the full odd-class boxes give
   approximately `+0.0048723` (three primes), `-0.0054226` (five),
   `+0.0003685` (seven), and `+0.0002127` (nine). This suggests further
   cross-class cancellation, but four-, six- and eight-prime terms are
   also substantial. Omitted classes and actual counting errors are
   not bounded by the experiment. No novelty or arithmetic floor is
   inferred from this classical-density model.

The next unresolved quantity is still the signed weighted cell sum below,
including its excess and the rest of the direct-carrier ledger. Extending
the formal decomposition without estimating it would not close this gap.

## What is literally selected

[`ZetaRieszParityPacket`](../RiemannGaussian/ZetaRieszParityPacket.lean)
defines one suballocation of the actual `narrowResponse`:

* The triple selection retains the existing `rectangleMass`,
  `rectangleIncidences`, physical primes, unique second incidence and
  original `tripleBand`. It also imposes the requested smaller **log-share**
  box `21/40 <= log(p)/log(n) <= 113/200` and
  `1/100 <= log(r)/log(n) <= 3/100`. The log-share box does not replace
  the old factorial-order rectangle.
* The quintuple packet filters the original `narrowBand` to five distinct
  ordered primes `p>a>b>c>r`, the same smaller log-share box, and the
  three hinge regions below. Every prime lies in the original
  `intermediatePrimes`; squarefreeness, the original prime-count cutoff,
  narrow window, nondominant and physical masks remain. Each integer is
  selected once, not once per marked pair.
* Both terms retain `1-boundedShare`, the original factorial kernel and
  `exp(-i*y*log(n))`. `packet_direct_ledger` retains the unselected part
  explicitly. No assertion is made that this remaining carrier is small.

`quintupleBand_subset_nontriple` proves that the quintuple packet belongs
to the original nontriple part `H`. `packetSelection_bounds` proves the
entire selection lies between zero and one.

## Exact hinge calculation

Write capital letters for **unnormalized** actual prime logarithms,
`P=log(p)`, `A=log(a)`, `B=log(b)`, `C=log(c)`, `R=log(r)`, and
`d=L_N-P`. The literal normalized cutoff is `L_N/log(n)`.
Replacing it everywhere by `-2*u*log(u)` would require a comparison which
has not been silently made here.

On the retained support the cofactor is saturated at `L_N` and `d<=A`.
Exact prime insertion and all eight remaining subsets give

\[
\mathcal R_{L_N}(pabcr)=-H(B,C,R;d),
\]

where

\[
\begin{aligned}
H(B,C,R;d)={}&d_+-(d-B)_+-(d-C)_+-(d-R)_+\\
 &+(d-B-C)_++(d-B-R)_++(d-C-R)_+-(d-B-C-R)_+.
\end{aligned}
\]

[`ZetaRieszQuintupleHinge`](../RiemannGaussian/ZetaRieszQuintupleHinge.lean)
proves the three evaluations:

| Region, with `B>C>R>0`, `d>B`, `d>C+R` | Reduced response |
|---|---|
| `d <= B+R` | `B-d` |
| `B+R <= d <= B+C` | `-R` |
| `B+C <= d <= B+C+R` | `d-B-C-R` |

The third expression is also `A-(log(n)-L_N)`. It is **zero**, not
strictly negative, at the closed upper endpoint. The formulas agree at
their shared boundaries. Saturation and `d<=A` are explicit predicates
of the selected literal packet, not assumptions about discarded errors.

The original coefficient is therefore

\[
c_{L_N}(n)=\frac{\log n}{L_N}H(B,C,R;d)\le0.
\]

The selected triple has `-R_L(pqr)=log(r)`, hence positive arithmetic
coefficient. The two classes really do have opposite arithmetic signs.
This statement is independent of any hypothetical zeta zero.

## The exact phase-preserving comparison

Let `T_N(n)>=0` and `Q_N(n)>=0` denote the two literal densities, including
their factorial, selection and allocation weights. The direct pair has
the arithmetic orientation

\[
\sum_n (T_N(n)-Q_N(n))e^{-iy\log n}.
\]

Its orientation should not be confused with the predicted negative
triple and positive quintuple **zero-source** constants.

For any `Delta>0`, define deterministic cells by
`k=floor(log(n)/(2*Delta))` and `t_k=(2*k+1)*Delta`.
[`ZetaRieszParityCells`](../RiemannGaussian/ZetaRieszParityCells.lean)
proves the exact grouping, the distance bound `|log(n)-t_k|<=Delta`, and

\[
\begin{aligned}
\mathrm{Frozen}_N&=\sum_k(T_{N,k}-Q_{N,k})e^{-iyt_k},\\
\operatorname{Re}\mathrm{Frozen}_N
 &=\sum_k(T_{N,k}-Q_{N,k})\cos(yt_k).
\end{aligned}
\]

Only the phase error is bounded in norm. Its allowance is
`|y|*Delta*sum_n |T_N(n)-Q_N(n)|`, with the actual signed cell main term
left untouched. The original summable divisor majorant and selection
bound pay this error for the concrete choice

\[
\Delta_N=e^{-N/4000},\qquad
r=\frac{10001/20000}{131071/262144}e^{-1/4000}<1.
\]

`packet_phase_error_at_source` gives, for `0<=u<=10001/20000`,

\[
\left|u^{N+1}(\mathrm{Packet}_N-\mathrm{Frozen}_N)\right|
\le\frac{10001}{20000}|y|\,r^N\,
\mathrm{MajorantMass}(1+1/262144).
\]

Thus `tendsto_packet_sub_frozen` is an unconditional source-scale error
estimate, for every fixed height and any prime-count cutoff schedule.
It is not a bound for `Frozen_N` or the packet itself.

## Exact limits of the currently proved counting input

[`ZetaRieszParityCountAudit`](../RiemannGaussian/ZetaRieszParityCountAudit.lean)
proves, for `t>=2` and `0<=w<=1/(16*t)`,

\[
\mathrm{lower}(e^{t+w})<\mathrm{upper}(e^t),
\]

using precisely the repo's Rosser comparison functions. For `t>=5100`,
the actual proved prime-count bounds therefore imply only

\[
\underbrace{\mathrm{lower}(e^{t+w})-\mathrm{upper}(e^t)}_{<0}
<\pi(e^{t+w})-\pi(e^t).
\]

`eventually_packet_cells_below_count_resolution` shows that the concrete
width `2*Delta_N` lies in this regime uniformly for all
`5100<=t<=41*N/20`. Endpoint subtraction cannot certify a positive count
at that resolution, before any of the extra weights or masks are handled.
This does **not** say the intervals lack primes.

Conversely, a polynomial width such as `N^(-1/2)` does not pay the
available source-normalized total-variation envelope:
`polynomial_width_envelope_diverges` proves its exponential-versus-power
rate failure. This theorem concerns that **error allowance**, not a
lower bound on the actual phase error or actual packet magnitude.
It does not rule out cancellation inside the transport error.

There is a separate signed issue even with exact cell counts. A larger
`Q_{N,k}` helps where the common cosine is negative and hurts where it is
positive. `common_phase_surplus_is_negative` checks the latter at phase
zero. The numerical source surplus is not an independent phase theorem.
A capped matching may remove equal masses, but its unmatched quintuple
excess must stay in the original carrier and be estimated; it is not free.

## What literature could change this verdict

The required cell width is within the range of known unconditional
short-interval prime asymptotics. On the smallest requested share,
`log(r)>=39*N/2000`, Lean proves
`exp(-log(r)/78)<=Delta_N`. Thus, at a prime scale `X`, the natural
interval length `X*Delta_N` is at least `X^(77/78)`; constant subdivisions
of a cell do not alter that exponent.

As an external benchmark, Guth and Maynard's
[New large value estimates for Dirichlet polynomials](https://arxiv.org/abs/2405.20552v2)
deduces unconditional prime asymptotics in intervals of length
`X^(17/30+o(1))`, substantially shorter than this requirement. This
theorem has **not** been formalized or imported here. The inference is
that the raw counting resolution is a formalization gap, not known
RH-strength difficulty. A uniform weighted five-prime comparison with
the present moving hinge, allocation and factorial masks is still an
additional obligation. A short-interval count by itself does not prove
the displayed signed cosine sum has an eventual numerical floor.

The continuing test must not assume either of those obligations.
There is no new restricted contradiction, quantitative saving for the
joint arithmetic main term, or change to `LocalizedTypeIIBound`, the
public zero-free frontier or the main RH endpoint.

## Local proof validation

The ordinary warning-as-error build and whole-project declaration lint
pass. The explicit root-import audit checks all six displayed terminal
theorems and reports only `propext`, `Classical.choice` and `Quot.sound`.
The generated project-status audit finds no project-defined axioms or
placeholder-dependent project declarations. The supporting explorer
links to the compiled theorem statements and their exact source lines.
The numerical probes remain separate from this Lean proof audit.
