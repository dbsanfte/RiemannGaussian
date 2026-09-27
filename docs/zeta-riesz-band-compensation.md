# Paying a growing balanced triple band

[`ZetaRieszBandCompensation`](../RiemannGaussian/ZetaRieszBandCompensation.lean)
proves an independent signed comparison for actual prime products, with
the original coefficient, allocation, phase and core masks. For every
fixed nonzero height, **some fixed positive share width** is payable by
at most half of a disjoint positive four-prime supply. No hypothetical
zero or signed prime-density transport is assumed.

This extends the [earlier fixed-width triple box](zeta-riesz-quadruple-compensation.md).
It does not pay the whole balanced-triple class, the whole radial core,
or the [cofinal joint floor](zeta-riesz-joint-floor.md).

## The entire selected triple band

For the original finite core set `S`, `tripleBand S N η` contains **every**
squarefree three-prime label in `S` satisfying

\[
2N\le\log n\le2N+1,\qquad
\left|\log p-\frac{2N}{3}\right|\le\eta N
\quad\text{for every }p\mid n.
\]

The prime-log widths grow linearly with `N`; the total-log interval still
has width one. Both restrictions matter. The chosen `η` may depend on
the fixed height, but not on `N`. The theorem does not assert that the
entire permitted range `η<=1/1000` is payable.

`fixed_box_subset_tripleBand` contains the original saddle triple boxes
once `η*N>=1/4`. `eventually_core_tripleBand_nonempty` proves that the
actual core selection is eventually nonempty for **every** fixed `η>0`.
The region is not a continuum-only or empty selection.

## Supply and quantitative comparison

The four-prime supply uses three free translation indices
`0<=i,j,k<floor(N/(125*h))`. Its ordered prime-log intervals, all of width
`h`, start at

\[
\frac{11N}{25}+ih,\quad
\frac{12N}{25}+jh,\quad
\frac{13N}{25}+kh,\quad
\frac{14N}{25}-(i+j+k)h+v.
\]

Thus all products satisfy `2N+v<log n<=2N+v+4h`. Unique factorization
proves that distinct grid cells give disjoint integer labels. For fixed
`y!=0`, a bounded translation `0<=v<=C` places this whole supply in a
negative-cosine interval. On the eventual actual length range
`137N/100<=L<=7N/5`, each coefficient is at most `-N/20` and at least half
the original unassigned allocation survives. These atoms have positive
real contribution. `eventually_supply_in_core` proves every supply label
belongs to the unchanged core.

Write `f_N` for the original complex residual atom and put

\[
Q_N=e^{-3N}(2N)^N/N!,\quad
X_N=\sum_{n\in\mathrm{tripleBand}}f_N(n),\quad
Y_N=\sum_{n\in\mathrm{supply}}f_N(n).
\]

Actual fixed-width prime-count lower bounds and the three disjoint grid
coordinates give

\[
\#\mathrm{supply}\ge c_0\frac{e^{2N}}{N+1},\qquad
\Re Y_N\ge c\frac{N e^{2N}}{N+1}Q_N>0.
\]

The whole triple band has a finite cover by two log-translation
coordinates, with the third interval retaining their sum constraint.
Chebyshev's prime-count upper bound and the original factorial kernel give

\[
\|X_N\|\le B\eta^2\frac{N e^{2N}}{N+1}Q_N,
\qquad B=27(6\log4)^3e^{11/2}.
\]

Both sides have the same rate. Choosing
`η=min(1/1000,sqrt(c/(2B)))`, `eventually_band_spending` proves the
**actual weighted inequality**

\[
\boxed{\quad\|X_N\|\le\tfrac12\Re Y_N.\quad}
\]

The prime number theorem supplies only unsigned interval populations;
it is not used to approximate or transport a signed sum. The phase sign
is known throughout each supply interval. The starting order is not
evaluated, and neither side is claimed to tend to zero at source scale.

## Exact credit retained in the joint ledger

On `1/2<u<=10001/20000` and the original dyadic schedule, set

\[
W_N=\sum_{n\in S\setminus(\mathrm{tripleBand}\cup\mathrm{supply})}f_N(n),
\qquad \theta_N=\frac{\max(-\Re X_N,0)}{\Re Y_N}.
\]

`eventually_core_band_spending` proves exactly

\[
\begin{gathered}
0\le\theta_N\le\tfrac12,\\
\Re\bigl(u^{N+1}\mathrm{coreResponse}_N\bigr)
=u^{N+1}\bigl(\Re W_N+\max(\Re X_N,0)+(1-\theta_N)\Re Y_N\bigr).
\end{gathered}
\]

Consequently `eventually_core_band_floor` gives the direct signed bound

\[
\boxed{
\Re\bigl(u^{N+1}\mathrm{coreResponse}_N\bigr)
\ge u^{N+1}\bigl(\Re W_N+\max(\Re X_N,0)+\tfrac12\Re Y_N\bigr).
}
\]

All positive triple credit and at least half the supply remain in the
comparison. The full complement stays signed, with all other prime
counts and radial intervals present. The enlarged supply overlaps the
earlier supply; their credit cannot be counted twice. This theorem is a
component floor, not an independent numerical floor for the whole core.
The cofinal `-79/1000-o(1)` target for `J_N+C_N` remains open.

## Optional quantitative check

The [probe](../scripts/probe_riesz_band_compensation.py) and
[recorded output](riesz-band-compensation-probe.json) evaluate the explicit
proof constants and sample the same geometry with ordinary prime densities.
The floating evaluation of the proof's width witness at sample height
`54` is about `3.52e-11`: the current proof is very conservative.
This is not a certified numerical width or a finite starting threshold.

The density model suggests more capacity, but also shows its limit:

| Width `η` | Triple absolute mass / positive supply, `N=262144` |
| --- | ---: |
| `1e-5` | about `0.0437` |
| `3e-5` | about `0.399` |
| `1e-4` | about `4.44` |
| `1e-3` | about `444` |

These are uncertified quadratures, with allocation and further arithmetic
eligibility tests omitted. The height is not asserted to be a zero
ordinate. The model's cancellation of the real triple sum is sensitive to
the total-log phase and sampling error; it supplies no signed transport
theorem. No displayed numerical estimate enters Lean or routine CI.

The next arithmetic issue is coverage: more of the triple shares and
radial range must be compared against available signed credit **without
reusing any supply**, while retaining the remaining prime counts. Merely
deleting this paid pair or bounding the two remaining pieces separately
would be stronger work than the joint floor requires.

The [subsequent radial comparison](zeta-riesz-radial-compensation.md) now
discharges the radial coverage step for some fixed positive balanced share
width: distinct slabs receive disjoint positive supplies, and the uncovered
edge labels have a source-scale geometric allowance. The remaining share
and prime-count complement is still open. The older and newer supply
credits overlap and must not be added as separate reserves.
