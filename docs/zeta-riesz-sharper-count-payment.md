# A smaller count ceiling for the whole joined floor

`ZetaRieszSharperCountPayment` independently pays an additional population
of the original core. On the unchanged native schedule

\[
K_j=2^{j+3},\qquad N_j=8(j+4)K_j,
\]

the new retained count endpoint is

\[
M_j=\lfloor K_j/768\rfloor+1.
\]

Previously the independent count payment left counts below `K_j/512`.
The new endpoint is asymptotically two-thirds of that endpoint. The exact
rounding theorem `countCeiling_comparison` proves, for `j>=9`,

\[
3(M_j-1)\le2K_{j-9}<3M_j.
\]

This is a reduction of a **count interval**, not a claim that one-third of
the remaining source mass, energy or floor difficulty has been removed.
Fixed counts and the growing intermediate counts remain in the signed sum.

## The independent geometric estimate

For every selected squarefree label with `768*omega(n)>=K_j`, the full count
tilt supplies

\[
K_j^{\omega(n)}\ge e^{N_j/9216}\qquad(j\ge64).
\]

The new ingredient is the stronger dyadic logarithmic estimate
`K_j*log K_j >= N_j/12`. It uses a rational lower bound for `log 2`.
All selected counts are joined inside the existing finite Euler bound:

\[
\sum_{n\in S}2^{\omega(n)}n^{-\sigma}
\le \exp(2K_j\operatorname{countMass}(\sigma)-N_j/9216).
\]

Here `S` is any finite squarefree selection with the stated count condition;
no prime-density replacement or new cancellation hypothesis is used.
Use the summable tilt

\[
q=499999/1000000,\qquad \sigma=3/2-q=1000001/1000000.
\]

Because `K_j/N_j=1/[8(j+4)]`, the Euler exponent is eventually at most
`N_j/1000000`. The constant `countMass(sigma)` is finite but unevaluated;
**no effective starting order is claimed**. Lean certifies the rate

\[
\frac{U}{q}\exp(-1/9216+1/1000000)
\le e^{-1/200000},\qquad U=10001/20000.
\]

For clarity, the certified exponent uses

\[
\log(U/q)\le U/q-1=51/499999,
\]

so the combined upper exponent is about `-5.51e-6`. The displayed geometric
rate is conservative. Its proof is rational/analytic; it is not a floating
certificate. It is slower than the previous `K/512` payment, in exchange
for covering a larger population.

`eventually_sharper_count_sum_bound` therefore proves, eventually and
uniformly over every height and restricted radius,

\[
\left\|u^{N_j+1}\sum_{n\in S}a_nK_{N_j}(3/2+iy,n)\right\|
\le \frac{203}{50}U(N_j+1)e^{-N_j/200000},
\]

provided the existing coefficient majorant `norm(a_n)<=2*logMajorant(n)`
holds and `log n<=203N_j/100`. These conditions are supplied unconditionally
for the actual residual coefficient when applying the theorem to the core.
The generic statement also accepts correlated coefficient masks satisfying
that same proved majorant.

## Exact transfer to the original floor

`eventually_norm_core_count_change_le` applies this estimate to

\[
\operatorname{coreResponse}(u,y,N_j,K_j)
-\operatorname{coreResponse}(u,y,N_j,M_j).
\]

The existing exact count-filter identity identifies the difference with
the deleted population. Every original physical, radial, nondominant and
allocation condition stays in that population, and its full complex phase
is retained. Nonsquarefree labels vanish exactly. No label is completed,
no supply debit is introduced and no earlier favorable credit is reused.

The original `joinedPhysical(u,y,N_j,K_j)` now satisfies the checked
comparison

\[
\operatorname{Re}(u^{N_j+1}\operatorname{joinedPhysical})
\ge -\sqrt{\frac{129N_j}{200}\max(E_{M_j},0)}-\operatorname{err}_j,
\qquad \operatorname{err}_j\to0.
\]

`E_M` is the actual signed `nonOrbitEnergy` of the **entire remaining core**
with counts below `M_j`, selected adverse cutoffs once on that whole
population. All lower counts and their cross terms remain. The error
contains the four original pair prices, the original core/joined bridge
and this new count allowance, each once.

There is no assertion that the new energy is smaller than the old energy:
signed cross terms and the adverse set can change when a population is
removed. The comparison is justified by the bound on the actual complex
carrier difference. This is an independent geometric population payment,
not a new representation of an unpaid error.

The sufficient numerical budget `3/(320*(N_j+1))` for `E_M` remains open.
In particular, balanced triples and their signed interactions with higher
counts remain. The `-79/1000` floor, multiplicity ceiling, contradiction and
new zero exclusion are **not proved** by this slice.

Focused direct/targeted Lean, ordinary root, namespace lint and transitive
standard-axiom checks are recorded in `riesz-sharper-count-payment-audit.json`.
The published README/explorer endpoints and prior mathematical sources are
unchanged. Work remains local; no commits, pushes or broader publication
gates are performed.
