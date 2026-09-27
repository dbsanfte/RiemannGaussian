# Balanced-triple compensation throughout the radial core

The later [four-prime reserve theorem](zeta-riesz-four-prime-reserve.md)
combines this floor with sharper four/five-prime bounds on its untouched
complement. It preserves the paid band and half the supply below; no
compensation is counted twice.

[`ZetaRieszRadialCompensation`](../RiemannGaussian/ZetaRieszRadialCompensation.lean)
extends the [single-interval comparison](zeta-riesz-band-compensation.md)
across the original core. For each fixed `|y|>=16`, it pays a fixed positive
balanced triple share band using disjoint positive four-prime supplies,
with an independently vanishing allowance for the uncovered radial edges.
It retains the original factorial moment, moving length, allocation,
complex phase and arithmetic masks.

This is an independent **component floor**, not the whole
[joint `J_N+C_N` floor](zeta-riesz-joint-floor.md). Its width is existential
and conservative. It does not pay every balanced triple configuration or
the full set of other prime counts. The height condition is available at
every hypothetical right-half zero from the existing
`ZetaRieszShiftedCenter.height_gt_fiftyFour`; the comparison itself uses no
zero hypothesis, simplicity or exposure.

## Disjoint supply for each radial interval

The moment order remains `N`. The radial index `M` varies over

\[
I_N=\{M\in\mathbb N: 1.95N<2M,\quad2M+1\le2.03N\}.
\]

Each triple slab has `2M<=log n<2M+2` and every prime log within `η*M`
of `2M/3`. The four-prime supply reuses the existing three-dimensional
grid at `M`, translated by `0<=v_M<=1/2`. A common fixed width
`0<h<=1/20` makes its entire phase negative, `cos(y log n)<=-1/2`.
Its total logarithm lies in `(2M,2M+1]`. Consequently:

- every supply label is in the original `coreBand`;
- supplies at distinct `M` are disjoint as integer labels;
- triple slabs are disjoint, including their upper-endpoint convention;
- triple and supply labels are disjoint by actual prime count.

`tuple_linear_wide` checks the reflected-linear chamber throughout
`271M/200<=L<=143M/100`; `tuple_coefficient_le_wide` gives `c_L<=-M/20`.
`eventually_length_on_slabs` proves that the actual moving length at
order **N** satisfies these inequalities for every `M` in `I_N`.
No moment order is silently replaced by the radial index.

## The common factorial scale is retained

The scalar envelope used in the comparison is

\[
E_{N,M}=e^{-3M}(2M)^N/N!.
\]

Actual prime-count lower bounds and the exact negative coefficient and
phase give a positive supply bound. The whole triple slab has a
Chebyshev upper count and an original-kernel upper bound. Uniformly in
the permitted slabs, these are

\[
\begin{aligned}
\Re Y_{N,M}&\ge c\frac{M e^{2M}}{M+1}E_{N,M},\\
\|X_{N,M}\|&\le B\eta^2\frac{M e^{2M}}{M+1}E_{N,M},
\qquad B=27(6\log4)^3e^8.
\end{aligned}
\]

`eventually_slabs_spending` chooses a single fixed positive `η`, depending
on the height, so that every triple slab costs at most half its own
supply. `union_spending` then proves

\[
\boxed{\quad
\left\|\sum_{M\in I_N}X_{N,M}\right\|
\le\frac12\Re\left(\sum_{M\in I_N}Y_{N,M}\right).
\quad}
\]

The supplies are disjoint, so this sum does not reuse any positive credit.
The proof uses the prime number theorem only for unsigned populations
in fixed-width multiplicative intervals. It performs no signed
prime-density approximation, phase transfer or cofactor completion.

## Coverage and the independently paid edges

`balancedTriples S N η` selects every squarefree three-prime label in
the original support satisfying

\[
\left|\log p-\frac{\log n}{3}\right|\le\frac{\eta N}{4}
\quad\text{for every prime factor }p.
\]

There is no extra radial restriction in this definition.
`eventually_core_balanced_nonempty` proves it eventually nonempty for
every fixed `η>0` on the original schedule.

`balanced_mem_radialTriples` proves that all such labels with

\[
1.952N<\log n\le2.029N
\]

belong to the paid union once `N>=4000` and `η*N>=4`. It chooses
`M=floor(log n/2)` exactly. The remaining labels are confined to the two
outer radial edges.

`radial_edge_costs` proves both endpoints have a strict factorial
deviation margin at `u=10001/20000`. `exists_missed_bound` then gives

\[
\left\|u^{N+1}\sum_{n\in B_N\setminus X_N^{\rm labels}}f_N(n)\right\|
\le C r^N,\qquad0\le r<1,
\]

uniformly in height, allocation set, finite selection and
`0<=u<=10001/20000`. Here `B_N` is the full balanced selection and `f_N`
the literal residual atom. This is an actual source-scale geometric
bound, not a relative-mass estimate. Its constants and starting order
are not numerically evaluated. `tendsto_edge_allowance` supplies the
vanishing allowance on the original dyadic schedule.

## The resulting signed floor

Let `X_N` be the paid triple-union sum, `Y_N` its positive supply, and
`W_N` the **signed original core sum** after removing the triple union,
its supply and the full balanced band. On `1/2<u<=10001/20000`,
`eventually_core_balanced_floor` proves

\[
\boxed{
\Re\bigl(u^{N+1}\mathrm{coreResponse}_N\bigr)
\ge u^{N+1}\left(\Re W_N+\max(\Re X_N,0)
+\tfrac12\Re Y_N\right)-C r^N.
}
\]

The exact intermediate ledger also retains the actual unspent fraction
`1-θ_N`, where `0<=θ_N<=1/2`. All other prime counts and all unselected
share configurations remain signed. The supply overlaps earlier
constructions; none of their budgets can be added again without debiting
the credit already spent here.

The full cofinal `-79/1000-o(1)` floor remains open. The next target is the
remaining signed sum **together with** its unused positive credit. No
separate decay, zero exclusion or RH claim follows from this component
comparison.

## Optional numerical check

The [probe](../scripts/probe_riesz_radial_compensation.py) and
[output](riesz-radial-compensation-probe.json) sample the exact radial
indices with the original moment `N` and moving length. In the unproved
ordinary-prime-density model at height `54`, `N=262144`, two Sobol samples
give the following triple absolute mass / positive supply ratios:

| Slab width parameter `η` | Model ratio |
| --- | ---: |
| `1e-5` | `0.0830..0.0831` |
| `2e-5` | `0.3497..0.3498` |
| `3e-5` | `0.7931..0.7933` |
| `1e-4` | `8.86..8.88` |

These suggest limited spare capacity, not a proof at those widths or
orders. The probe omits allocation and further arithmetic eligibility
conditions, and its quadrature has no rigorous error enclosure. Tiny
signed radial averages are sensitive to phase sampling error. No actual
prime sum, untouched complement, or zero ordinate is certified. The
Lean constants are more conservative and use none of these numbers.
The probe is optional and does not run in ordinary CI.
