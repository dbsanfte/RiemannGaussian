# Literal joint transfer with paid exterior and owner errors

This continuation strengthens the arithmetic estimate. It does **not** prove
the modal cancellation estimate for the remaining literal sum, packet decay,
an independent signed floor, or any new zero exclusion. All previous no-go
audits remain in force.

## What changed mathematically

The prior constant-weight modal test required nonresonant exterior endpoints.
That condition does not follow from merely widening a share interval.
The literal carrier has additional information: its exact factorial rectangle.
Using that information, several restrictions can be removed with independently
proved source-scale errors, before any prime-phase replacement.

Write `U=10001/20000`, `σ=1+1/262144`, and

\[
r=U\frac{262144}{131071}e^{-1/1600}<1
\qquad (r\approx0.9994827582396332).
\]

The strict inequality is proved in Lean. Let `Cσ` denote the existing finite
`zetaMoebiusLogMajorantMass σ`.

### Exterior largest-share boundaries

[`ZetaRieszJointBoundary`](../RiemannGaussian/ZetaRieszJointBoundary.lean)
keeps the original rectangle allocations: the largest marked order satisfies
`21N<=40j<=23N`, the least-prime order satisfies the original derivative-shifted
cuts, and the correlated total base order is `N+1`. Orders zero and one on
other primes are retained.

For a genuine squarefree label, outside

\[
\tfrac12<\frac{\log p_{\max}}{\log n}<\tfrac35,
\]

`weight_exterior` proves the entire rectangle mass is at most
`2 exp(-N/1600)` for `N>=1`. The two concrete tilts are `11/10` and `9/10`.
Their rates are certified by exact rational-power comparisons, not the probe.

`exteriorPacket_bound` then bounds the **literal arithmetic sum** of those
exterior labels by `2 U Cσ r^N` after source normalization. This retains the
residual Riesz coefficient, old allocation, physical primes, count cutoff,
core total-log window and full phase. It is uniform even in moving heights.

The new `packet` joins all largest shares while retaining the existing
least-share interval `3/250..7/250` and all other original support masks.
`neighbors` is exactly its difference from the old `fullParityPacket`.
The ledgers are

\[
\begin{aligned}
J_N&=\mathrm{fullParityPacket}_N+\mathrm{neighbors}_N,\\
\mathrm{coreResponse}_N&=J_N+\mathrm{rest}_N,\\
\mathrm{fullParityRest}_N&=\mathrm{neighbors}_N+\mathrm{rest}_N.
\end{aligned}
\]

Thus the neighboring pieces are charged to the old unpaid rest, with their
original signs. They are not a free reserve or separately bounded allowance.
The old packet's definition has not changed.

### Exact actual-prime expansion

[`ZetaRieszJointPrimeTransfer`](../RiemannGaussian/ZetaRieszJointPrimeTransfer.lean)
proves, for every literal allocation with `sum d_p=N+1`,

\[
\operatorname{allocationWeight}(d)K_N(s,n)
=\frac{N+1}{\log n}\prod_{p\mid n}K_{d_p}(s,p).
\]

This is an equality of finite arithmetic expressions, with the full complex
phase and all low orders. It is not a product of separately completed prime
limits. The rectangle condition remains inside the same sum over allocations.

### Largest-prime ownership

[`ZetaRieszJointOwnerTransfer`](../RiemannGaussian/ZetaRieszJointOwnerTransfer.lean)
proves that every wrongly marked prime has log share at most `1/2`.
Its exact rectangle mass is therefore at most `2 exp(-N/1600)`.

Removing the old largest-share cut changes the applicable count ceiling:
`jointBox_count_le` proves **83**, rather than reusing the old 39.
Summing wrong incidences costs at most `166 exp(-N/1600)` per label.
`wrongPacket_bound` gives the independent source-normalized bound
`166 U Cσ r^N` for their literal finite sum, uniformly in height.

Consequently `marked_joint_transfer_bound` and
`tendsto_marked_sub_joint` prove

\[
\left\|u^{N+1}
  \bigl(\mathrm{markedPacket}_N-
    (\mathrm{fullParityPacket}_N+\mathrm{neighbors}_N)\bigr)\right\|
\le166U C_\sigma r^N\longrightarrow0.
\]

`marked_mass_le_one` also proves for `N>=21` that the sum over **all** marked
prime incidences uses at most one complete allocation. The selected marked
order is a strict majority; two such primes cannot occur in one allocation.
This transfer has no incidence averaging or duplicate carrier mass.

### Old allocation factor

[`ZetaRieszJointAllocationError`](../RiemannGaussian/ZetaRieszJointAllocationError.lean)
estimates the old allocated fraction **jointly** with the retained rectangle.
It does not require every prime to lie below the former `9/16` share cut.
On every label in the enlarged box, `old_allocation_weight` proves

\[
\theta_N(n)\operatorname{weight}_N(n)
 \le83e^{-N/3200}.
\]

Including the wrong marked incidences gives the bound `249 exp(-N/3200)`.
The exact `allocation_ledger` is `rawMarkedPacket = markedPacket +
allocationError`; the raw packet removes only the factor `1-theta`.
For

\[
r_a=U\frac{262144}{131071}e^{-1/3200}<1,
\]

`allocationError_bound` proves its source-normalized norm is at most
`249 U Cσ r_a^N`, uniformly in height, order and count cutoff.
Combined with the ownership bound, `rawMarked_joint_transfer_bound` gives

\[
\left\|u^{N+1}
 \bigl(\mathrm{rawMarkedPacket}_N-
 (\mathrm{fullParityPacket}_N+\mathrm{neighbors}_N)\bigr)\right\|
\le U C_\sigma(249r_a^N+166r^N)\longrightarrow0.
\]

Thus the allocation mask is actually paid, rather than erased in a model.
This estimate uses no zero hypothesis or prime-phase approximation.

## Continuing through the least-share mask

[`ZetaRieszLeastBoundary`](../RiemannGaussian/ZetaRieszLeastBoundary.lean)
now joins the least-share neighbors as well. Its `fullBand` imposes **no**
largest-share or least-share interval: it retains the original core,
physical primes, squarefreeness, count and nondominant support, and the
same full factorial rectangle. No low individual order is removed.

The concrete tilts `3/2` and `2/3` prove `weight_least_exterior`:

\[
\frac{\log p_{\min}}{\log n}\notin(1/200,3/50)
\quad\Longrightarrow\quad
\operatorname{weight}_N(n)\le3e^{-N/1600}.
\]

The actual `h+1` derivative shift is retained. Combined with the
largest-share estimate, **all** exterior labels outside

\[
1/2<p_{\max}\text{-share}<3/5,
\qquad1/200<p_{\min}\text{-share}<3/50
\]

have source-normalized norm at most `3 U Cσ r^N`. This is a literal
arithmetic estimate uniform in the phase height and count cutoff.
`leastNeighbors` is exactly the contribution newly drawn from the previous
rest, and both rest ledgers are proved. Extending the support creates no
unaccounted reserve.

The new interior has its own proved count ceiling **200**. The ownership
and old-allocation estimates are extended to it, rather than borrowing
83 or 39. The simultaneous error weight simplifies exactly to

\[
\operatorname{wrongWeight}_N(n)
 +\theta_N(n)\operatorname{weight}_N(n)
 \le600e^{-N/3200}.
\]

`cleanupError_bound` gives source-normalized error `600 U Cσ r_a^N`.
With the names from `ZetaRieszLeastBoundary`, the exact terminal ledger is

\[
\mathrm{coreResponse}
=\mathrm{rawInteriorPacket}+\mathrm{rest}
 -\mathrm{cleanupError}+\mathrm{exteriorPacket}.
\]

Both displayed errors tend to zero independently of any zero hypothesis.
`tendsto_raw_sub_full` proves the raw interior and the full joined packet
agree asymptotically at source scale. It does **not** prove either is small.

## The exact remaining signed object

`ZetaRieszLeastBoundary.rawInteriorPacket_riesz_expansion` cancels the product-log normalization and
identifies the remaining finite sum as

\[
-\frac{N+1}{L_N}
\sum_{n\in\mathrm{fullBand}_N\cap\mathrm{interior}}\mathcal R_{L_N}(n)
\sum_{p\mid n}\sum_{d\in\mathrm{markedAllocations}(N,n,p)}
\prod_{q\mid n}K_{d_q}(3/2+iy,q).
\]

Here the summation support still contains squarefreeness, the original
core/nondominant and count support, the physical prime masks, and the new
outer share boundaries whose complements are now paid.
`markedAllocations` retains the canonical **least-prime** identity and the complete correlated rectangle
and total order. The Riesz hinge remains label-dependent; the old allocation
factor has been removed with the independently proved error above.

The largest-prime comparison has been paid; the marked prime need no longer
be ordered against the other primes. The remaining task is a signed estimate
for this coupled object, especially its least-prime/Riesz correlations.
The independent error estimates do not permit applying separate completed-leg
limits through these remaining masks. No estimate for `rawInteriorPacket` itself
is asserted, and the old diverging `restAllowance` is not reused.

### Radial error on the actual marked sum

`ZetaRieszLeastBoundary.radialBand_core` proves that intersecting the new
`rawRadialBand` with `1.95N < log n <= 2.03N` gives exactly the support of
`rawInteriorPacket`. The wider band retains the original nondominant
support, physical primes, squarefreeness, count restrictions and share interior.
It is a finite arithmetic support, not an unrestricted completion.

For `N>=21`, the strict-majority incidence bound gives total marked
weight at most one on every squarefree label. Applying the existing arithmetic
deviation estimate to this exact weight proves `exists_raw_radial_error`:

\[
\exists\,0\le r_{\rm rad}<1,\ C\ge0,\qquad
\left\|u^{N+1}(\mathrm{rawRadialPacket}_N-
                    \mathrm{rawInteriorPacket}_N)\right\|
\le C r_{\rm rad}^{N}.
\]

The constants are independent of `y`, `K` and `0<=u<=10001/20000`.
`tendsto_rawRadial_sub_full` combines this with the independently paid
ownership/allocation/share errors. Thus the wider signed radial sum
has the same source-scale asymptotics as the literal joined packet.
Its own signed estimate remains open. This theorem neither transfers a
synthetic density to primes nor removes the canonical least-prime condition.

### Independent bound for the retained high-count tail

`high_count_least_share` uses the largest-share lower bound as well as
squarefreeness: `omega(n)>=64` forces `leastShare<=1/126`. The exact least
factorial order is at least `N/100-1`, so the tilt `q=5/4` gives

\[
\log(505/504)-\tfrac1{100}\log(5/4)\le-\tfrac1{5000}.
\]

`count_tail_tilt` certifies this with rational arithmetic. Every marked
incidence then has mass at most `2 exp(-N/5000)`. Retaining the proved
count ceiling 200 gives `highCountPacket_bound`:

\[
\left\|u^{N+1}\mathrm{highCountPacket}_N\right\|
\le400U C_\sigma r_{\rm count}^{N},\qquad
r_{\rm count}=U\frac{262144}{131071}e^{-1/5000}<1.
\]

The bound is independent of zeros, uniform in height and count cutoff, and
retains the literal Riesz coefficient, phase and every support mask.
`count_ledger` splits the raw interior exactly into `lowCountPacket` and
`highCountPacket`; `tendsto_highCountPacket` proves decay of the latter.
The former contains counts **3 through 63** together with their signs.
No separate positive allowances are introduced for those remaining classes.
Their joint signed estimate is still open. The following joint tilt improves
this first cutoff without changing or deleting any of its theorems.

### Joint factorial tilt: the tail now starts at 56 factors

For any marked prime `p`, squarefreeness and `omega(n)>=56` imply

\[
 x_p+55x_{\min}\le1,\qquad x_q=\log q/\log n.
\]

The large and least factorial slots satisfy `j>=21N/40` and
`h>=N/100-1` simultaneously. Tilting both slots by `341/340` and `79/68`
keeps their correlation. Their multinomial generating function is at most
`(341/340)^(N+1)`, because `79/68-1=55(341/340-1)`.
Lean checks the exact rational-power inequality which gives

\[
 \tfrac{19}{40}\log(341/340)-\tfrac1{100}\log(79/68)
 \le-\tfrac1{9700}.
\]

`markedWeight_joint_count_tail` therefore bounds each literal marked
incidence by `2 exp(-N/9700)`. With `sigma'=1+1/1048576`, the new terminal
arithmetic estimate `jointHighCountPacket_bound` is

\[
 \|u^{N+1}\mathrm{jointHighCountPacket}_N\|
 \le400U C_{\sigma'} r_{56}^N,\qquad
 r_{56}=U\frac{1048576}{524287}e^{-1/9700}<1.
\]

The rate is about `0.999998809568`: the saving is strict but slow, and the
majorant constant is not claimed small. The estimate is independent of zero
hypotheses and uniform in the full phase height and moving count cutoff.
It retains every literal support condition and the Riesz coefficient.

The exact `joint_count_ledger` leaves **counts 3 through 55** in
`jointLowCountPacket`. `fullPacket_sub_jointLow_bound` pays all three errors
explicitly: the count tail, ownership/allocation cleanup, and share exterior.
`tendsto_rawRadial_sub_jointLow` also connects the wider radial target to this
same signed expression. None of these theorems bounds that expression itself.
The complementary direct carrier still needs its independent signed floor.

## Quantitative checks

The optional
[`probe_riesz_joint_boundary.py`](../scripts/probe_riesz_joint_boundary.py)
writes [`riesz-joint-boundary-probe.json`](riesz-joint-boundary-probe.json).
It is excluded from ordinary CI and does not supply a Lean proof.

It checks the exact rational tilt inequalities and the finite binomial
marginals through `N=262144`. It also evaluates actual prime labels made
from distinct Mersenne primes, with deterministic Lucas--Lehmer checks in
the probe, at `N=400` and `1600`. Their radial window, physical-prime,
least-share and nondominant inequalities are checked explicitly. The full
complex finite-kernel and incidence ledgers agree to relative error below
`5e-97`. These are individual label checks, not an exhaustive evaluation of
the signed carrier or a Lean primality certificate.

A separate **unmasked** modal diagnostic uses the classical
[Euler beta integral](https://dlmf.nist.gov/15.6.E1):

\[
\int_0^1\binom Mj
 \frac{q^j(1-q)^{M-j}}{(qz_1+(1-q)z_2)^{M+2}}\,dq
=\frac{1}{(M+1)z_1^{j+1}z_2^{M-j+1}}
\quad(\Re z_1,\Re z_2>0).
\]

Numerical quadrature checks this identity at small order for the old seam,
retuned seam, and new exterior resonances. In this unmasked model the
factorial weight restores a product denominator and removes the spurious
convex-denominator growth. Its hypotheses omit the literal Riesz,
least-prime and finite radial masks; it is motivation for the next joint
analysis, not their transfer theorem. The existing masked counterexamples
therefore remain valid.

The first coupled diagnostic,
[`probe_riesz_joint_masked.py`](../scripts/probe_riesz_joint_masked.py),
uses scrambled Sobol sampling through prime count nine. At `N=4096` the
individual higher-count sampling errors are comparable to or larger than
`1/1000`, and the omitted count tail is unpaid. Its apparent residual is
**inconclusive**; it is not evidence for a surviving source or for decay.

The replacement diagnostic,
[`probe_riesz_joint_renewal.py`](../scripts/probe_riesz_joint_renewal.py),
sums all counts on a discretized cofactor-share measure. With
`a_i` the complex mode weight of a grid cell, it computes the coefficients of

\[
A(X)=e^{-\sum_i a_iX^i},\qquad
B(X)=e^{\sum_i a_iX^i},\qquad
A(X)B(XY).
\]

The coefficient at total index `n` and Riesz-shift index `j` is exactly
`A_(n-j) B_j`. Applying the one-sided ramp difference
`min(r,(d-j*dx)_+)` retains the distinguished least-prime insertion and
every subset sign. The cutoff makes the count expansion finite at each
total index, so no numerical count ceiling of nine or eleven is used.
An independent small-lattice subset enumeration checks its signs and
factorial symmetry divisors. This grid identity includes repeated grid
atoms; it is a quadrature model of the continuous density, **not** a
replacement of distinct squarefree primes by repeated primes.

The current diagnostic evaluates the exact finite factorial rectangle directly
at quadrature nodes, in floating point without a certified enclosure. It keeps
the moving `L_N/T`, radial window, least-share interval and full complex
synthetic mode product. Physical prime inequalities are explicitly masked;
some nodes near the wider least-share endpoints are inadmissible at smaller
orders. It removes the old allocation only after
the separate Lean estimate above. Grid, quadrature and precision checks are
recorded in the optional JSON artifacts; none is an arithmetic transfer
theorem or a proof of a uniform asymptotic rate. In particular finite-order
smallness does not overturn the previous delayed-growth no-go for fixed
positive least cutoffs.

The original all-count grid runs at `N=640,4096,8192` show very small
normalized responses. An independent 60-digit recurrence at `N=4096`,
least share `7/250`, and largest share `11/20` confirms rounding errors
below `1e-16` for the tested point. This validates the numerical computation
at that point, not continuum convergence. Increasing quadrature from 40
to 64 nodes changes the mixed response appreciably relative to its tiny
size; no digits of an asymptotic constant are certified.

The widened least-share diagnostic is in
[`riesz-joint-least-probe.json`](riesz-joint-least-probe.json). It evaluates
the finite binomial rectangle directly at quadrature nodes (no rectangle
interpolation) and uses `1/200..3/50`. The three-mode normalized residual
is about `1e-8` at `N=4096` and `2e-9` at `8192`, after all supported counts
are summed together. These finite synthetic values motivate the remaining
coupled estimate. They neither prove eventual decay nor include the full
actual zeta pole/analytic-remainder arithmetic transfer.

Normalization check: in total-log/share coordinates the prime-density
Jacobian contributes `1/T`. The coefficient contributes
`T H/λ`; these cancel, leaving `H/λ` against the radial factorial kernel.
The moving length and the Riesz ramp are evaluated before the radial
integration, not at a frozen saddle.

### Analytic-mode and quadrature audit

The optional analytic stress family has negative-residue modes
`xi=0` and `xi=1/40000-i/2`, plus a positive-residue mode
`xi=1/20000+3i/5`. The last mode has complete-leg coefficient radius
strictly greater than `4/3`. It is **not** asserted to be the actual zeta
analytic remainder. Its purpose is to test the coupled operation, rather
than infer masked convergence from complete legs.

The first coarse `N=2048` run appeared to grow. Refining the oscillatory
quadrature changes that conclusion: the narrow-window norm decreases from
about `4.01e-5` to `1.06e-5` at that same order. There is no certified growth
exponent in these data. Extending the synthetic radial interval to
`1.8N..2.2N` gives the following diagnostic values:

| Order | Joined norm | Old-share piece norm | Neighbour-piece norm |
| --- | --- | --- | --- |
| 2048 | `2.21e-8` | `3.94e-6` | `3.96e-6` |
| 4096 | `5.77e-9` | `7.29e-7` | `7.34e-7` |

The two pieces are summed with their complex signs before taking the joined
norm. The coarse split into old and neighbouring shares is diagnostic;
neither its boundary quadrature nor the joined continuum discretization
has an error enclosure. These observations do **not** prove eventual
smallness, exclude delayed growth, or overturn any earlier fixed-cutoff
counterexample.

Artifacts: [refined core](riesz-joint-refined-core-probe.json),
[refined radial](riesz-joint-refined-radial-probe.json), and
[higher order](riesz-joint-high-order-probe.json). The probe now separates
largest-share and radial quadrature orders. It uses a finite-mode
differential recurrence for the same grid exponential, cross-checked against
the quadratic recurrence, and checks the accelerated convolution against
direct summation at sampled nodes. Radial batching bounds memory use without
changing quadrature nodes. All of this remains outside ordinary CI.

Doubling the least-share quadrature at `N=4096` changes the joined norm
from `5.77e-9` to `8.52e-9`; see
[least-share refinement](riesz-joint-least-refinement-probe.json).
The scale remains small, but the relative change reinforces that no digits
of the small residual or an asymptotic rate are certified.

The live arithmetic gap is cancellation in `rawRadialPacket`, with its
canonical least prime, Riesz clock, count and physical restrictions and
correlated orders. The finite unmarked negative-mode support theorem does
not by itself control that ordering. No bound for this sum or its signed
complement is claimed here.

### Close-mode and multiplicity stress test

A more sensitive synthetic family uses `xi=0, 1/40000 +/- (3/500)i`.
Each competing denominator satisfies `abs(U-xi)>U`, so the selected mode
remains exposed. These are not asserted zeta zeros. The selected multiplicity
is one; the two competing multiplicities are varied together. The probe
keeps the moving length, finite rectangle, least-prime ordering, all grid
counts, phase and radial kernel, with joined share ranges `0.5..0.6`,
`0.005..0.06` and radial range `1.8N..2.2N`.

| Competing multiplicities | Order | Joined real response | Qualification |
| --- | ---: | ---: | --- |
| 1, 1 | 8,192 | `-1.14e-10` | Coarse diagnostic |
| 1, 1 | 32,768 | `-7.13e-10` | Coarse diagnostic |
| 1, 1 | 65,536 | `-5.5308e-9` | Grid and quadrature refinement agrees to about 0.1% |
| 3, 3 | 8,192 | `+0.04605` | Coarse diagnostic |
| 3, 3 | 65,536 | `-0.0055884` | Refinement changes the value by about 0.15% |

The first three rows do not prove decay: their magnitude is increasing on
this finite range. The last two do not prove eventual growth: their sign
changes and magnitude decreases. They do show that the earlier small
numbers for simple competing modes cannot justify a general estimate.
Even the refined values have **no certified quadrature or grid enclosure**.

Reports: [simple close modes](riesz-joint-close-modes-probe.json),
[simple refinement](riesz-joint-close-refined-probe.json),
[multiple modes](riesz-joint-close-multiple-probe.json), and
[multiple-mode refinement](riesz-joint-close-multiple-refined-probe.json).
A same-half-plane control with zero horizontal gain is also recorded in
[the half-plane probe](riesz-joint-close-halfplane-probe.json); it gives a
similar small response at 65,536, so the finite simple-mode rise is not
evidence of a proved rightward-resonance exponent.

At order 262,144 the multiplicity-three diagnostic is especially sensitive:
[one grid/quadrature choice](riesz-joint-close-multiple-high-probe.json)
gives about `-0.0854`, while
[a different grid with finer radial quadrature](riesz-joint-close-multiple-radial-probe.json)
gives about `-0.319`. Several resolutions differ between these two runs, so
this is not a controlled one-axis convergence comparison. Neither value is
a certified bound, and neither establishes an eventual growth exponent.
Resolving the signed residual requires further quadrature and grid checks;
the finite diagnostics cannot discharge or refute the arithmetic target.

The recurrence has an independent [65-digit rounding audit](riesz-joint-close-recurrence-audit.json).
At its checked grid points the accelerated recurrence differs from the
high-precision defining series by up to `3.47e-10` in absolute value
(`9.51e-11` after coefficient scaling), while the quadratic recurrence
differs by up to `2.27e-14`. Thus a small inverse-series product residual is
not itself a precision certificate. Exact conjugate mode pairs use real
recurrence coefficients, justified by conjugation invariance; arbitrary
complex families retain their complex coefficients. No arithmetic phase
is projected away. This audit checks rounding only, not the prime model,
continuum approximation or oscillatory quadrature.

The classical smallest/largest-prime duality is another possible identity,
but it does not currently supply a quantitative saving here: the literal
weights depend jointly on the full label, the least prime, all factorial
orders and the Riesz hinge. Applying the unweighted divisor identity leaves
those weighted divisor correlations to be bounded. The relevant classical
identity and its quantitative context are discussed by
[Alladi and Johnson](https://arxiv.org/html/2410.18259v1) and
[Alladi and Goswami](https://arxiv.org/html/2412.03088v1).
No new duality-based estimate is asserted.
