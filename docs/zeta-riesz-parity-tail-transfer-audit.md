# Signed insertion tail and the remaining masked phase transfer

Continuation from `6e42991ac4ba43f0deb75c36425647d0c87a3bcf`.
The literal `FullParityPacket`, every finite mask, its exact rest ledger,
the paid factorial errors, and `LocalizedTypeIIBound` are unchanged.

**The requested literal packet bound is not proved.** The new quantitative
theorem bounds the complete 12+ series of the **supported inverse kernel**,
uniformly in a positive auxiliary lower cutoff. The empty-cofactor boundary,
the passage to zero auxiliary cutoff, and the transfer through the actual
coupled arithmetic masks are separate, unresolved obligations. Do not label
this a bound for the complete positive-cutoff cascade or for the arithmetic
packet.

## The entire signed support-insertion tail

Put `r=7/250`, retain `0<a<=r`, and let

\[
\lambda_a=\int_a^r\frac{dx}{x},\qquad
P_{0,a}(g)=\mathbf1_{g\le0},\qquad
P_{k+1,a}(g)=\int_a^rP_{k,a}(g-x)\frac{dx}{x}.
\]

These are actual nested density integrals, not numerical weights.
`jumpCount_properties` proves positivity, boundedness by `lambda_a^k`,
and monotonicity in the gap. `rawInsertion_succ` and `nestedSupport_eq`
identify the binomially compensated counts with repeated application of
the exact two-shift support difference

\[
f(s,d)\longmapsto\int_a^r
  [f(s-x,d)-f(s-x,d-x)]\frac{dx}{x}.
\]

The starting function is the existing `supportKernel(s,d)=1_(s<=d)`.
`insertedSupport_insert` proves the same difference identity for the
existing finite subset kernel. All subset signs and both coordinates
remain. The factorially normalized order-`k` term is

\[
I_{k,a}(g)=\sum_{i+j=k}
 \frac{(-\lambda_a)^i}{i!}\frac{P_{j,a}(g)}{j!}.
\]

`supportInsertionSum_eq` proves an absolutely convergent resummation:

\[
\sum_{k\ge0}I_{k,a}(g)
 =e^{-\lambda_a}\sum_{j\ge0}\frac{P_{j,a}(g)}{j!}\ge0.
\]

The proof estimates this positive compensated sum **after** cancellation.
For a tilt `t>=0`, `jumpCount_tilt` bounds its exponential moment. Convexity
of the exponential, with `t=2/r`, gives

\[
\int_a^r\frac{e^{tx}-1}{x}\,dx\le e^2-1.
\]

For the proved literal gap `g>289/1000`, the resulting bound is

\[
0\le\sum_{k\ge0}I_{k,a}(g)
 \le\exp(e^2-1-2g/r)<10^{-6}.
\]

Lean checks the final exponential inequality using rational bounds, with
no numerical quadrature. The estimate is uniform even as `lambda_a`
diverges when `a` tends to zero.

The first eleven lower orders vanish. At order eleven only the positive
jump term remains; its support forces every coordinate above `9/1000`.
`eleven_insertion_bounds` proves

\[
0\le I_{11,a}(g)\le\frac{\log(28/9)^{11}}{11!}<10^{-6}.
\]

Subtracting this one term from the full compensated sum proves

\[
\left|\sum_{k\ge12}I_{k,a}(g)\right|<10^{-6}.
\]

`nested_tail_core_bound` states this directly for the repeated two-shift
kernel at the original moving length and core coordinates. The series
runs to infinity; there is no numerical count truncation or termwise
absolute-value allowance.

## Boundary that this estimate does not pay

The proved transform renewal is still

\[
G_b-G_a=(e^A-1)(G_a-1/z^2).
\]

The supported-kernel insertion is only one part of its inverse. In a
one-sided inverse transform the total and cutoff variables also have
nonnegative support, whereas the existing `supportKernel(s,d)` is defined
on all real arguments. Once enough shares have been inserted, `s-sum x`
can cross zero. The empty-cofactor term and this support boundary cannot
be discarded. The new estimate neither identifies the unrestricted
support-insertion sum with `G_r` nor proves the positive-cutoff inverse
formula used by the Dickman/Buchstab numerical model.

Uniform bounds for every positive auxiliary cutoff also do not, by
themselves, prove convergence as that cutoff tends to zero. These are
explicit remaining steps before calling the entire continuum defect paid.

## Why the one-leg phase theorem is insufficient for the share mask

The new `ZetaRieszParityMaskedPhaseAudit` is a checked **analytic-mode
counterexample to a general inference**, not actual prime data or a
counterexample to `FullParityPacket`.

Take

\[
u=\frac{10001}{20000},\quad a=\frac{20001}{40000},\quad
z_1=a+\frac i{10},\quad z_2=a-\frac{43i}{370}.
\]

Both modes satisfy `|z_i|>u`. Lean proves their complete moments
`(u/z_i)^k` tend geometrically to zero, uniformly over all `k>=N/200`.
Adding these errors to minus one preserves the individual simple-zero
phase limits. This audit already respects the repaired lower-order range;
it is not another objection based on order-zero atoms.

However, the correlated total-order integral over exactly the retained
largest-share interval is

\[
B_N=\int_{43/80}^{9/16}
 \left(\frac{u}{qz_1+(1-q)z_2}\right)^{N+2}\,dq.
\]

At its lower endpoint the denominator is exactly `a<u`; at its upper
endpoint it is `a+i/185`, whose norm is greater than `u`. Lean evaluates
the antiderivative and proves

\[
(N+1)(a/u)^{N+1}B_N\longrightarrow\frac{u}{(8/37)i}\ne0.
\]

Consequently `not_eventually_band_bounded` rules out **every** fixed
eventual norm bound for this masked integral, despite complete-mode decay.
`scaled_defect_not_eventually_bounded` proves the same for `c*B_N` for
every nonzero complex constant `c`, however small. A small fixed continuum
defect is therefore insufficient for this general transfer rule.
Separate exposure outside a disk does not imply exposure of weighted
combinations of modes. The hard share boundary can retain an endpoint
that the complete prime moments suppress.

The literal Riesz coefficient and its complete prime-count cascade impose
additional information, so this is not a no-go theorem for the actual
packet. It proves that applying `eventually_good_product_phase` to the
masked packet without another joint estimate is invalid as a general
argument. The existing `interior_variation_fibre` also retains a nonzero
coefficient on a region where the residual share fits only one prime;
an arbitrary joint prime discrepancy is not automatically annihilated
by adding higher counts on that same fibre.

## Numerical tests and their limits

`scripts/probe_riesz_masked_phase.py` evaluates the exact analytic integral
above. At `N=4096` its norm is about `0.000238`; by `N=131072` it is about
`0.01238`, and at `N=262144` it is about `4.34`. The individual complete
mode errors continue to decrease. The Lean limit theorem, rather than
these samples, certifies the eventual obstruction to the general inference.

`scripts/probe_riesz_multiphase_cascade.py` additionally tests the candidate
all-count delay inverse with several analytic modes. It retains the
largest/least-share masks in a fixed total-log slice, and audits its FFT
convolutions against the inverse-product identity. It does not perform
the radial factorial integration or evaluate actual primes. Its large
fixed-slice values include same-mode oscillations which can cancel in
that radial integral. The convolution audit errors also exceed some
reported small residuals. Thus these outputs do **not** establish growth,
decay, or a no-go result for the literal all-count packet.

The original single-phase probe was separately refined to 3200 and 6400
steps per unit: its largest sampled continuum packet norm is respectively
`8.0374947653e-14` and `8.0374898614e-14`. This remains exploratory evidence
for the candidate delay inverse, not a certified arithmetic bound.

The subsequent [coupled radial audit](zeta-riesz-radial-mode-audit.md)
integrates the original radial window and moving length. Its ordered
all-count modal sector retains delayed growth; its checked Lean additions
certify the positive saddle exponent and modal-share separation. It does
not establish growth of the full mixed-mode measure or the literal packet.

The decisive missing theorem is still a **joint masked phase estimate**
using the actual prime measure and the full Riesz/count structure, including
any mixed-mode boundary response. The independent arithmetic floor for
`fullParityRest` is also still open; its existing positive allowance
continues to diverge. No source ledger is recomputed by assuming the packet
small, and no RH contradiction or new zero-free region is asserted.
