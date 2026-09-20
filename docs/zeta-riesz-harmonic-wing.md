# The remaining harmonic-cost budget

The goal is an independent cofinal floor for the **coupled** lower-prime-count
response and tapered wing. The exact evaluated head and central block remain
upstream:

$$
u^{N+1}(H_N+C_N)\longrightarrow-m^2c(u),\qquad
c(u)=\frac{\log(32/15)}{-2u\log u}-\log(17/15)<1.
$$

Here (u=3/2-\Re\rho), (m) is the analytic zero multiplicity, and the
original source range is (1/2<u<e^{-2/3}). The source statements retain
their explicit exposed-zero hypothesis. The initial contradiction target
concerns simple exposed zeros; no theorem here establishes that every
hypothetical off-line zero is simple or satisfies these restrictions.

The [joint cofactor estimate](zeta-riesz-joint-cofactor.md) now independently
bounds the original unpaid wing plus an explicit complete signed composite
companion by \(C_\gamma(N+1)^2e^{-N/64}\). All saturation, prime-prefix,
repeated-prime and unit corrections are accounted for. The remaining target
is the same finite count sum minus that companion; its independent lower
bound remains open. This is a bound for a coupled sum, not separate decay
of the wing or a new zero-free region.

The [allocation follow-up](zeta-riesz-joint-allocation.md) pays the complete
companion outside the logarithmic window and a retained prime-factor sector
inside it. The latter has coefficient saving 3 exp(-N/140), and its entire
source-normalized sum has a height-uniform geometric bound. The subsequent
support comparison also pays or exactly eliminates every off-mask correction.
The combined reduction error vanishes uniformly at all real heights for each
fixed eligible radius. The exact source
survives in `ZetaRieszMaskSupport.retainedRemainder`; the joint floor for
that smaller finite sum remains open.

The exact evaluation also gives the **entire positive reserve**:

$$
u^{N+1}V_N^+\longrightarrow m^2v(u),\qquad
v(u)=\log(19/17)+\left(1-\frac1{-2u\log u}\right)\log(15/13).
$$

The retained carrier itself consequently tends to

$$
-m+m^2c_{\rm ret}(u),\qquad
c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13)<\frac{37}{40}.
$$

The limit keeps the original exposed-zero premises and
`1/2<u<exp(-11/16)`. The rational cost bound holds throughout the closed
radius interval. For simple exposed zeros an independent cofinal lower
bound of `-3/40` on the retained real sum would suffice. It remains unproved.
See [the exact retained source](../RiemannGaussian/ZetaRieszRetainedSource.lean)
and [the current arithmetic ledger](zeta-riesz-joint-allocation.md).

The [dominant-prime continuation](zeta-riesz-dominant-sector.md) now pays
every remaining term with an eligible prime carrying at least `13/20` of
the total logarithm. Its whole unassigned arithmetic sum has an explicit
two-rate geometric bound, uniform in height. The nonzero surviving support
has `log(p)<13/20*log(n)` for **every** prime factor. The exact source and
`3/40` deficit remain in `nondominantRemainder`; the independent floor for
that smaller signed carrier is the current target.

## The parts now paid

The prior [complete high-prime-count deletion](zeta-riesz-whole-prime-count-decay.md)
leaves all frequencies of the lower-count sum and the tapered wing on

$$
K_j=2^{j+3},\qquad N_j=8(j+4)K_j.
$$

All earlier frequency estimates remain available. The full high-count
deletion already includes those integers' low frequencies; their savings
are not added twice.

| Component | Compiled estimate | Scope |
| --- | --- | --- |
| Lower-count outer logarithmic tails | `exists_annular_window_error`: at most (Cr^N), (0\le r<1), outside (25N/16<\log n\le5N/2) | Independent of zeros; uniform in height, count threshold and (0\le u\le e^{-2/3}), for every fixed full complex filter |
| The same tails on the smaller radius interval | `exists_reserve_window_error`: at most (Cr^N) outside (7N/4<\log n\le9N/4) | Same uniformity, for (0\le u\le e^{-11/16}) |
| Original wing orders (lfloor13N/32\rfloor+1\le k\le\lfloor(15N+64)/32\rfloor) | `eventually_re_reserve_ge`: real normalized contribution at least (15m^2/544) | Exposed-zero phases, (1/2<u<e^{-11/16}); actual taper and finite-prime completion included |
| Original wing orders with (4N\le5(N+1-k)) | `eventually_norm_highWing`: at most (C(N+1)^2e^{-N/1024}\to0) | Exposed-zero premises and the same smaller radius interval |

The first two estimates control the complete discarded sums, with all their
frequencies. They follow from the exact deviation profile

$$
I(x)=x/2-1-\log(x/2),\qquad \log(2u)<I(x),
$$

with both strict endpoint inequalities proved in Lean. They do not use a
sign assumption. The positive wing bound uses actual exposed-zero phases
after an independent height-uniform completion estimate. The high-wing
bound uses an unconditional finite tapered high-leg estimate and a
source-conditioned bound on its complete low leg. The whole wing product
estimate is therefore not described as unconditional in height.

The new source modules are
[ZetaRieszWingReserve](../RiemannGaussian/ZetaRieszWingReserve.lean),
[ZetaRieszWingHighOrders](../RiemannGaussian/ZetaRieszWingHighOrders.lean), and
[ZetaRieszHarmonicWindow](../RiemannGaussian/ZetaRieszHarmonicWindow.lean).
The explorer exports exact declaration lines and transitive axiom audits.

## The fixed remaining arithmetic target

In the smaller interval, let (F_N^{\mathrm{win}}) be the original
lower-count sum, with its existing masks, intersected with

$$
3\le\omega(n)<K_j,\qquad 7N_j/4<\log n\le9N_j/4.
$$

It retains the original signed squarefree Riesz coefficient, the actual
floor-defined length, factorial weight and product phase

$$
\exp(-3\log n/2)\frac{(\log n)^N}{N!}\exp(-i\Im\rho\log n).
$$

Let (V_N^{\mathrm{mid}}) contain precisely the original wing orders still
unpaid. `unpaidOrders_support` proves

$$
k\le\lfloor13N/32\rfloor,\qquad 5(N+1-k)<4N.
$$

Define the actual joint remainder and separately retained reserve by

$$
R_j^{\mathrm{win}}=u^{N_j+1}
 (F_{N_j}^{\mathrm{win}}+V_{N_j}^{\mathrm{mid}}),\qquad
Q_j=u^{N_j+1}V_{N_j}^{+}.
$$

The compiled theorem `tendsto_remainder_add_reserve` proves

$$
R_j^{\mathrm{win}}+Q_j\longrightarrow-m+m^2c(u),\qquad
\Re Q_j\ge15m^2/544\quad\text{eventually}.
$$

The second assertion is `eventually_re_reserve_ge` composed with the same
cofinal schedule. This was the earlier coarse reserve estimate; the exact
limit at the top of this ledger now strengthens it. No assertion that the
joint remainder vanishes follows.

For a **simple exposed zero**, the earlier sufficient floor on arbitrarily
large orders was:

$$
\Re R_j^{\mathrm{win}}\ge-\eta(u),\qquad
\eta(u)<1-c(u)+15/544.
$$

`false_of_remainder_floor` checks this implication with the floor as an
explicit **open premise**. No such independent floor, zero exclusion or
new zero-free region is proved in this slice. The constants and starting
orders in the geometric estimates are not numerically evaluated.

Throughout the full original interval, `tendsto_annularRemainder` also keeps
the wider (25N/16<\log n\le5N/2) count window coupled to the **entire**
tapered wing and retains the exact source. The smaller interval used by the
new wing estimates does not replace the full goal.

Next work should bound these surviving signed terms together. A new lemma
must evaluate a contribution, reduce this unpaid budget, or discharge a
necessary hypothesis of the restricted contradiction.
