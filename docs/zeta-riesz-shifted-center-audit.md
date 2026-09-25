# Per-leg shifted-center cancellation: proved spectral gate, open packet gate

This local slice continues `316a00c0f8ec413d8a9727d3f9ae9b198a7d1ced`.
Every earlier positive theorem, literal packet/rest ledger and negative audit
is preserved. **No broad arithmetic packet decay or independent floor is
claimed.** The per-leg operator passes its exact spectral and relative
arithmetic tests. The proposed source-normalized removal of exceptional
factorial allocations does not follow from multinomial concentration; the
rate obstruction below persists after summing all the other allocations.

## Complete ordinary-prime theorem

In [ZetaRieszShiftedCenter](../RiemannGaussian/ZetaRieszShiftedCenter.lean),
put $s_0=3/2+i\gamma$, $c=s_0-1$, and $C=s_0/c$.
`height_gt_fiftyFour` uses the existing low-height zero theorem to derive

$$
54<|\gamma|,\qquad |C|<1001/1000.
$$

`leg_eq_multiplier` proves, pointwise for every positive integer p,

$$
\widetilde W_k(p)
=\left(1-\frac{C^k}{p}\right)k u^k K_k(s_0,p).
$$

`finiteLeg_eq_sum`, `hasSum_completeLeg` and `completeLeg_succ` retain
the factorial convention and ordinary-prime support exactly.
`hasSum_fullGenerating` proves the full von Mangoldt generating series on
an initial regular disk. `pole_cancellation` gives exactly

$$
\frac{u}{c-ut}-\frac{uC}{s_0-uCt}=0.
$$

`global_decomposition` and `analyticOnNhd_regularGenerating` give

$$
\widetilde G(t)=-u\,\frac{\xi'}{\xi}(s_0-ut)+E_\rho(t),
\qquad E_\rho\text{ analytic on }|t|\le2.
$$

The equality is stated away from the original divisor and pole; the
regular correction itself is analytic on the whole stated disk.
`regular_coefficient_bound` uses radius 3/2 to bound its coefficients by

$$
M_\rho(2/3)^n.
$$

[ZetaRieszShiftedZeroModes](../RiemannGaussian/ZetaRieszShiftedZeroModes.lean)
justifies the infinite coefficient extraction. The actual inverse-square
zero sum supplies a uniform majorant on a neighborhood of the safe center.
Locally uniform convergence then permits every iterated derivative.
`hasSum_negative_global_coefficient` retains **all** actual zeros and
their analytic multiplicities, with negative sign and no reflected modes.

Finally
[`completeLeg_global_error_bound`](../RiemannGaussian/ZetaRieszShiftedPrimePowers.lean)
proves, for $k\ge2$,

$$
\left|\widetilde W_k^{\rm complete}
+\sum_{\tau}m_\tau\left(\frac{u}{s_0-\tau}\right)^k\right|
\le M_\rho(3/4)^{k-1}.
$$

Both proper-prime-power terms, including the shifted $C^k$ term, have
independent geometric bounds. The expansion needs neither exposure,
simplicity, nor a global rightmost zero. `selected_zero_mode` proves that
the selected zero still contributes exactly $-m_\rho$.

This is a complete-leg theorem. It does **not** assert transfer through a
hard share mask.

## Exact relative arithmetic bridge

[ZetaRieszShiftedAllocation](../RiemannGaussian/ZetaRieszShiftedAllocation.lean)
proves that the adaptive upper restriction implies $k\le4\log p$.
Consequently

$$
\left|C^k/p\right|\le p^{-99/100}
\le (N+1)^{-15}\quad\text{when }p>(N+1)^{16}.
$$

`arithmetic_product_identity` retains the literal product of prime legs.
`product_multiplier_error_linear` and
`tendsto_product_multiplier_error_envelope` give

$$
\left|\prod_p(1-C^{k_p}/p)-1\right|
\le \exp\!\left(\frac{3}{(N+1)^{14}}\right)-1\longrightarrow0
$$

when the factor count is at most $3(N+1)$. This proves **relative**
pointwise closeness. Multiplying this envelope by an exponentially growing
absolute source majorant does not give a small packet error.

## Finite negative modes and the moving support process

[ZetaRieszNegativeModeCascade](../RiemannGaussian/ZetaRieszNegativeModeCascade.lean)
proves the convergent count exponential and its finite product algebra:

$$
\frac{1-\prod_j (w-\xi_j)/(w+z-\xi_j)}{z^2}.
$$

Repeated indices encode multiplicity. The two- and three-mode expansions
and the exact adjoining-mode recurrence are checked. All their w
denominators have the shifted form $w+z-\xi_j$.
The two-mode expansion includes a term without $1/z$; the three-mode
expansion includes a term proportional to z. These represent diagonal
delta/derivative channels in the usual distributional inversion. They
must not be silently dropped when identifying a real-space inverse.
The count algebra is proved; the general complex-mode integral
identification and the full boundary-aware inverse support theorem remain
separate obligations. No below-diagonal counterexample is claimed.

[ZetaRieszMovingInsertion](../RiemannGaussian/ZetaRieszMovingInsertion.lean)
extends the compensated jump tilt to any nonnegative tilt. With

$$
r_N=\frac{320}{39}\frac{\log(N+1)}N,
$$

`movingInsertion_exp_bound` proves $0\le S_N\le e^{-N/100}$ for

$$
N\ge100000,\qquad g\ge7/25.
$$

Here $S_N$ is the **already-defined supported jump process in rescaled
coordinates**, with a positive auxiliary lower cutoff retained. It is not
an identification with the positive-cutoff multimode inverse or with a
literal arithmetic packet. The infinite-zero and boundary identifications
remain unpaid.

## Quantified obstruction to discarding adaptive bad allocations by norm

[ZetaRieszAdaptiveRateAudit](../RiemannGaussian/ZetaRieszAdaptiveRateAudit.lean)
proves `zero_order_full_marginal`: summing every allocation of all the
other prime legs gives exactly

$$
\Pr(d_p=0)=(1-x_p)^N.
$$

This is the **entire binomial marginal**, not one isolated allocation atom.
It is contained in the proposed $d_p<2$ exceptional event. For the
explicit logarithmic share $x_N=16\log(N+1)/(N+1)$, Lean proves

$$
\Pr(d_p=0)\ge(N+1)^{-32}
$$

eventually. More generally, `shrinking_share_source_mass_tendsto` proves
for **any** $x_N\to0$ and every fixed $u>1/2$,

$$
(2u)^N(1-x_N)^N\longrightarrow+\infty.
$$

Thus changing the fixed polynomial exponent 16 cannot make the summed
exceptional mass beat the worst absolute source growth. The issue is not
limited to a polynomial threshold: every shrinking-share schedule has
zero-order marginal with this rate obstruction. This theorem is about
factorial weights and an absolute source envelope; it **does not prove
divergence of the signed arithmetic carrier**, nor that the hypothetical
zero exists. A signed estimate could still control the exceptional part.

The next arithmetic obligation is therefore a coupled signed estimate for
the low-order allocations and for the exact multiplier error, or an
independent bound for their actual weighted total variation that is
stronger than the generic source envelope. Discarding them first with a
polynomial Chernoff/union bound is not sufficient. The useful per-leg
operator is preserved; the broad packet is not introduced before those
errors are paid. The old fixed least-share packet is not reopened.

## Optional quantitative reproduction

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_shifted_center.py \
  --output docs/riesz-shifted-center-probe.json
```

The [recorded report](riesz-shifted-center-probe.json) checks the finite
count algebra and scans N=256 through $10^7$. At $10^7$, the logarithm
of the source-scaled supported-tail envelope is about -240088, whereas the
source-scaled exact binomial $d<2$ marginal has logarithm about +878.
These are different model quantities, not measurements of a signed
arithmetic packet. The probe is optional and is not added to routine CI.

No new packet/rest ledger, arithmetic floor, restricted zero exclusion,
or RH claim is made. The existing public source frontier stays unchanged.
