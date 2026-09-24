# Pole-jet filtering, half-plane modes, and the rightward-chain test

This continues the local tree after the radial masked-mode audit. All
previous parity identities, negative audits, independently paid errors,
and the exact unfiltered packet/rest ledger are preserved.

**The proposed conditional literal packet theorem has not passed.** The
zero-mode half-plane geometry works, including a genuine masked two-node
decay theorem. The missing bridge is earlier than a higher-dimensional
divided-difference estimate: the existing polynomial Riesz kernel filters
the **total moment**, not each prime leg. Its pole root therefore does not
annihilate a mixed pole/zero denominator. Lean now checks this distinction
for the repository's actual filter. Separately, the proposed extension of
the rightward-chain estimate fails for several rightward modes; an exact
family of counterexamples is proved below.

Neither a counterexample consisting of actual zeta zeros nor divergence
of the literal filtered packet is asserted. The conditional small-packet
statement remains unproved, rather than refuted as a statement about zeta.
No RH or zero-free frontier is advanced.

## What works: actual zero modes in a half-plane

In [`ZetaRieszHalfPlaneModes.lean`](../RiemannGaussian/ZetaRieszHalfPlaneModes.lean),
`Rightmost rho` explicitly means that every nontrivial zero has real part
at most that of `rho`. No maximizing zero is inferred from RH failure.
At the selected ordinate,

\[
u=\frac32-\Re\rho,\qquad
z_\tau=\frac32+i\Im\rho-\tau.
\]

`direct_re_ge_of_rightmost` proves `Re(z_tau)>=u` and `direct_self` gives
`z_rho=u`. `local_support_actual_zero` identifies each point in the
canonical finite divisor with an actual `NontrivialZetaZero`, so the
geometry applies to the actual local support as well.

For an admissible reflected mode,

\[
z^*=\frac{R^2}{\overline z},\qquad
\Re z^*=\frac{R^2\Re z}{|z|^2}>\Re z
\quad (\Re z>0,\ |z|<R).
\]

This is `reflected_re_gt`, with the interior-circle hypothesis retained.
`convex_re_ge` and `convex_norm_ge` prove for every finite mode family

\[
q_j\ge0,\quad \sum_jq_j=1,\quad\Re z_j\ge u
\quad\Longrightarrow\quad
\Re\sum_jq_jz_j\ge u,\quad
\left|\sum_jq_jz_j\right|\ge u.
\]

For `0<=a<=b<=1` and distinct nodes, `twoBand_eq` proves the exact
antiderivative before taking a norm:

\[
B_N=\int_a^b\left(\frac{u}{qz_1+(1-q)z_2}\right)^{N+2}dq
=\frac{u}{(z_1-z_2)(N+1)}
\left[
 \left(\frac{u}{az_1+(1-a)z_2}\right)^{N+1}
-\left(\frac{u}{bz_1+(1-b)z_2}\right)^{N+1}
\right].
\]

Under the half-plane hypotheses, `twoBand_bound` and `twoBand_tendsto`
give

\[
|B_N|\le\frac{2u}{|z_1-z_2|(N+1)},\qquad B_N\longrightarrow0.
\]

`twoBand_coincident` supplies the exact confluent value
`(b-a)*(u/z)^(N+2)`. In this half-plane a repeated node other than `u`
has strictly larger norm, hence geometric decay
(`twoBand_coincident_tendsto`). The repeated selected node has the
constant value `b-a`. This is a masked integral theorem, not an inference
from separate complete-leg limits.

These results do not yet estimate the Riesz-weighted, finite-order,
all-count packet. Higher-dimensional Hermite--Genocchi infrastructure
was not built after the filter bridge failed. In particular, the
two-node estimate is not silently applied to an N-dependent Riesz weight
without a variation estimate.

## The exact literal filtered packet and the failed bridge

[`ZetaRieszFilteredMaskAudit.lean`](../RiemannGaussian/ZetaRieszFilteredMaskAudit.lean)
defines `filteredFullParityPacket P u y N K` by retaining every original
support, allocation, `rectangleMass`, moving-length and phase factor,
and replacing just `zetaPrimeLogKernel N` by `zetaPrimeFilterKernel P N`.
`poleJetFilteredFullParityPacket` specializes it to the existing
`zetaRightHalfPoleJetFilter`.

`filterKernel_eq_total_shift` and
`filteredPacket_eq_frozen_total_filter` prove the literal bridge:

\[
\mathrm{filteredPacket}_{P,N}
=\sum_k P_k\sum_n W_N(n)\,K_{N+k}(n).
\]

Here **every mask in `W_N` still uses N**, including `L_N`. This is not
a sum of whole packets with their masks recomputed at `N+k`. Nor is it
a product of filters on individual prime variables.

For a mixed geometric mode with denominator `w=sum q_j*z_j`, the exact
repository sequence-filter identity is

\[
\sum_kP_k w^{-(N+k+1)}=w^{-(N+1)}P(1/w).
\]

It gives `P(1/w)`, not `product P(1/z_j)`. This is
`total_filter_mixed_mode`. Replacing the former by the latter would
change the arithmetic kernel, and the difference has no paid error
estimate or source identity in this pass.

The actual pole-jet filter already contains the local zero-isolating
Lagrange polynomial. Its roots annihilate the individual direct local
zero modes and the pole, with the pole root promoted to order two.
The new theorem `poleJetFilter_eval_inner_ne_zero` proves, for the exact
repository filter and under `Rightmost rho`,

\[
\frac12<a<u\quad\Longrightarrow\quad P(1/a)\ne0.
\]

The result is stronger under disk exposure:
`poleJetFilter_eval_exposed_inner_ne_zero` proves

\[
\Re w>\frac12,\quad |w|<u
\quad\Longrightarrow\quad P(1/w)\ne0.
\]

The proof uses the actual local divisor and the exact Lagrange product.
An inner denominator cannot coincide with a root coming from an actual
competing local zero, since disk exposure excludes that zero. Its real
part also prevents coincidence with the pole. No coefficient search,
numerical polynomial root test, or hypothetical disappearance of the
analytic residual is used.

Thus the exact zero isolator does not fix this bridge either. It kills
individual competing modes on complete moments, while any intruding
mixed denominator inside the exposed disk is specifically **not** a root.

## The pole keeps its imaginary coordinate

At the evaluation ordinate `y=Im rho`, the actual pole denominator is

\[
c=\frac12+iy,
\]

not the real number `1/2`. The proposed real mixed denominator is
obtained if a same-real-part zero `tau` has the compensating ordinate

\[
\Im\tau=\frac{y}{1-q},\qquad
z_\tau=u-i\frac{q}{1-q}y.
\]

`pole_same_real_mix` proves exactly

\[
qc+(1-q)z_\tau=\frac q2+(1-q)u\in(1/2,u).
\]

For `q=43/80`, `u=10001/20000`, `pole_mix_radius_exact` gives
`800037/1600000 = 0.500023125`. `pole_mix_growth_bounds` proves its
logarithmic growth rate lies between `1/19000` and `1/18000`; numerically
the rate is about `5.37460698e-5`.

The actual-zero theorem `pole_same_real_resonance_not_killed` retains
both the existence of `tau` and the compensating ordinate equation as
hypotheses. It proves resonance and nonzero evaluation of the **actual**
pole-jet filter at that mixed denominator. The second zero is not
constructed or asserted to exist. At nonzero height it is not the
selected zero itself. At large height it can lie outside the canonical
local disk, which is precisely why finite local zero-mode control is not
the whole task.

`total_filter_ne_legwise_on_pole_mix` states the failed algebraic bridge
directly: `P(1/w)` is nonzero while `P(1/c)*P(1/z_tau)` is zero. Even under
the temporary rightmost hypothesis, changing the total kernel to the
existing pole-jet kernel therefore does not license deleting every
pole-containing assignment from the masked prime-factor expansion.

This is a structural obstruction to that inference, not an assertion
that the actual all-count Riesz response fails to cancel such terms.
Proving that cancellation would be new joint arithmetic/analytic work.

## The rightward-mode test

`resonance_forces_rightward` applies to arbitrary finite families of
actual direct and admissible reflected zero modes. An inner mixed
denominator forces at least one participating zero farther right.
`resonance_depth_forces_rightward` quantifies the horizontal conclusion:
a resonance of depth greater than `epsilon` forces a zero with real-part
gain greater than `epsilon`. This does not control its ordinate.

For one actual competing zero mixed with the selected zero,
[`ZetaRieszRightwardModeAudit.selected_successor_gain`](../RiemannGaussian/ZetaRieszRightwardModeAudit.lean)
proves the sharper relation

\[
q\bigl((\Delta\gamma)^2+(\Delta\beta)^2\bigr)
 <2u\Delta\beta,
\qquad \Delta\beta>0.
\]

For several rightward modes the analogous displacement estimate is
false. For any `0<delta<=1/40000`, take

\[
z_1=u-\delta+i/10,\qquad
z_2=u-\delta-43i/370,\qquad q=43/80.
\]

`gain_geometry` checks

\[
u<|z_1|,|z_2|<3/4,\qquad
qz_1+(1-q)z_2=u-\delta<u.
\]

The two heights do not approach the selected height as `delta` shrinks.
`gain_dispersion` proves their weighted mean ordinate is zero while
their weighted squared dispersion is exactly `43/3700`.
`no_uniform_successor_bound` proves that, for every `C>=0`, such a
resonance can be chosen with **both** squared ordinate offsets greater
than `C*delta`. Thus there need not be even one successor satisfying
the estimate required by the existing inverse-square chain argument.
These are synthetic denominator coordinates, not actual zeta zeros.

The [numerical probe](../scripts/probe_riesz_rightward_modes.py) checks
two, three and four modal families, with gains from `1e-5` down to
`1e-11`. Their modal shares can be realized by five positive prime-log
shares in the original largest/least-share box. No actual prime labels
with those exact logarithms are asserted. It checks every direct/reflected
choice using the actual map `R^2/conj(z)`, with `R=3/4`.

The real-part lower bound is `u-delta` for every such choice, and the
explicit balanced all-direct assignment attains it. The optimizer's
local runs agree with this lower bound; their convergence is not needed
to certify a global minimum. The algebraic lower bound and witness
already identify it in this model.

| Modes | Gain of each mode | Weighted ordinate variance / gain |
| ---: | ---: | ---: |
| 2 | `1e-5` | `1162.16` |
| 2 | `1e-11` | `1.16216e9` |
| 3 | `1e-11` | `1.27415e9` |
| 4 | `1e-11` | `1.25714e9` |

The same probe tests exact factored isolators that vanish at each
competing individual mode and equal one at the selected mode. Their
sampled values at the inner mixed denominator approach **one** as the
tested gain decreases.
The full output, including all optimizer statuses and scope warnings, is
[`riesz-rightward-modes-probe.json`](riesz-rightward-modes-probe.json).

The elementary gain-at-least-resonance-depth statement survives. What
fails is an ordinate-dispersion estimate strong enough to feed the old
no-infinite-chain theorem. Stop that chain extension unless new actual
zero correlations supply the missing information.

## Residual, finite masks, and decision

The actual `adaptiveZetaResidualMoment` still obeys the existing Cauchy
estimate at every `u<q<R`. Fixed polynomial shifts preserve decay of the
complete residual (`tendsto_adaptiveZetaResidualFilter_mul_pow`). This
is not an estimate for the hard-share projected residual. We have not
replaced the residual by an arbitrary mode or dropped it from a claimed
terminal theorem. A pole mixed with a contribution represented only by
the analytic residual is among the terms still requiring a joint bound.

Likewise, no previously paid arithmetic error has been declared paid for
a different per-prime filtered carrier. The literal new definition keeps
the old masks exactly; a fixed shift of the kernel is not a shift of the
mask. Proving rates for those errors would not repair the failed
total-filter/per-leg-filter equality, so no new concentration framework
was added after that obstruction was identified.

The pure selected-mode parity support theorem remains valid. Its proved
supported insertion tails are still distinct from the unclosed one-sided
positive-cutoff inverse identification and auxiliary-cutoff limit. Those
old obligations are not assumed away.

There is therefore no conditional `poleJetFilteredFullParityPacket`
decay/smallness theorem, no revised `fullParityRest` limit, and no
independent signed floor. The useful compiled results are the actual
half-plane geometry and masked two-node estimate, the exact filter
bridge and its obstruction, and the sharp distinction between one and
several rightward successors. The main RH and zero-free frontiers stay
unchanged.

## Local validation

The three new modules and the root library pass `lake build --wfail`
(11,180 build jobs). The root-importing verbose declaration lint and
`scripts/LintProject.lean` pass. Explicit axiom checks on the 15 audited
terminal theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The compiled status generator reports zero project axioms, zero
placeholder-dependent declarations, and no nonstandard theorem axioms.
The generated status adds supporting audit entries and updates the
module/declaration/theorem inventory; public frontier statements remain
unchanged. The generated family index includes all three modules in
arithmetic cancellation. The RH explorer exposes the compiled results in
its supporting `harmonic-pole-jet-mask-audit` view.

The optional probe records 12 explicit witnesses and 28 successful,
feasible optimizer checks. Its recorded source hash matches the script.
These are local checks; remote CI must be verified on the pushed commit.

Reproduce the optional numerical audit in an isolated probe environment:

```bash
python3 -m venv .lake/riesz-probe-venv
.lake/riesz-probe-venv/bin/python -m pip install -r scripts/requirements-riesz-probes.txt
.lake/riesz-probe-venv/bin/python scripts/probe_riesz_rightward_modes.py \
  --output docs/riesz-rightward-modes-probe.json
```

It uses `scripts/requirements-riesz-probes.txt`; ordinary builds and CI
do not invoke the probe.
