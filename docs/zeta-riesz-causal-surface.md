# Causal pole-surface subtraction: a quantitative regression bypass

**The latest analytic-factor counterexample is controlled on the moving
radial core.** Lean proves a source-normalized bound (2/3)^(N+1), and
hence <1/1000 for N>=20, for that explicitly defined toy response.
This is not a bound for the actual `FullParityPacket` or for the zeta
analytic remainder. No arithmetic floor or zero exclusion follows yet.

The proofs are in
[ZetaRieszCausalSurface](../RiemannGaussian/ZetaRieszCausalSurface.lean).
This continues the [artificial-mode audit](zeta-riesz-artificial-mode-audit.md)
after the request to keep iterating beyond its two-variable obstruction.
The earlier support failures, fixed-mode surface mismatch, Gamma-growth
audit and constant-filter masked-mode counterexamples all remain valid.

## Match the whole pole surface with a cutoff operator

The finite artificial-mode proposal successfully cancels the normalized
slice at w=1, but cannot match the toy trace 1/(w+1) along w+z=0 with a
polynomial in w. Instead substitute w=-z in that trace. The resulting
multiplier is 1/(1-z), which depends only on the cutoff transform variable.

`cutoffRay_laplace` proves that convolution on the positive cutoff ray
with exp(b t) gives the multiplier 1/(z-b), on Re z>Re b.
`cutoffRay_vanishes` proves that this operation preserves the triangular
cone. Taking its negative at b=1 gives precisely 1/(1-z). This is a
causal cutoff operator, not a mode location that secretly depends on w.

The full toy transform has the exact decomposition

$$
\frac1{z(w+z)(w+1)}
=\frac1{(1-z)z(w+z)}
 +\frac1{z(w+1)(z-1)}.
$$

`causal_response_split` proves this identity. The first term contains the
whole selected-pole trace. The second has no selected diagonal pole.
All signs and the empty-cofactor boundary remain.

More generally, `surface_subtraction_removable` proves that subtracting
H(-z,z) from H(w,z) cancels the normal simple pole for every fixed z:

$$
\frac{w\,[H(w,z)-H(-z,z)]}{w+z}
$$

has an analytic extension at w=-z whenever H is analytic there in w.
This is a parameterized local removal theorem. It does **not** assert that
an arbitrary H(-z,z) has a causal inverse with useful growth bounds.

## A quantitative estimate replaces exact support

The old ordinary inverse is

$$
K(s,d)=e^{-s}\bigl(e^{\min(s,d)}-1\bigr),\qquad s,d>0.
$$

`kernel_split` proves the exact decomposition into a supported term and
an ordinary remainder:

$$
K(s,d)
=\mathbf1_{d\ge s}(1-e^{d-s})
 +e^{-s}(e^d-1).
$$

`remainderKernel_transform` identifies the second term's double Laplace
transform exactly as 1/[z(w+1)(z-1)], on w>0,z>1. For 0<=d<s,
`leakageKernel_core_bound` proves

$$
|K(s,d)|\le e^{-(s-d)}.
$$

Thus the support failure remains true, but its size on a growing strict
core can be exponentially small. Neither a nonzero inverse at fixed s,d
nor a persistent specialized Taylor coefficient alone proves failure of
a source-normalized radial bound.

## Source-matched moving radial regression

The original unscaled `maskedToy` remains available, with bound
(2/3)^(N+1). To match the earlier A(t)=1/(2-t) counterexample at the
carrier's physical center w=1/2, both its scale and its selected-mode
location must be adjusted. Put delta=1/2-u. `sourceFactor_path` proves
exactly, at w=1/2 and z=-ut,

$$
\frac{w-\delta}{w+z-\delta}
\frac{w+z-\delta+u}{w-\delta+u}
=\frac{1-t/2}{1-t}.
$$

`sourceFactor_response` and `sourceFactor_split` prove the full
**two-variable** response and its cutoff-only causal subtraction:

$$
\frac{u}{z(w+z-\delta)(w-\delta+u)}
=\frac{u}{(u-z)z(w+z-\delta)}
 +\frac{u}{z(w-\delta+u)(z-u)}.
$$

The ordinary inverse is

$$
K_u(s,d)=e^{\delta s}K(us,ud).
$$

`sourceKernel_transform` identifies its double Laplace transform by two
actual changes of variables. On the core 0<=d<s it is precisely

$$
K_u(s,d)=e^{\delta s}\bigl(e^{-u(s-d)}-e^{-us}\bigr).
$$

`sourceMaskedToy` uses the same floor-defined length as the repository:

$$
L_N=2\log\!\left(\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor+2\right).
$$

It retains 39N/20<T<=203N/100, largest share 43/80<=p<=9/16,
the one-sided condition d=L_N-pT>=0, and exp(-iyT). Its cofactor
coordinate is s=(1-p)T, so exactly s-d=T-L_N>7T/25.
`sourceMaskedToy_core_bound` proves its norm is at most exp(-7T/50),
using delta<=0 and u>=1/2. There is no substitution T=2N.
Measurability and genuine Bochner integrability are proved separately.

`radial_integral` evaluates the factorial Gamma majorant.
`sourceMaskedToy_radial_decay` proves, for N>=2 and
1/2<=u<=10001/20000, uniformly in real y and p,

$$
\left|u^{N+1}\int_0^\infty
 \frac{e^{-T/2}T^N}{N!}\,\mathrm{sourceMaskedToy}_{N}(T)\,dT\right|
\le\left(\frac{u}{1/2+7/50}\right)^{N+1}
\le\left(\frac45\right)^{N+1}.
$$

The first inequality is the generic `radial_bound`; the named masked
endpoint uses the final rational bound. `sourceMaskedToy_radial_small`
gives <1/1000 for N>=32. This is a bound on the complete regression response
after the signed count subtraction, not a legwise absolute phase estimate.

These are regression-model results. Neither toy is the finite-prime packet.
No transfer of squarefree labels, factorial allocations, physical prime
cutoffs, least-share masks or the actual zeta remainder is asserted.

## A quantitative directional target

For a complex displaced analytic mode b, the exact below-diagonal model is

$$
K_{u,b}(s,d)=e^{\delta s}\bigl(e^{-b(s-d)}-e^{-bs}\bigr).
$$

`sourceKernel_eq_displaced` checks the original case b=u.
`displacedKernel_bound` proves, for u>=1/2, s,d>=0 and Re b>=0,

$$
|K_{u,b}(s,d)|\le2e^{-\Re b(s-d)}.
$$

`displacedKernel_core_bound` specializes Re b>=1/1000 to the joint envelope
2 exp(-7T/25000). More generally, `directional_radial_bound` proves that
**any exact joint response** f with norm at most M exp(-7T/25000), M>0,
has normalized radial integral at most

$$
M\left(\frac{9999}{10000}\right)^{N+1}.
$$

Thus this very small physical-gap saving suffices. The required radial
rate only needs to exceed u-1/2, at most 1/20000 on the restricted range.
A local coefficient radius alone does not imply such a directional bound.
No theorem here supplies this premise for the actual zeta response. Its
genuine integrability and exact arithmetic identification must also be proved.

## Numerical checks and a directional failure

The optional probe uses exact integer arithmetic for the floor, both
rational radii, and N=64,256,640,1536,4096,8192, with p=11/20. Incomplete
Gamma integration retains both exponential terms, the full radial interval,
and the changing L_N:

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_causal_surface.py \
  --output docs/riesz-causal-surface-probe.json
```

At u=10001/20000,N=8192, the **source-matched** normalized response has
base-10 logarithm about -1010.40. The earlier unscaled comparison has
logarithm about -2017.48. The distinction is kept in the JSON output.
The probe takes y=0; the compiled bounds permit every real y.

The same experiment also tests the exact complex-mode inverse model
above. Its analytic leg is u/(u+b-ut), so the normalized pole radius is
|u+b|/u. For b=-1/20+3i/5 that radius is about 1.49991, greater than 4/3,
but the source-normalized radial response grows:

| N | log10 of normalized norm |
|---:|---:|
| 256 | 3.6211 |
| 640 | 11.1156 |
| 1536 | 28.7090 |
| 4096 | 79.2103 |
| 8192 | 160.2081 |

The one-sided boundary term e^{(delta-b)s} dominates this model; it is
retained, not dropped. Its upper-radial-endpoint exponent is positive.
A smaller negative real part, b=-1/100+3i/5, initially decreases and then
grows, making a short finite-N experiment misleading. These are numerical
stress tests, with 90/130-digit cross-checks, not Lean growth theorems or
identified modes of the actual zeta remainder. Fixed-height checks at
y=55 and y=1000 also grow: at N=8192 their normalized logarithms are
157.90 and 156.64. Oscillation reduces these finite values but does not
suppress the observed exponential mechanism. They show why the successful
real-mode regression cannot justify a generic analytic-remainder claim.

## A genuine conjugate-mode obstruction to the directional shortcut

The directional condition cannot simply be assigned to each actual shifted
mode. In physical radial coordinates, a zero tau in the shifted-center
term has mode

$$
\xi_\tau=\frac12-\frac{s_0+1-\tau}{C}
=\frac{(\tau-1)(s_0-1)}{s_0}-i\gamma.
$$

`shiftedMode_eq` proves the exact formula. For the genuine conjugate of
the selected zero, `shiftedMode_conjugate_re` proves

$$
\Re\xi_{\bar\rho}=
\frac{(\beta-1)(\gamma^2+3/4)+\gamma^2}{\gamma^2+9/4}.
$$

Using the repository's proved |gamma|>54 and beta>=19999/20000,
`shiftedMode_conjugate_re_gt` proves **Re xi>99/100**. This is in the
adverse direction. `shifted_conjugate_displacement_neg` proves the b
needed by the directional kernel estimate is less than -99/100.

At the same time, `shiftedPole_conjugate_outside` proves its normalized
Taylor location has norm greater than 2, entirely consistent with the
existing complete-leg analyticity theorem. `shiftedPole_substitution`
identifies the zero at the shifted center exactly, while
`shiftedPole_original_re_gt` proves the original center at that location
has real part >199/100. Thus it is not a competing original zero or the
zeta pole. These are geometry theorems conditional on an actual selected
zero; they do not construct such a zero.

The probe also keeps **both original negative modes and both positive
shifted copies** in the same rational count factor. For synthetic
beta=19999/20000,gamma=55, the positive modes have real parts about
-0.99931 and +0.99921. Their Taylor pole moduli are outside the working
disk. Keeping all four modes, the full moving-window normalized inverse
has log10 norm about 97.88 at N=256 and 3243.03 at N=8192. The growing
term is the retained cutoff-boundary residue of the positive shifted
conjugate mode. This is an explicit finite-mode numerical test, not a
full zeta-divisor inverse or an asserted zero at those coordinates.

Consequently the new atomwise directional shortcut cannot control the
actual shifted correction. A successful transfer would have to prove
cancellation in the **combined** remainder/shifted configurations before
inversion and masking. The geometry alone does not rule out that
cancellation, and the finite-mode experiment must not be promoted to a
growth theorem for the complete arithmetic packet.

## Real-contraction redesign: pair success does not survive the stress test

A short follow-up tested the real scale C=1/2 and center 1+C(s0-1).
Its shifted actual-style modes have Re xi=2(Re tau-1)<0, removing the
complex-scale conjugate displacement. The selected/conjugate pair alone
looks favorable. No contracted arithmetic packet or new framework was built.

The optional [contracted-mode probe](../scripts/probe_riesz_contracted_modes.py)
then adds two rightward pairs, with real part 99999/100000 and positive
heights 10 gamma and (119/40) gamma. Both heights exceed the selected
height. It tests the pairs and the full twelve-zero collection obtained
by conjugation and reflection tau -> 1-tau, retaining the corresponding
positive shifted copies. It includes the selected largest-prime source,
the moving radial interval, all finite-mode count terms and the cutoff-zero
residues. It tests both the common modal clock and the unscaled cutoff
relative to the contracted clock; neither is asserted to be a literal
prime-packet transfer.

The dangerous mixed term has an **exactly zero radial frequency**:

$$
2(119\gamma/40)-\gamma-(11/20)(10\gamma-\gamma)=0.
$$

`contraction_model_phase_exact` proves this identity. Its real radial rate,
including the selected largest leg, is 250021/500000 by
`contraction_model_rate`. The moving-length contribution then gives the
exponent

$$
\log(10001/20000)-\log(250021/500000)
 -\frac{\log(10001/20000)}{50000}>\frac1{40000},
$$

proved by `contraction_model_exponent_pos`. This is an exact sign check of
the model exponent, not a theorem of growth for the full arithmetic packet.

The three-pair common-clock model initially looks small, but its normalized
norm rises from about 0.43 at N=16384 to about 1.93 at N=65536 and 682.6
at N=262144. Including all reflected partners does not repair the numerical
model. The full-quartet, unscaled-cutoff model has normalized log10 norm
about 7.73 at N=262144. The extra rightward pairs respect the proposed
minimum-height selection of the original near-edge zero; minimum height
alone therefore does not exclude this configuration.

The probe uses 75/110-digit arithmetic. It replaces the floor length by
2 log(u^(-N)/(N+1)) with the explicitly recorded error upper bound
4(N+1)u^N. Numerically negligible terms are removed only after retaining
an absolute envelope for their **total numerical truncation error**; this
is not an arithmetic triangle-inequality proof for the carrier. These
experiments use synthetic zeros and are optional, outside CI:

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_contracted_modes.py \
  --output docs/riesz-contracted-mode-probe.json
```

This failed stress test stops the proposed minimum-height/real-contraction
shortcut before a large Lean construction. It preserves the existing
multi-rightward audit: several modes can satisfy a phase relation that
single-pair estimates miss. A usable advance still needs information in
the literal arithmetic coefficients or a proved cancellation among the
entire original/shifted configurations.

## The next actual transfer

The finite genuine divisor and the combined analytic remainder from
`ZetaRieszLocalXiDivisor` remain the starting point. The next obligation is a joint cancellation estimate retaining the actual
shifted conjugate channel. Neither local Cauchy estimates nor the new
atomwise directional estimate pay it. Any causal trace construction must
prove its growth bounds for the complete combined response before using
the physical core and radial integration. Local Cauchy bounds alone
have not discharged those obligations.

No infinite-zero inverse, moving-prime-cutoff identification, arithmetic
multiplier estimate, new broad packet or rest floor is claimed. This
source-matched regression and directional threshold supply a different
joint mechanism to test on the actual remainder; it does not erase the earlier negative audits.

The subsequent [joint cancellation pass](zeta-riesz-joint-cancellation.md)
retains the exact two cutoff clocks, pays the finite multiplier correction
on the existing fixed-share packet, and proves geometric cancellation
across an internal share seam in a modal integral. Its literal weighted
transfer and the remaining arithmetic floor are still open.
