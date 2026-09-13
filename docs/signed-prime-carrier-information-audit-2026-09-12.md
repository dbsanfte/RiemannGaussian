# Information and correlations in the signed prime carrier

This is a source-level audit of the live carrier and its connections to
the divisor filters, squarefree matrices, Gaussian phase bounds, prime
Gram matrices, reflected zeros and Suzuki discrepancy. It identifies
which information the compiled identities retain and where downstream
estimates stop using it. It does not prove the independent arithmetic
lower bound or claim an exhaustive classification of all zeta identities.

## 1. The exact target and quantifiers

Fix a hypothetical nontrivial zero `rho=beta+i*gamma`, with `beta>1/2`.
Put `u=3/2-beta` and let `p` be its original normalized pole-jet filter.
The following quantities retain every complex polynomial coefficient:

```math
F_{p,N}(t)=\sum_k p_k\frac{t^{N+k}}{(N+k)!},\qquad
K_{p,N}(s,x)=x^{-s}F_{p,N}(\log x),\qquad s=3/2+i\gamma.
```

On `A_N=exp(N*log(2)/4)` to `B_N=2^(32*N)`, the centered carrier is

```math
J_N=\int_{A_N}^{B_N}K'_{p,N}(s,x)(x-\theta(x))\,dx,\qquad
C_N=u^{N+1}J_N.
```

These are genuine finite integrals, with integrability proved in
[ZetaPrimeBandChebyshev](../RiemannGaussian/ZetaPrimeBandChebyshev.lean).
For the right boundary layer covered by the
[complete filter-cost theorem](zeta-zero-filter-cost.md),
`actual_centered_source_limit` proves `C_N -> -1`; simplicity is discharged
there. Outside that layer the earlier zero-mode filter gives the same
centered reduction with source `-m_rho`. Do not extend the new quantitative
pole-jet coefficient bound to the whole remaining strip.

The sufficient independent estimate for the simple source is

```math
\exists\varepsilon>0\quad\forall N_0\quad\exists N\ge N_0:
\Re C_N\ge-1+\varepsilon.
```

The margin and the selected orders may depend on the fixed zero. A common
margin over all heights, a bound at every order, and full norm decay are
stronger than necessary. A finite-order bound strictly above minus one
without a fixed positive margin is insufficient.

## 2. What the carrier actually contains

Set `E(t)=1-exp(-t)*theta(exp(t))`. Using the compiled kernel derivative
recurrence and the ordinary logarithmic substitution gives the explanatory
coordinate form

```math
\Re C_{N+1}=u^{N+2}\int_{\log A_{N+1}}^{\log B_{N+1}}
 e^{-t/2}E(t)\left(\Re D_N(t)\cos(\gamma t)
                 +\Im D_N(t)\sin(\gamma t)\right)dt,
\qquad D_N=F_{p,N}-sF_{p,N+1}.
```

The exact real integral in the original `x` coordinate is compiled as
`zetaPrimeBandChebyshevIntegral_re_lowering`; this audit does not add a
new signed logarithmic-substitution theorem. The analogous absolute
substitution is already compiled in
[ZetaPrimeEnvelopeRate](../RiemannGaussian/ZetaPrimeEnvelopeRate.lean).

There are at least four coupled variables: logarithmic position, moment
order, detector height, and the divisor-dependent polynomial. The sine
channel carries a factor `gamma`; discarding it would change the carrier.
Adjacent orders are tied by differentiation, not independent samples.
The filter changes with the selected divisor, so height differentiation
must either freeze it locally or justify its variation explicitly.

The full function `E` still determines the prime positions and weights.
Between its prime jumps it satisfies the elementary relation `E'=1-E`;
at `t=log r`, for a prime `r`, its jump is `-log(r)/r`. More generally,

```math
E(b)=e^{a-b}E(a)+(1-e^{a-b})
     -e^{-b}\sum_{e^a<r\le e^b\atop r\ {\rm prime}}\log r.
```

These are exact consequences of the definition of `theta`, recorded here
as proposed drift-and-jump interfaces, not newly compiled declarations.
Replacing `E` by an arbitrary amplitude envelope loses that linkage.

The [integer drift/jump work module](zeta-prime-discrepancy-work.md) now
proves the exact recurrence and every complete block for `d_n=n-theta(n)`.
Its complex-weighted square identity retains the correlation with each
preceding error, every earlier prime pair, both block energies and every
test increment. The complete local forcing diagonal is independently
geometrically negligible for the full factorial kernel divided by its
integer coordinate. The quadratic signed flux remains; this does not yet
give the independent floor for the original linear carrier. The continuous
logarithmic drift formula above is still a proposed interface.

The [linear lattice carrier](zeta-prime-lattice-carrier.md) now keeps the
original source in a fully discrete signed sum with coefficients
`lambda(n)-1`, where lambda is the ordinary-prime logarithm. Its exact
first-error-increment identity inserts no quadratic factor. Both signed
sawtooth endpoints and the whole sampling integral are retained; the
independently proved sampling error is geometrically small for every fixed
filter and height. Together with the old boundary estimate, it proves the
same normalized limit `-m_rho` for the original zero-mode filter. The
independent cofinal signed lower bound remains open in this lattice form.

### Why a zero produces a resonance

As a diagnostic, insert the single complex mode

```math
E_\rho(t)=\rho^{-1}e^{-(1-\rho)t}.
```

This is a test mode, not an asserted standalone expansion of the actual
Chebyshev error. Its frequency cancels the detector's `exp(-i*gamma*t)`.
The remaining damping is exactly `exp(-u*t)`. The compiled identity
[`integral_zetaFactorialPolynomial_exp`](../RiemannGaussian/ZetaPrimeKernelLaplace.lean)
evaluates every full half-line factorial moment as
`u^(-N-1)*p(1/u)`. Consequently the two derivative terms in this diagnostic
give

```math
\frac{u^{N+2}}{\rho}
\left(u^{-N-1}-s\,u^{-N-2}\right)p(1/u)
=\frac{u-s}{\rho}=-1.
```

The final algebra uses `p(1/u)=1`. This calculation explains the source;
it is not an independent bound or a proof of a global explicit formula.
The actual source is proved instead by the local analytic divisor chain.
A proposed cancellation mechanism must constrain such a resonant component,
not merely observe that the detector oscillates rapidly.

## 3. The transport and loss ledger

| Interface | What survives exactly | What its estimate does, or leaves open |
| --- | --- | --- |
| [Local zero-mode filter](../RiemannGaussian/ZetaZeroModeFilter.lean), `zetaPrimeLogFilter_isolate_adaptive_zero` | Selected multiplicity, every other local node, residual and canonical reflected modes | The normalized analytic residual and canonical reflected modes decay. The selected source remains. Canonical disc reflection here is distinct from functional-equation reflection. |
| [Pole-jet lift](../RiemannGaussian/ZetaMoebiusPoleJetFilter.lean) | Full polynomial and selected normalization; pole value and derivative are both killed | Removes the continuous pole contribution, not the selected zero. |
| [Complete filter cost](../RiemannGaussian/ZetaZeroFilterCost.lean) | Exact physical-distance Mahler product before the coefficient estimate | The coefficient norm forgets polynomial phase, but is applied only to reduction errors. The signed carrier continues to use the original polynomial. |
| [Complete squarefree matrix](../RiemannGaussian/ZetaSquarefreeEulerFamilyDecay.lean) and [prime tail](../RiemannGaussian/ZetaSquarefreeEulerPrimeTailSource.lean) | All lcm incidences, both complex divisor families, logarithmic insertion and original cutoffs | Independent decay proves `large composite response + prime correction -> 0`. It does not bound the prime correction separately. |
| [Finite band and Abel transform](../RiemannGaussian/ZetaPrimeBandAbel.lean) | Exact prime atoms, signed density error, both endpoints and complete derivative | Density and endpoint errors are independently negligible. Centering is an exact recoding of the live arithmetic. |
| [Full derivative envelope](../RiemannGaussian/ZetaPrimeEnvelopeRate.lean), `actual_original_derivative_allowance_tendsto` | Entire derivative polynomial stays together until the norm | Replacing the signed error by a subexponential full-density majorant gives a divergent allowance. This is an actual method obstruction for every fixed normalized filter. |
| [Window and complementary tail](../RiemannGaussian/ZetaPrimeTailWindowObstruction.lean) | Both complex amplitudes and the original sieve/cutoff | Raw window norms grow; their complementary relative cancellation follows from the hypothetical source. It cannot be reused as an independent bound. |
| [Local and far pair form](../RiemannGaussian/ZetaRoughSquarefreeLocalCorrelation.lean) | All ordered mixed terms, real and imaginary parts, arithmetic weights | Local correlations decay independently; the far form retains `m_rho^2` using the source. Additive separation does not imply logarithmic-phase separation. |
| [Gaussian finite divisor and prime work](../RiemannGaussian/ZetaGaussianStripPhaseFamily.lean), `finite_source_add_mixedWork_le_exactBudget` | Finite zero group, all multiplicities and ordinate displacements; three actual prime responses | `source_le_exactBudget` replaces their nonnegative total by zero. The exact stronger inequality remains upstream. |
| [Anchored prime correlations](../RiemannGaussian/ZetaGaussianPrimeCorrelation.lean) | Exact ratio and product phases, common weights, zero-frequency anchor, cosine and sine energies | The cosine projection removes an unnecessary sine allowance from a ratio-only Schur test. The resulting actual-zero constraint is proved; its independent upper energy gap is not. |
| [Ordinary Gaussian-prime reduction](../RiemannGaussian/ZetaGaussianPrimeReduction.lean) | Exact amplitude splitting, nonconstant frequency mass, every mixed quadratic term and the full squared source | Proper powers and both auxiliary responses have a fixed summable remainder. Their complete Young allowance divided by squared dilation tends to zero at bounded nonconstant mass. Ordinary-prime energy and the signed boundary budget remain live. |
| [Clipped left boundary](../RiemannGaussian/ZetaClippedEulerFamily.lean), `totalMean_le`, `totalAllowance_le` | Actual signed means are available before the bounds | Pointwise upper growth is summarized by nonconstant mass and logarithmic frequency cost. Correlation of the actual mean with prime work is not estimated. |
| [Gaussian discrepancy](../RiemannGaussian/GaussianPrimeDiscrepancy.lean), `gaussianArithmeticExplicitFormula_nonnegative_iff_primeDiscrepancyBudget` | Endpoint, digamma gain and centered prime energy share one exact budget | Positivity of uncentered prime energy alone does not prove this signed discrepancy condition. |

No loss was found in the final real projection that would invalidate the
source: both phase channels are explicitly retained. The clearest unused
quantitative information is in the Gaussian prime work and the joint
signed boundary budget, rather than a missing endpoint or imaginary term.

## 4. Correlations worth testing together

**One prime measure behind three Gaussian responses.** Write
`P(v)=sum_n a_n*cos(omega_n*v)`, with the current eligibility assumptions.
The existing `hasSum_arithmetic` theorems in
[ZetaGaussianPhaseArithmetic](../RiemannGaussian/ZetaGaussianPhaseArithmetic.lean)
and [ZetaSechPhaseFamily](../RiemannGaussian/ZetaSechPhaseFamily.lean), and
the Euler arithmetic expansion, express the three responses with exactly
the same `P(gamma*log m)`. Their combined amplitude is

```math
W(m)=W_G(m)+\frac{24B}{\eta^2}W_E(m)+\frac{W_S(m)}{2\eta}\ge0.
```

The combined identity is now proved as `hasSum_mixedWork` in
[ZetaGaussianPrimeBlocks](../RiemannGaussian/ZetaGaussianPrimeBlocks.lean),
together with nonnegativity and summability of `W` and the exact constant
response `constantWork=sum_m W(m)`. It offers a single target for
cross-prime phase constraints, with all three responses retained.
The desired improvement is on `mixedWork-exactBudget`, or a lower bound
for `mixedWork` paired with the existing budget. Its signed boundary
component must remain available until an estimate actually uses it.

**Prime powers impose linked phase returns.** The stronger existing
`zetaPhase_weighted_returns_le` in
[ZetaPhaseWeightedRecurrence](../RiemannGaussian/ZetaPhaseWeightedRecurrence.lean)
proves, for every nonnegative summable coefficient family with a zero
frequency at index zero, every angle `theta` and every integer `H`,

```math
(H+1)\big((H+1)a_0-A\big)
\le 2\sum_{j=1}^{H}(H+1-j)P(j\theta),\qquad A=\sum_n a_n.
```

For nonnegative `P`, put
`R_H=max(0,(H+1)*((H+1)*a_0-A)/2)`. Any nonnegative coefficient `c_r`
satisfying `(H+1-j)*c_r <= W(r^j)` for `1 <= j <= H` gives the lower bound
`c_r*R_H` for that actual prime-power block. The new
`gaussian_blocks_lower` proves an explicit such minorant and adds it over
disjoint prime bases, without charging the complete sum repeatedly.
`finite_source_add_blocks_le_budget` transports this reserve to the actual
finite-zero budget. `mixedWork_pos` proves strict positivity whenever
`a_0>0`, with no numerical coefficient search.

There is now a checked scale obstruction for this whole class of
triangular minorants of initial prime-power blocks. At the current scaled
geometry, for every eligible family, every finite set of distinct primes,
every collection of block lengths and every admissible coefficient,

```math
\sum_{r\in S}c_rR_{H_r}
\le \frac{1998}{25}\operatorname{Re}\frac{-\zeta'(2)}{\zeta(2)}.
```

The coefficient bound uses the full combined `W`, not just its Gaussian
part. `tendsto_normalized_block_reserves` proves that this reserve divided
by the dilation tends to zero even when the coefficient family, prime set,
block lengths and minorants all change. The source and allowance have
scale `q`, so adding more such blocks cannot supply a leading gain.
This is a ceiling on the guaranteed minorant, **not an upper bound on
actual prime work** or on every conceivable per-prime inequality. It
does not exclude finite-height improvements. The
[prime-block proof note](zeta-gaussian-prime-blocks.md) records the exact
assumptions and constants. The next estimate needs cross-prime information,
new arithmetic beyond this recurrence, or a joint gain with the signed
boundary mean.

**Distinct primes and logarithmic ratios.** For a finite prime sum, put
`b_r=log(r)*r^(-3/2)*F_{p,N}(log r)`. Its exact squared norm has mixed terms

```math
\sum_{r,v} b_r\overline{b_v}
 e^{-i\gamma\log(r/v)}.
```

The complex coefficient phases remain inside `b_r*conj(b_v)`. A bound
based only on `|r-v|` loses multiplicative-scale information. Unique prime
factorization constrains exact logarithmic relations, but supplies no
automatic uniform separation of their phases modulo `2*pi` at growing
heights. The [prime-pair separation identity](../RiemannGaussian/ZetaPrimePairSeparation.lean)
also retains the exact subtraction of the squared log-ratio from the
squared product logarithm. Its product-only upper bound discards that
subtraction. Neither identity currently estimates the surviving far form.

The new
[anchored correlation theorem](zeta-gaussian-prime-correlation.md)
turns the Gaussian version into a quantitative test. Write `M=sum_S W`,
`c=a_0`, `A=sum_n a_n`, and

```math
Q_S=\frac12\sum_{p,q\in S}W(p)W(q)
\left[P\bigl(t\log(q/p)\bigr)+P\bigl(t\log(pq)\bigr)\right].
```

`Q_S` is exactly the convergent sum of weighted cosine squares.
The excess in the ratio-only energy is exactly the nonnegative sine
energy. Keeping product phases therefore removes an avoidable cost in
that proposed test; this is not a newly discovered omission in the
existing signed-carrier source theorem. The actual Gaussian work obeys

```math
cA M^2\le(A-c)Q_S+2cM\operatorname{mixedWork}.
```

For `c,M>0`, an independent bound
`(A-c)*Q_S <= c*(A-2*delta)*M^2` would force
`mixedWork >= delta*M`. The Lean criterion retains this upper bound as
a premise. The original finite-zero source and signed boundary budget
also satisfy the full squared constraint
`max(0,c*M+source-exactBudget)^2 <= (A-c)*(Q_S-c*M^2)`.
The terminal theorem retains this square and removes the constant phase
from the energy exactly. None of these identities proves the required
independent upper gap.

The same coordinates separate the actual Gaussian prime-pair weight:
with `U=log(pq)` and `V=log(q/p)`, the checked factor is
`(U^2-V^2)/4 * exp(-sigma*U) * exp(-B*U^2/2) * exp(-B*V^2/2)`.
This retains the arithmetic separation factor alongside both heat
directions. The
[ordinary Gaussian-prime reduction](zeta-gaussian-prime-reduction.md)
now pays for all proper powers, auxiliary responses and their mixed
quadratic terms. At the current `k=9` dilation, the remainder has a fixed
mass `C`, and for nonconstant coefficient mass `m` the actual source obeys

```math
\max\{0,a_0M_S+\mathcal S_Z-\mathcal B_{\rm exact}\}^2
\le (1+q^{-1})mQ_{\widetilde a}(P_q)+(1+q)m^2C^2.
```

Here `P_q` is the unchanged ordinary Gaussian-prime amplitude, and the
real energy keeps all prime-pair terms, including its diagonal. The
complete additive allowance divided by `q^2` tends to zero for moving
families of bounded nonconstant mass. The current class has `m<=61/100`.
This proves decay of the separated remainder cost, not an independent
upper bound on the surviving ordinary-prime energy. The source surplus
must still be positive at the chosen detector geometry.

**Mixed analytic probes.**
[ZetaPrimeGram](../RiemannGaussian/ZetaPrimeGram.lean) proves strict
positive definiteness of `-zeta'/zeta(conj(s_i)+s_j)` and retains all
off-diagonal phases, even after a finite prefix is removed. The proof
requires `Re(s_i)>1/2`, so every mixed zeta argument has real part greater
than one. Inward continuation of the entries does not by itself continue
positive definiteness. Any Schur-complement or matrix bound must pay for
its diagonal energies at the current factorial normalization and preserve
an anchor for the desired real signed projection.

**Functional equation, colour and completion.** Same-height reflection
`rho -> 1-conj(rho)` preserves multiplicity, and the repo keeps both
spectral Cauchy pieces and their Blaschke difference in
[RiemannXiSpectralReflectionPairing](../RiemannGaussian/RiemannXiSpectralReflectionPairing.lean).
The two source distances from `3/2+i*gamma` are `u` and `v=1/2+beta`.
For an off-line right zero, `u<v`; its reflected partner's mode is smaller
after normalization by `u^(N+1)`. Unequal rates are compatible with the
functional equation. An independent coercivity or comparison inequality
would be additional mathematics, not a consequence of pairing alone.
Eta current and completion identities retain this information upstream;
their quotient denominators and global arithmetic estimates still need
their own control. The old raw eta endpoint asymptotics are not an
independent counterweight to the prime source.

## 5. What enlarging the zero-free region would buy

There is a proved geometric gain: the
[all-height squarefree transport](../RiemannGaussian/ZetaSquarefreeGaussianAllHeight.lean)
gives an actual analytic radius `1+margin(y)/2` for `zeta(s)/zeta(2*s)`.
Wider valid clearance, through the same denominator-window argument,
improves the Cauchy rate for that response. Its prefactor can depend on
height; there is no existing uniform constant on all heights.

The Gaussian multiplicity and finite-group theorems additionally supplied
separation, which now controls the actual full filter product. Separation
is extra proved information, not an automatic consequence of a zero-free
edge. A new region needs a checked transport for any enlarged simplicity
or isolation layer before using the corresponding stronger filter cost.

A wider region does not on its own supply the centered signed floor.
The all-filter envelope obstruction holds for every `1/2<u<1`. In fact,
as the remaining zeros move closer to the critical line, `u` approaches
one and the independent arithmetic exponent needed to beat their source
approaches the critical exponent. There is no proved automatic iteration
from successively wider regions to RH. The useful iteration must bring
a new signed estimate or stronger coupled zero constraint at each step.

## 6. Next tests and acceptance criteria

The [squarefree Vaughan projection](zeta-squarefree-vaughan-projection.md)
now independently removes the **entire nonsquarefree finite-band sum** at
the larger cutoffs below. Its proof retains all reciprocal Euler factors,
then averages their divisor corrections; a pointwise factor bound would
have lost the needed cutoff scale. The exact coprime cross term and both
other projected prefixes have vanishing normalized allowances. The
remaining source is supported on squarefree products, retaining the
Möbius signs and physical logarithmic phase. This does not supply the
cofinal signed lower bound, nor bound the removed terms' total variation.
Do not spend a new slice merely re-proving this deletion or weakening the
cutoffs to accommodate a pointwise Euler bound.

The [Vaughan cutoff budget](zeta-vaughan-cutoff-budget.md) now removes both
complete small-factor sectors with a proved
`C*(u/(N+1)+u^(N+1))` normalized allowance,
at cutoffs `D_N=floor(u^(-N)/(N+1))`. Chebyshev prime-power density and
inverse-square-root Dirichlet weights pay the complete product cost.
The remaining finite band is exactly
`sum_(ab in band, a>D_N, b>D_N) mu(a)*kappa_(D_N)(b)*K(s0,ab)`.
Its cofactor keeps the large prime-power divisors, is nonnegative and at
most `log b`, and is additive for coprime products. The original source
and all product phases survive. This is an independently paid reduction,
not a proof of the remaining signed floor. Test correlations in this
literal coefficient; arbitrary bilinear coefficients or separate raw
interval estimates would impose stronger, unproved obligations.

The [complete ordinary-prime energy bound](zeta-gaussian-prime-energy-bound.md)
now proves an independent estimate `Q <= 4*K^2*m*L(t)^2 + 2*D*K*q*F`,
where `L(t)=log(abs(t)+26)`, `m` is nonconstant mass and `F` its first
logarithmic frequency cost. Complete prime-prefix convergence transports
the original squared source and cancels the constant channel exactly.
The normalized energy decays for moving bounded-mass, bounded-cost
families when `L(t)/q -> 0` in that first estimate. The same module proves
this ratio is at least `320000` at the current explicit-region dilation
beyond its plateau. The subsequent
[signed Poisson comparison](zeta-gaussian-prime-energy-decay.md) now
removes the limitation: the existing log-log region gives an arbitrarily
small logarithmic coefficient uniformly through the Euler boundary, and
the complete Gaussian average preserves it. Lean proves `Q/q^2 -> 0`
when absolute height diverges and `L(t)/q` is bounded. The current schedule
qualifies with upper ratio `320000+log(13)`.

The complete auxiliary allowance also decays. The actual positive squared
source surplus over the **retained signed boundary budget**, divided by
squared current dilation, tends to zero for arbitrary moving finite-zero
windows and clipping depths, with the original phase hypotheses. This
closes the energy cost at that scale. It does not prove a positive source
surplus over the signed budget or a new region.

The [signed-budget reduction](zeta-gaussian-signed-budget-reduction.md)
now bounds all non-left terms together by
`109*m+3*(m*L(t)+F)/(50000*q^2)` at the working heights. Their difference
from the original signed clipped left mean, divided by current dilation,
tends to zero. The actual source constraint reaches that mean with its
same normalized squared surplus limit. The inverse-square right multiplier
is retained before estimating its logarithmically growing completion.
The remaining mean is still clipped at arbitrary finite negative depth;
no unclipped integral limit is proved by this reduction.

The [source-support audit](zeta-gaussian-source-support.md) now proves an
additional restriction on using that limit. The nearby condition couples
both coordinates exactly, but its horizontal edge is fixed by derivative
order. At order nine, every zero with `beta<=2035/2046` has exactly zero
compensated source for every dilation and phase frequency. Across all
currently admitted orders `k>=2`, `beta<=5/7` is still outside the source.
These are detector cutoffs, not zero-free boundaries. Such a zero retains
its complete complex contribution in the far term. Moreover, every fixed
finite zero window eventually has exactly zero source as detector height
diverges, even after arbitrary scalar reweighting. The fixed-window
source-surplus limit then controls only the negative part of the left mean.

There is now a checked constructive alternative using the existing general
strip identity. For each hypothetical right-half zero, let `h=beta-1/2`
and take `sigma=1+h/4`, `eta=1/2-h/4`. The right edge stays at `3/2`; the
source retains the fixed zero and is strictly positive for every `B>0`.
`exists_fixed_zero_source_constraint` carries it into the full original
signed inequality. The arithmetic comparison remains open, and the current
order-nine height-decay results do not apply to this geometry automatically.

1. The common-measure identity, disjoint-block transport, growing-block
   test, anchored real correlation constraint and complete remainder
   reduction, an independent full-energy upper bound and normalized decay
   at the current dilation are now proved. The normalized non-left budget
   correction is also proved negligible. First exhibit a nonzero source
   for the hypothetical zero at the proposed scale. The current boundary
   geometry has the exact visibility restrictions just proved. Within a
   stated boundary-region target, attack the original signed clipped left
   mean, retaining its height, depth and common phase-family dependence.
   A contradiction needs a positive surplus over that actual mean.
   Do not re-prove the closed energy decay or silently replace the mean
   by an unclipped integral without proving the limit and integrability.
2. Test a joint deficit involving prime work and the actual left boundary
   mean, or a new arithmetic constraint beyond the weighted recurrence.
   Include every coefficient, smoothing and counting cost before calling
   it a saving. A fixed positive constant may improve a finite-height
   inequality; a leading asymptotic improvement requires a gain on the
   growing scale. An interface becomes a region improvement only when its
   surplus reaches an actual zero exclusion theorem.
3. For the global fixed-zero target, the direct centered carrier in section
   1 already retains the selected multiplicity at its limiting scale.
   Preserve the drift-and-jump identity
   across a complete signed block partition. Target only the cofinal
   real lower bound in section 1. Separate raw window norms, a sublinear
   full-density envelope, or a source-derived cancellation limit fail the
   existing tests and should not be recycled as new estimates.

The audit identifies exploitable interfaces, not a missing theorem whose
truth has already been established. The independent lower bound and RH
remain open. The filter-cost, prime-block, anchored correlation and
ordinary-prime remainder, complete-energy and current-dilation decay
theorems are verified mathematical slices. A strong enough estimate on
the retained signed left mean remains a research target. The new
large-height limit loses fixed zero windows exactly, so it does not settle
a fixed interior zero or the separate centered carrier floor. Restoring
the complex far terms is a possible alternative requiring a new estimate;
the audit alone supplies no such estimate.
