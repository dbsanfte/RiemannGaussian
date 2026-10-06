# Global Gaussian/Weil and Suzuki research

The [Riesz reduction](zeta-riesz-terminal.md) is frozen. The active research
uses the existing global Suzuki arithmetic signal and Gaussian/Weil
identities. This changes the architecture; it does not establish a new
positivity estimate or show that RH has become easier.

The first concrete arithmetic target is the literal signed signal

\[
S(t)=4e^{t/2}-\sum_{n\le e^t}
 \frac{\Lambda(n)}{\sqrt n}(t-\log n),\qquad t>0.
\]

The existing
[`riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound`](../RiemannGaussian/SuzukiLaplaceCompensator.lean)
proves RH if, for a fixed nonzero orientation `a`,

\[
\forall\epsilon>0\ \exists C_\epsilon\ge0\ \forall t>0,
\qquad aS(t)\ge-C_\epsilon e^{\epsilon t}.
\]

All Laplace convergence, continuation and arbitrary-multiplicity steps in
this conditional theorem are proved. The arithmetic estimate is **open**.
Its subexponential allowance concerns a canceled, global signed signal;
it must not be confused with the relative PNT error envelope audited as
insufficient for prime-moment non-coherence.

The adjacent
[`RiemannXiBoundaryGaussianGram`](../RiemannGaussian/RiemannXiBoundaryGaussianGram.lean)
identifies the complete reflected zero-pair heat correlation with a
Hilbert Gram norm. Its vanishing at positive heat time is equivalent to
RH, with all multiplicities and reflection pairs retained. Independent
arithmetic vanishing remains open. One-point Gaussian positivity or
automatic Gram nonnegativity does not establish it.

The next research pass should compare the actual Suzuki signal, its full
Archimedean correction and Gaussian transform before estimating their
signed difference. Probe growing cutoffs for joint mass/moment constraints
and cross-scale inequalities on actual `Lambda`, with continuous coherent
countermodels as rejection controls. Then attempt a concrete one-sided
arithmetic estimate for `S`, or an arithmetic identity controlling the
complete reflected Gaussian Gram. A conditional reformulation or finite
numerical agreement alone does not count as a new bound.

Preserve the earlier Suzuki transport/source obstructions. Do not revive
local Riesz cutoff searches, hard-share completions or source-preserving
saddle decompositions. The
[compensator notes](suzuki-subexponential-compensator.md) and
[Gaussian–Suzuki bridge](../RiemannGaussian/GaussianScrewBridge.lean)
give the existing interfaces. Published-region imports and finite-height
coverage remain separate from this all-height arithmetic task.

## Local joined-excursion and correlation audit, 2026-10-05

The optional
[`probe_suzuki_joint_excursions.py`](../scripts/probe_suzuki_joint_excursions.py)
now streams the literal integer von Mangoldt measure, including every proper
prime power, through `X=2^26=67,108,864`. It retains centered work and the
whole entropy credit before measuring changes, negative variation or
drawdown. These are floating research measurements, **not certificates**.

In the last doubling block, `[2^25,2^26]`, it finds:

| Quantity | Measured value |
| --- | ---: |
| Balanced cutoffs | 7,731 |
| Centered work | 96.50559263 |
| Entropy credit | 96.46640050 |
| Joined signed change | +0.03919213 |
| Sum of negative joined increments | 0.04809091 |
| Separated quadratic allowance | 195.72715107 |
| Minimum balanced potential | 0.02149858 |
| Longest observed balanced gap | 4,631,945 integers |

Fourteen gaps exceed the local `N^(3/4)` scale; they account for about 86%
of that block's negative variation. Thus the existing short balanced-block
bound does not cover the observed long intervals. The actual finite joined
cancellation is substantial, but its bounded appearance proves no
all-height excursion bound.

### What the positive-density control rules out

[`SuzukiJoinedExcursionAudit`](../RiemannGaussian/SuzukiJoinedExcursionAudit.lean)
proves an explicit continuous **tail control**, distinct from integer primes.
For `0<alpha<1/2`, `gamma>0`, it has eventually positive density, the exact
mass/log-moment derivative law and the full joined work-minus-entropy
identity. At complete phase times `t_n=2*pi*n/gamma`, its corrected mass is
exactly `2*exp(t_n/2)`, yet

\[
 B_{\rm model}(t_n)
   =b-\frac{2}{\alpha^2+\gamma^2}e^{\alpha t_n}.
\]

Every eventual lower allowance `-C*exp(delta*t_n)` with `delta<alpha`
therefore fails. No low-order channel, cross interaction or entropy cost
was dropped. Positivity, balance and the joined ledger alone cannot prove
the desired arithmetic floor.

The separate numerical control is globally positive: its continuous density
is `1` below `exp(B)`, and
`1-2*x^(beta-1)*cos(60*log x)` above it, where
`B=log(2)/(1-beta)`. For `beta=0.99995` its negative balanced minima have
measured power exponent `0.49995`, as predicted. Neither control has the
ordinary-prime Euler product, exact integer divisor identities or the
completed zeta functional equation. They refute the generic inferences
above, not an arithmetic theorem about the actual primes.

### The detector needs collective correlations

The probe also evaluates the **arithmetic time kernel**

\[
 K_\Psi(s,t)=\Psi(s)+\Psi(t)-\Psi(s-t),
\]

using the full literal prime contribution and digamma/Lerch completion.
This is not the automatically positive Gram matrix of pre-existing
Hilbert vectors. At 64 nonzero equally spaced nodes in `[-9,9]`, the
actual sampled kernel has minimum eigenvalue about `0.00686345`.
That is neither an all-window theorem nor a certified finite eigenvalue.

Synthetic off-axis quartet controls can make this matrix indefinite while
every sampled scalar value **and every two-node principal matrix** remain
positive. Thus pairwise checking can miss a collective direction. The
probe saves the offending node weights, the separate Archimedean and prime
quadratics and their joined value before any norm estimate. Its unit-
multiplicity controls are also labelled synthetic, never actual zeta zeros.

For example, adding a synthetic unit-multiplicity quartet at height `600`
and horizontal offset `0.49995` to the `[-9,9]` sampled kernel leaves the
minimum nonzero scalar value about `0.005969` and the minimum two-node
principal eigenvalue about `0.005296`, while the full minimum eigenvalue is
about `-0.069443`. Thus the collective failure does not require fractional
mode weights. This is an artificial diagnostic, not evidence for an
actual off-line zero at that height.

The Lean audit independently proves that a three-coordinate quadratic can
be nonnegative on every coordinate pair and negative on their joint
direction. It also checks the actual two-node identity

\[
 Q_\Psi(t,-t;1,1)=2[4\Psi(t)-\Psi(2t)],
\]

and the critical cosine identity
`4*(1-cos x)-(1-cos(2*x))=2*(1-cos x)^2`. No sign is asserted for the actual
arithmetic dilation defect or for its general quadratic.

No missing term or error in Suzuki's formula was found. The collective
test-function correlations are already part of his
[Weil/screw-function framework](https://arxiv.org/html/2606.09096v3).
They were underused by the scalar detector. For the actual zeta function,
global pointwise positivity already implies RH; the controls here do not
contradict that equivalence.

The next arithmetic task is to control the full signed prime quadratic
against its exact Archimedean reserve on growing windows, keeping all
cross terms. Merely verifying scalar values, pairwise submatrices,
automatic Hilbert Gram positivity, or more finite positive matrices does
not supply the missing estimate. The independent balanced floor and all-
height kernel bound remain **open**. Riesz stays frozen, and this pass
earns no new zero-free or RH credit. The local proof/probe scope is recorded
in [`suzuki-joint-excursion-audit.json`](suzuki-joint-excursion-audit.json).

## Exact integer-prime constraints and their sensitivity, 2026-10-05

The next local pass proves a constraint that the continuous controls do
not impose: **additive integer cutoffs must agree with prime factorization
at every scale**. This is classical factorial/binomial arithmetic, now
checked for the repository's literal von Mangoldt sequence; it is not a
claim of a newly discovered theorem about prime distribution.

[`SuzukiIntegerCarry`](../RiemannGaussian/SuzukiIntegerCarry.lean) proves

\[
 \sum_{d=1}^N\left\lfloor\frac Nd\right\rfloor\Lambda(d)
   =\log(N!).
\]

All proper prime powers and quotient endpoints are retained. More strongly,
if an arithmetic sequence `f` satisfies `f(0)=0` and every one of these
factorial observations, then `f=Lambda` exactly. Any different such sequence
fails at least one observation. Smooth density controls matching mass,
log-moment derivatives, positivity and the work/entropy ledger therefore
do not supply this full integer constraint system.

Define the exact binary carry

\[
 c_N(d)=\left\lfloor\frac{2N}{d}\right\rfloor
        -2\left\lfloor\frac Nd\right\rfloor\in\{0,1\},
 \qquad P_N=\sum_{d\le2N}c_N(d)\Lambda(d).
\]

The checked identity is `P_N=log(binomial(2N,N))`. Consequently,

\[
 N\log4-\log(2N+1)\le P_N\le N\log4,
\]

and the **joined signed adjacent prime sum** obeys

\[
 \log4-\frac1{2N+1}
 \le\sum_{d\le2(N+1)}[c_{N+1}(d)-c_N(d)]\Lambda(d)
 \le\log4-\frac1{2N+2}.
\]

This is an unconditional all-scale arithmetic estimate. Positive and
negative incidences have been combined before any norm. Complex weights in
the *cutoff variable* also retain this reciprocal defect bound; this does
not insert an arbitrary twist `d^(-iy)` inside each prime profile.

The optional
[`probe_suzuki_integer_carry.py`](../scripts/probe_suzuki_integer_carry.py)
replays literal prime powers through `2(N+1)=524,290`. At `N=262,144`, the
joined adjacent sum is about `1.386292453777`, with defect from `log 4`
about `1.907343176e-6`; the separated absolute incidences total about
`26.33959858`. These measurements are diagnostic, without outward rounding.
The Lean bounds, rather than the replay, provide the proof.

### Why this signed bound is not the Suzuki floor

[`SuzukiIntegerCarryMellinAudit`](../RiemannGaussian/SuzukiIntegerCarryMellinAudit.lean)
identifies `c_N(d)` with the floor-parity colour at `log(N/d)`, **including
every discontinuity endpoint**. Only the continuous integral uses an
almost-everywhere change to the repository's translated eta cells. For
`Re s>0`, `s!=1`, the actual integrable colour has transform

\[
 C(s)=\int_{\mathbb R}e^{-st}\,c(t)\,dt
     =\frac{(2^s-2)\zeta(s)}s.
\]

The full logarithmic power-mode response, with the scale and complex phase
retained, is exactly

\[
 \int_{\mathbb R}e^{st}c(T-t)\,dt=e^{sT}C(s).
\]

Thus if `zeta(s)=0`, this linear response is zero at **every** scale. The
same holds for finite combinations of dilated carry tests. The numerical
controls at `0.9+60i` and `0.99995+60i` have nonzero carry symbols, whereas
the first known critical zero gives the expected null response. Those
synthetic heights are not asserted to be actual off-line zeros.

This is a precise sensitivity failure of the **linear power-mode carry
test**, not a theorem that all integer arithmetic is powerless. The exact
factorial constraint system remains much stronger than any one asymptotic
projection, but the displayed signed bound does not oppose the genuine
zero source. It gives no independent Suzuki excursion floor, all-window
Weil-kernel bound, new zero-free region or RH proof. Further use needs a
source-sensitive arithmetic correlation, with a proved estimate; generic
positivity or another linear carry combination does not provide it.

Both leaf modules pass warnings-as-errors builds, 14 namespace linters
each and all-declaration transitive axiom checks. The only axiom
dependencies are `propext`, `Classical.choice` and `Quot.sound`. This pass
remains local, outside root/public metadata and ordinary CI. Its proof,
probe and limitation are pinned in
[`suzuki-integer-carry-audit.json`](suzuki-integer-carry-audit.json).

## Lagged carry-Gram and source-sensitive packets, 2026-10-05

The next pass keeps the full height twist and joins the literal integer
incidences **before** measuring a quadratic. It does not reopen the frozen
Riesz branch. Let `delta_N(d)=c_(N+1)(d)-c_N(d)` and

\[
 G_{N,M}(y)=\sum_d\Lambda(d)\delta_N(d)\delta_M(d)d^{-iy}.
\]

Every row has finite support. For any finite coefficient support `S`,
[`SuzukiCarryGram.fullQuadratic_eq_joined`](../RiemannGaussian/SuzukiCarryGram.lean)
proves exactly

\[
 \sum_{N,M\in S}\alpha_N\overline{\alpha_M}G_{N,M}(y)
 =\sum_d\Lambda(d)d^{-iy}
       \left|\sum_{N\in S}\alpha_N\delta_N(d)\right|^2.
\]

All proper prime powers and quotient endpoints are included. At nonzero
height this matrix is generally complex, **not** a Hermitian positive
Gram matrix. The checked nonnegativity assertion is restricted to `y=0`.
This same-prime-power incidence quadratic is also distinct from the full
off-diagonal Suzuki/Weil kernel.

### Exact integer correlation, without a density replacement

[`SuzukiCarryCorrelation`](../RiemannGaussian/SuzukiCarryCorrelation.lean)
proves the endpoint formula

\[
 \delta_N(d)=\mathbf1_{d\mid2N+1}+\mathbf1_{d\mid2N+2}
                  -2\mathbf1_{d\mid N+1}.
\]

Thus `G_(N,M)` is exactly a nine-term signed sum of the phase-preserving
divisor observations of `gcd(e_(N,i),e_(M,j))`, with endpoints
`e_N=(2N+1,2N+2,N+1)` and weights `(1,1,-2)`. In particular,

\[
 G_{N,N+1}(y)=-\log2\,2^{-iy}
             -\mathbf1_{N\bmod3=1}\log3\,3^{-iy}.
\]

For every positive lag `h`, no denominator `d>2h+1` contributes. A checked
entry bound is `|G_(N,N+h)(y)| <= 16 log(2h+1)`, independent of the absolute
cutoff `N`; this entry bound is **not** used to norm-pay the whole matrix.

The complete periodic formula is proved for `d>=2`:

\[
 A_d(h)=\frac{
 2\mathbf1_{h\equiv0\ (d)}
 -\mathbf1_{h\equiv\lfloor d/2\rfloor\ (d)}
 -\mathbf1_{h\equiv d-\lfloor d/2\rfloor\ (d)}}d.
\]

For even `d`, the two negative residues coincide. Both `d=0` and `d=1`
give zero. This sparsity follows from the exact two-spike profile modulo
`d`, not from averaged prime independence.

### The power-mode gate passes, with a scope distinction

[`SuzukiCarryGramSource`](../RiemannGaussian/SuzukiCarryGramSource.lean)
defines the same floor-parity packet in the continuous log-denominator
variable `t`; it agrees with the literal weights at every `t=log d`.
For the specified component `psi(x)-x=-(m/rho)x^rho`, `rho=beta+iy`, its
logarithmic derivative is `-m exp(rho*t)`. Matching the height and integrating
the exact squared kernel gives

\[
 -m e^{\beta T} C_{\alpha,\beta},\qquad
 C_{\alpha,\beta}=\int_{\mathbb R}e^{\beta t}
                 |\operatorname{realPacket}_\alpha(t)|^2\,dt>0.
\]

Genuine integrability and positivity are proved for every nonzero finite
packet and `beta>0`. For flat coefficients on `[A,2A)`, exact telescoping
and dilation give `C_(flat A,beta)=A^beta C_(flat 1,beta)`, with a fixed
positive base coefficient. This is a source-sized response, rather than
mere positivity at individual finite lengths.

This theorem tests **one specified Chebyshev component**. It does not
assert that the full literal prime statistic has a one-zero asymptotic,
or that other zero contributions cannot cancel it. Height matching also
changes the linear Mellin argument from `beta+iy` to `beta`; sensitivity
must not be attributed solely to squaring. The optional unweighted
squared-symbol replay is nonzero at the first two known critical zeros
(about `0.31513` and `0.10649`), but its Hurwitz/Dirichlet-beta transform
derivation is **not** a checked Lean theorem.

### A genuine arithmetic saving for the same Fejer packet

[`SuzukiCarryFejer`](../RiemannGaussian/SuzukiCarryFejer.lean) uses the
literal triangular coefficients obtained by averaging flat intervals
`[A+t,A+t+H)`, `0<=t<H`. Exact telescoping and a window exchange prove

\[
 W_{A,H}(d)\le\left(\frac{H\bmod d}{H}\right)^2.
\]

Every `d` dividing `H` is removed exactly. This is a kernel estimate,
before any prime-phase norm. For the growing packets with `A=H>=2`,
the same module proves the uniform matched-source lower bound

\[
 C_{A=H,H,\beta}\ge\frac{\log(9/8)}9 H^\beta
 \quad(\beta>0).
\]

It comes from an explicit macroscopic denominator cell
`4H<exp(t)<9H/2`; no continuum coefficient or concentration approximation
replaces the finite triangular weights.

After joining the phase-retaining statistic, define `lowPacket` by `d<=D`
and `highPacket` by `d>D` on the full physical support. Their sum equals
the complete quadratic **exactly**. The actual Chebyshev prime-power
bound and the preceding remainder identity yield

\[
 |\operatorname{lowPacket}(A,H,D;y)|
 \le(\log4+4)\frac{D^3}{H^2}.
\]

This independently pays the whole phased low-denominator sector. For
`H=n^2,D=n` it tends to zero absolutely. More relevant to the campaign,
on the cofinal integer scales `H=n^20000,D=n^19998`, it proves

\[
 \frac{|\operatorname{lowPacket}|}{H^\beta}
 \le\frac{\log4+4}{n^5}
 \quad\text{for every }\beta\ge19999/20000.
\]

Equivalently, `D=H^(9999/10000)` and the normalized saving is
`H^(-1/4000)`. Location `A`, height `y`, and every proper prime power
remain in the same literal statistic. This is a sector estimate;
`highPacket` has not been paid.

### What still prevents the requested whole-statistic result

Short lags suppress large denominators, but a source-sized packet uses
lags comparable to its growing block. Their correlations still contain
the main-scale prime powers. For flat coefficients the unsigned actual
quadratic is at least `A log4-log(4A+1)`; replacing the signed phase by
this whole positive mass cannot oppose an `A^beta` source for `beta<1`.
Raw density/pole contributions also need their correct centering or
Archimedean reserve before a whole-statistic smallness claim is possible.

The exact outstanding estimate is a source-precision signed bound for
the **same** `highPacket` (and the matching centering/reserve), not a
generic gcd-matrix bound, another linear carry identity, or a separate
positive capacity estimate. Neither the global Suzuki floor nor the
independent Gaussian/Weil arithmetic bound has been proved. The
requested criterion—one whole statistic both arithmetically small and
source-sensitive—remains open; the framework and source-sized
small-denominator saving are checked progress toward it.

The two optional probes replay full prime powers, exact endpoint gcds,
16,637 integer lag tests, arbitrary complex coefficient packets, and
flat/triangular/Hann localization. Floating replay and quadrature are
diagnostics, not numerical certificates or all-height estimates. All
five new leaf modules pass warnings-as-errors, 14 namespace linters each,
and all-declaration transitive axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. This work remains local, outside
root registration, public metadata and ordinary CI. Its proof scope and
hashes are recorded in
[`suzuki-carry-correlation-audit.json`](suzuki-carry-correlation-audit.json).

## Two-scale pole-centered carry preflight, 2026-10-05

[`SuzukiCarryPoleCenter`](../RiemannGaussian/SuzukiCarryPoleCenter.lean)
keeps the same finite Fejer packet at `A=H` and extends its response to

\[
 C_H(s)=\int_{\mathbb R}e^{st}W_H(e^t)\,dt,
 \qquad \Re s>0.
\]

The integrability is proved, and `C_H(beta)` equals the previously checked
real source coefficient. Twisting a component `exp(rho*t)` by the full
`exp(-iy*t)` phase gives exponent `rho-iy`. Thus density has exponent
`p=1-iy` and the matched component at `rho=beta+iy` has exponent `beta`.

For the **unchanged literal prime-power statistic** `Q_H(y)`, define

\[
 T_H=C_{2H}(p)Q_H-C_H(p)Q_{2H},\qquad
 \widehat T_H=T_H/H.
\]

The deterministic division by `H` does not require a nonzero complex
Mellin coefficient. It is necessary for an `H^beta` source comparison:
the native determinant has the expected scale `H^(1+beta)`.
The checked joint physical response is

\[
 D_H(s)=C_{2H}(p)C_H(s)-C_H(p)C_{2H}(s),\qquad D_H(p)=0.
\]

This is exact pole cancellation at every finite length, on the full
positive-denominator Mellin integral. If density is instead restricted
to denominators at least one, the omitted endpoint of each coefficient
has norm at most one, and its contribution to `T_H/H` has norm at most18.
That endpoint is independently bounded, not an additional source-scale
channel for `beta>0`.

The specified matched Chebyshev component contributes **exactly**
`-m D_H(beta)`. This alone is not an actual-prime one-zero asymptotic.
The finite sampling correction is important. Let

\[
 E_H(s)=C_{2H}(s)-2^s C_H(s).
\]

The checked identity retains it:

\[
 D_H(\beta)=(2^p-2^\beta)C_H(p)C_H(\beta)
             +E_H(p)C_H(\beta)-C_H(p)E_H(\beta).
\]

`ideal_scale_factor_ne_zero` proves
`|2^p-2^beta| >= 2-2^beta >0` for `beta<1`. But the literal finite
Fejer weights are **not** exactly dilational: a checked regression gives
`W_2(6)=1/4`, whereas `W_1(3)=1`. We therefore do not claim the determinant
is globally nonzero by dropping `E_H`. The module gives the exact finite
lower bound

\[
 |D_H(\beta)|\ge(2-2^\beta)|C_H(p)|\,C_H(\beta)
        -|E_H(p)|\,C_H(\beta)-|C_H(p)|\,|E_H(\beta)|
\]

and an explicit strict-defect-gap nondegeneracy criterion. Paying this
criterion cofinally for every fixed campaign height, including any
degenerate limiting pole symbol, remains an **open source gate**.

### Arithmetic ledger and the surviving centered obstruction

The same module expands `Q_H` through the exact endpoint gcd observations,
and joins both scales on the single prime-power support `d<=12H`:

\[
 T_H=\sum_{d\le12H}\Lambda(d)d^{-iy}
       [C_{2H}(p)W_H(d)-C_H(p)W_{2H}(d)].
\]

No phase or prime-power deletion is used. `normalizedStatistic_eq_low_high`
retains `lowStatistic` and the still-signed `highStatistic` exactly.
The proved coefficient support budgets `|C_H(p)|<=6H`,
`|C_(2H)(p)|<=12H` preserve the existing low-sector saving:

\[
 |\operatorname{lowStatistic}|
 \le\frac{27}2(\log4+4)\frac{D^3}{H^2}.
\]

For `H=n^20000,D=n^19998,beta>=19999/20000`, its norm divided by
`H^beta` is at most `(27/2)(log4+4)/n^5`. This is an independent payment
only of the literal low sector.

There is a checked macroscopic obstruction to **pointwise or positive
norm** payment on the main range. On `8H<d<9H`, the original-scale
weight is zero, while the doubled-scale weight is at least `1/9`.
Consequently the combined literal integer kernel has norm at least
`|C_H(p)|/9`. The genuine integrable joined absolute-density budget obeys

\[
 \int e^t|C_{2H}(p)W_H(e^t)-C_H(p)W_{2H}(e^t)|\,dt
 \ge\frac{8\log(9/8)}9H|C_H(p)|.
\]

Thus, when the pole coefficient has its expected nonzero linear scale,
this positive budget is quadratic before normalization and linear after
normalization. It cannot supply `o(H^beta)` for `beta<1`. This is a
proved obstruction to that **norm-payment method**, not a theorem that
the actual centered signed prime statistic remains source-sized or that
every two-scale approach is impossible. Cross-range signed cancellation
in `highStatistic` is still unproved; we do not revert to the uncentered
statistic or count the cancelled density as arithmetic credit.

### Quantitative replay and limits

The optional
[`probe_suzuki_carry_pole_center.py`](../scripts/probe_suzuki_carry_pole_center.py)
uses exact rational periodic jump bookkeeping for small packets, followed
by high-precision Hurwitz evaluations. Large packets use their unchanged
finite floor sums on a refined Mellin grid; literal prime-power sums are
evaluated by integer floor summation, joining the two scales before a
norm. The periodic Hurwitz and limiting-profile formulas are **paper/probe
derivations, not Lean imports**. Quadrature refinement and a lower-tail
budget are reported separately; neither is an outward-rounded certificate.

At `H=131072`, `beta=.99995`, height60, the modeled matched response of
`T_H/H`, divided by `H^beta`, is about `.0461518`, compared with `.0001152`
for the literal finite prime statistic. At the near-doubling-resonant
synthetic height `12pi/log2`, the modeled finite response is about
`3.52e-6`, with ideal limiting value about `1.86e-6`; finite scaling
corrections still matter. These heights are **not** asserted to be actual
off-line zeros. No all-height bound follows from these observations.

The exact pole cancellation and low-sector payment are checked. Universal
cofinal zero-response nondegeneracy and an independent source-precision
signed bound for the same `highStatistic` are not. Hence the user's
whole-statistic success criterion has **not** been met, and no Suzuki
floor, new zero-free region or RH claim is made. Focused build, 14 linters
and all-declaration standard-axiom audit pass. The local scope is pinned
in [`suzuki-carry-pole-center-audit.json`](suzuki-carry-pole-center-audit.json).

## Same-amplitude phase codes: exact diagonal removal, 2026-10-05

The latest user steer replaces the two-scale preflight by three modulations
of **one unchanged finite Fejer vector**. The local checked module is
[`SuzukiCarryPhaseCode.lean`](../RiemannGaussian/SuzukiCarryPhaseCode.lean).
All preceding two-scale results and negative audits remain available.

For arbitrary finite coefficients and modulations, the joined coefficient
at signed lag `h=N-M` is exactly

\[
 b(h)=\sum_j\lambda_j e^{i\theta_jh}.
\]

`familyQuadratic_eq_lag_fibers` joins the entire quadratic by signed lag;
`familyQuadratic_eq_offDiagonal` removes the diagonal when `sum lambda=0`.
`familyKernel_eq_zero_of_no_cross` kills **every** single-incidence
denominator, independently of its prime or prime-power status. Each
surviving off-diagonal incidence obeys `d<=2|h|+1` pointwise. The exact
correlated-prime sum and nine-term endpoint-gcd expansion both retain
`Lambda(d)d^(-iy)`; neither is replaced by a norm or a positive matrix.

There is a stronger literal outer cutoff: on coefficient support
`range(3H)`, a denominator `d>3H` meets at most one carry spike. Thus
`codedKernel_outer_eq_zero` kills that **entire** outer sector exactly.
No mass from an enlarged/doubled support is introduced.

The complex responses are the same genuinely integrable finite Mellin
responses, with the modulated coefficients:

\[
 C_{j,H}(s)=\int_{\mathbb R}e^{st}
      |\operatorname{realPacket}(a_Ne^{i\theta_jN};t)|^2\,dt.
\]

At `p=1-iy`, the cyclic coefficients
`lambda=(C_1(p)-C_2(p),C_2(p)-C_0(p),C_0(p)-C_1(p))` have both
`sum lambda=0` and `sum lambda*C_j(p)=0` **exactly**. The checked
`integral_coded_pole_eq_zero` identifies the integral response, including
genuine integrability before exchanging the finite sums.

There is a sign correction to the proposed steer: this particular cyclic
vector is the **negative** of the cofactors of the last determinant row.
Consequently the specified matched component has response

\[
 -m\sum_j\lambda_j C_{j,H}(\beta)
 =+m\det\begin{pmatrix}
 1&1&1\\ C_{0,H}(p)&C_{1,H}(p)&C_{2,H}(p)\\
 C_{0,H}(\beta)&C_{1,H}(\beta)&C_{2,H}(\beta)
 \end{pmatrix}.
\]

This is a response to **one specified diagnostic Chebyshev component**,
not an actual-prime single-zero asymptotic. The natural normalized
statistic is `codedStatistic/H`; its source size is measured by the
native determinant divided by `H^(1+beta)`. There is no division by an
unproved nonzero coefficient.

Two exact preflight exclusions are useful. For real amplitudes, opposite
modulations have identical squared kernels. Thus `0,+theta,-theta` has
zero determinant at every H and exponent. Fixed phase `pi` instead has
literal mass **H^2 at d=2**. The old unmodulated Fejer low-denominator
payment cannot be transferred to arbitrary modulations. These exclusions
do not prove that every asymmetric slow code fails.

The candidate `theta_j=j/H`, for `j=0,1,2`, avoids these two regressions.
The optional finite-profile probe tests H through8192, synthetic heights
54.38832170192632,60,100,1000, and beta=.99995,.999975,.9999999. At height60
and beta=.99995 its normalized modeled determinant is about6.90e-4 at
H=8192; at height54.388 it is about1.06e-4. Every proper prime power is
retained in the separate literal statistic, and its modulation phase
normalization is retained too. The probe compares integer residue and
direct carry evaluations, joined/off-diagonal algebra, the outer cutoff,
and the pi alias. Refinement and omitted-tail bounds are **not** a proof
of uniform quadrature error or cofinal nondegeneracy.

The exact source gate is the non-collinearity of the two response
contrasts:

\[
 (C_1(p)-C_0(p))(C_2(\beta)-C_0(\beta))
 -(C_2(p)-C_0(p))(C_1(\beta)-C_0(\beta)).
\]

`sourceDet_eq_zero_iff` identifies source loss exactly.
`sourceDet_norm_lower_of_gap` gives a quantitative sufficient gap, with
its analytic response hypotheses explicitly retained. A cofinal lower
bound of source size for the **literal** Cmod responses at every permitted
fixed height and campaign beta is **not yet proved**. The numerical
candidate is promising; the user's strict three-property success gate
is not yet discharged. Heavy global arithmetic payment is deferred to
that gate. The slow-modulation low-denominator and lower-density-endpoint
bounds must also be proved before borrowing those old unmodulated credits.
No independent small bound for the correlated remainder, new zero-free
region or RH contradiction is claimed. Focused build, 14 linters and the
all-declaration standard-axiom audit pass; see
[`suzuki-carry-phase-code-audit.json`](suzuki-carry-phase-code-audit.json).

## Scaled Mellin convergence and the asymmetric cofinal gate, 2026-10-05

The source limit now has an exact continuous description. The new local
leaves are
[`SuzukiCarryMellinLimit`](../RiemannGaussian/SuzukiCarryMellinLimit.lean),
[`SuzukiCarryMellinRate`](../RiemannGaussian/SuzukiCarryMellinRate.lean), and
[`SuzukiCarryDeterminantGate`](../RiemannGaussian/SuzukiCarryDeterminantGate.lean).
The arithmetic statistic and every preceding positive result/no-go remain
unchanged. No global arithmetic payment is attempted before the source gate.

Let

\[
 f(v)=\max(0,\min(v-1,3-v)),\qquad
 P_\tau(x)=\sum_{k=1}^{\lceil6/x\rceil}
       (-1)^{k-1}f(kx/2)e^{i\tau kx/2}.
\]

The finite Fejer coefficient is exactly `f((N+1)/H)`. The finite packet,
at log denominator `t+log H`, equals `exp(-i*tau/H)` times the same
alternating jump sum with every `kx/2` rounded upward to the `1/H` grid.
`realPacket_eq_roundedProfile` retains all jumps landing on grid boundaries
and all coincidences. In particular, after squaring, the phase prefactor
disappears and the requested normalization satisfies the exact identity

\[
 F_H(s,\tau)=H^{-s}C_{H,\tau/H}(s)
 =\int_{\mathbb R}e^{st}|P_{H,\tau}(e^t)|^2\,dt.
\]

The limiting response is

\[
 F(s,\tau)=\int_{\mathbb R}e^{st}|P_\tau(e^t)|^2\,dt.
\]

These are genuinely integrable when `Re(s)>0`. Joined alternating partial
sums give count-independent bounds `|P_tau|<=3(1+|tau|)` and
`|P_H,tau|<=4(1+|tau|)`, and both vanish at `x>=6`. The grid error is
`(1+|tau|)(6/x+1)/H`. Splitting the Mellin integral at
`t=-log H/2` pays the small-x tail separately from the grid error.
For `0<a<=1` and `a<=Re(s)<=b`, Lean proves

\[
 \boxed{\quad
 |F_H(s,\tau)-F(s,\tau)|
 \le\frac{(25+49\cdot6^b)(1+|\tau|)^2}{a}\,H^{-a/2}.
 \quad}
\]

`tendstoUniformlyOn_scaledResponse` proves joint uniform convergence over
the entire real-part strip and any bounded tau interval. There is no
imaginary-height cost in this sampling estimate. `continuumResponse_neg`
proves evenness from the exact finite identity.

For the asymmetric phases `0,tau/H,2tau/H`, the normalized native
determinant therefore converges to the stated continuum determinant:

\[
 e^{-(p+\beta)\log H}\det C_H
 \longrightarrow
 \Delta_{p,\beta}(\tau).
\]

`normalized_nativeDet_eq` proves the finite normalization exactly.
`continuumDet_ne_zero_iff_cofinal_source` proves that a nonzero continuum
determinant is **equivalent** to some positive cofinal native source
margin. In particular, if it is nonzero, then eventually

\[
 |\det C_H|\ge\tfrac12|\Delta_{p,\beta}(\tau)|
    H^{\Re p+\beta}.
\]

Thus for `p=1-iy`, division of the diagnostic statistic by H retains
source size `H^beta`. This is still a matched-component response, not an
actual-prime single-zero asymptotic or an independent arithmetic bound.

The fourth-order jet algebra gives exactly

\[
 \det(1,A+B\tau^2+C\tau^4,a+b\tau^2+c\tau^4)
 =12(Bc-Cb)\tau^6.
\]

`normalized_contrastDet_eq` retains the full actual jet remainders.
`exists_fixed_code_source_lower` proves the positive fixed-tau/cofinal
conclusion **under** explicit fourth-order expansion and nonzero-wedge
premises. The actual continuum expansion and universal nonvanishing for
every permitted `p!=beta` are **not yet proved**. The theorem is not a
discharge of those premises. We therefore have not passed the complete
cofinal determinant gate and have not begun the heavy arithmetic remainder.

The optional continuum probe checks finite Euler-polynomial moment sums,
exact-rational grid coincidences, and quadrature refinement. The separate
jet detector retains the polynomial components before combination: knots
have the form `2a/b`, with `a=1,2,3`, and the branch data compress to eight
residue classes modulo2,4,6. It replays 240 exact rational moment branches.
A proposed Mellin boundary/Hurwitz formula agrees with independent
quadrature: at synthetic height60 and beta=.99995 it gives the wedge
approximately `8.302538575e-5+8.227571629e-6*i`. This compression is an
analytic research lead; its Mellin identification is not a Lean theorem.
Neither floating evaluation nor sampled nonzero values certify all heights.

The focused leaves and all-declaration axiom checks are kept separate from
ordinary CI; no commits, root registration, public explorer changes or
wider gates are run. See the scoped
[`suzuki-carry-mellin-limit-audit.json`](suzuki-carry-mellin-limit-audit.json).

## Periodic remainder payment: negative checkpoint, 2026-10-05

The proposed bounded-prefix/Fejer-variation payment has a checked
source-scale obstruction, even if its cofinal determinant gate succeeds.
This is a short negative preflight of that payment, not a positive global
arithmetic estimate performed before source nonvanishing. The two local
leaves are
[`SuzukiCarryPeriodicDiscrepancy`](../RiemannGaussian/SuzukiCarryPeriodicDiscrepancy.lean)
and
[`SuzukiCarryPeriodicBudgetAudit`](../RiemannGaussian/SuzukiCarryPeriodicBudgetAudit.lean).

For the unchanged literal Fejer vector, set

\[
 E_{H,h,d}=\sum_{N<3H}a_Na_{N+h}
       \bigl(\delta_N(d)\delta_{N+h}(d)-A_d(h)\bigr).
\]

At `d=2h+1`, the centered periodic row is exactly
`1/d - 1_{N mod d=h}`. Every partial sum has magnitude at most one,
and every complete-period sum is zero. Nevertheless, for `H<=h` and
`2h<3H`, with `r=2H-h`, Lean proves the literal identity

\[
 E_{H,h,2h+1}
 =\frac{r(r^2-1)}{6H^2(2h+1)}-a_ha_{2h}.
\]

In particular,

\[
 \boxed{\ E_{H,H,2H+1}\longrightarrow\frac1{12}.\ }
\]

Thus a pointwise Fejer slope of order `1/H` does not give a row discrepancy
of order `1/H`. Its total variation over a main-scale period is not small.
Lean proves more than a single-denominator example: for `H>=100` and
`H<=h<=101H/100`, this discrepancy is at least `1/20`.

The audit then joins **all three modulations, both lag orientations and
all N rows before taking any norm**. If `c_H` is the exact normalized
canonical Mellin code, their joined symbol is

\[
 2S_{c_H}(\tau,h/H),\qquad
 S_c(\tau,x)=c_0+c_1\cos(\tau x)+c_2\cos(2\tau x).
\]

A nonzero continuum determinant implies `c_H -> c_infinity != 0`.
For every fixed `tau>0`, a nonzero code cannot make this symbol vanish
on an open interval. There is consequently a fixed subinterval of
`1<h/H<101/100` on which its norm stays positive. The existing actual-prime
PNT supplies linear logarithmic mass of ordinary primes `d=2h+1` in
that band. Those primes are strictly above `2H`, below `3H`, and outside
any paid low-denominator cutoff at most `2H`.

Let `V_H` be the sum of norms of those fully joined periodic-discrepancy
rows, retaining every prime power and the full `d^(-iy)` phase. The native
and normalized codes are connected by an exact pre-norm identity;
`nativePeriodicBudget/H` is exactly the normalized budget. For **every**
fixed source-retaining `tau`, every fixed height, and `beta<1`, Lean proves

\[
 \Delta_{1-iy,\beta}(\tau)\ne0
 \quad\Longrightarrow\quad
 \boxed{\ \frac{V_H^{\rm native}}{H^{1+\beta}}
                  \longrightarrow+\infty.\ }
\]

`componentwise_allowance_source_diverges` covers any allowance bounding
each fully joined `(d,h)` row separately, including a sharper discrete
summation-by-parts allowance. Optimizing the determinant, periodic prefix
constant or such an allowance cannot make this payment source-small.
The proof uses actual primes, not a continuous-density countermodel or
a hypothetical single-zero prime asymptotic.

This negative checkpoint **does not bound the signed sum from below**
and does not prove that cancellation across different primes or lags is
impossible. Such signed correlation would be new input. Stop the tested
componentwise periodic/SBP payment; retain the exact lag ledger, all earlier
source theorems and every no-go. The actual all-height existence of a
nonzero continuum determinant and the literal fourth-order expansion are
still open. No arithmetic floor, packet decay, new zero-free region or RH
claim follows here.

Both leaves pass their focused build, all 14 namespace linters and the
all-declaration standard-axiom audit: 157 declarations, including 145
theorems/private/generated proofs. The optional probe independently replays
272 rational rows, 14 uniform-band rows and the joined modulation identity.
It is outside ordinary CI and is not an asymptotic certificate. Exact scope
and source pins are in
[`suzuki-carry-periodic-discrepancy-audit.json`](suzuki-carry-periodic-discrepancy-audit.json).

## Actual carry jets and global collapse, 2026-10-06

The actual fourth-order continuum expansion is now proved for every
positive real-part Mellin exponent. Its signed coefficients also have
an exact convergent elementary polynomial-cell series, with certified
truncation errors. This discharges the earlier expansion premise.
The all-height nonzero wedge/alternative-code claim remains open:
the explicit exceptional equation has not been proved to have no
solutions in the campaign strip. A nonexceptional candidate now gets
the fixed positive modulation and cofinal source margin directly.

The complete arithmetic collapse is also checked. Every row, modulation,
lag orientation and prime power joins into one exact twisted von
Mangoldt sum. A global signed Abel identity makes it one Chebyshev
test with an exactly zero outer boundary. Both the row join and the
endpoint-gcd identities hold for arbitrary denominator weights; their
bookkeeping alone adds no prime-specific size constraint. The previous
rowwise/SBP payment remains closed, and no independent smallness bound
for this test is proved. Stop this carry estimation route unless new
actual-prime arithmetic input is identified. This audit does not rule
out future prime-specific identities and does not exclude any zero.

The exact formulas, exceptional equation, arithmetic reduction and
scoped validation are in
[`suzuki-carry-collapse.md`](suzuki-carry-collapse.md) and its
[local audit](suzuki-carry-collapse-audit.json). Public root/metadata
registration and wider publication checks are not part of this local
slice.

## Publication of the carry jet and collapse checkpoint

The 2026-10-06 publication registers `SuzukiCarryMellinJet`,
`SuzukiCarryMellinBranches` and `SuzukiCarryCollapseAudit` in the ordinary
root and Suzuki theorem family. The actual fourth-order expansion and
elementary coefficient series are checked; universal campaign determinant
nonvanishing is still open. The complete signed statistic collapses exactly
to a twisted Chebyshev test, with no independent prime-specific bound
provided by the carry/gcd reindexings. Further carry estimation is stopped
pending genuinely new arithmetic input. The global Suzuki criterion
remains the active endpoint, Riesz remains frozen, and no new zero
exclusion or RH proof is claimed. See the
[published scope](suzuki-carry-publication.md),
[mathematical details](suzuki-carry-collapse.md) and
[root publication audit](suzuki-carry-publication-audit.json).
