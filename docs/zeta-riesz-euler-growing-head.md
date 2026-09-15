# Growing prime heads in the original arithmetic band

The complete Euler correction remains independently negligible after multiplication
by a growing head of actual primes. For every fixed polynomial filter `P`, ordinate
`y`, and source scale `0<u<1`, a positive integer stride `d` pays every head prime up
to `n+16` at the original factorial order `d*n`. The physical cutoff, both Fourier
phases, logarithmic mark and exact prime universe remain unchanged.

The terminal deletion theorem is
[`exists_stride_actual_band_sub_windowResidual`](../RiemannGaussian/ZetaRieszEulerWindowDeletion.lean).
Its error tends to zero without a hypothetical-zero premise. The subsequent
`exists_stride_normalizedWindowResidual_source` proves that the exact negative
multiplicity source survives on a genuinely cofinal sequence if a right-half zero
exists. The independent lower bound for the full residual remains open.

Open the [growing-head theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=euler-growing-head-deletion)
for the Lean statements, hypotheses, source lines and transitive axiom audits.
The default RH explorer still ends at the original whole-carrier critical profile.

## Entire coefficients and exact head phases

Write `H` for the full correction product, with every prime interaction order
retained. An arbitrary fixed entire coefficient `A(s)` and fixed real shift
`delta` act before differentiation on the paired correction kernel. Its
normalization stays `1/L`, even when its frequency shifts to `delta-L`.
For `L>=a>0`, the shifted phase cost satisfies

\[
\frac{\operatorname{phaseTailCost}(\sigma,\delta-L)}{L}
\leq
\frac{\operatorname{phaseTailCost}(\sigma,a+|\delta|)}{a}.
\]

On a Cauchy circle of radius `R`, a bound `C` for `|A|` gives the original
filtered response an allowance

\[
C\,\operatorname{shiftBudget}(\sigma,a,\delta,K)
\,\operatorname{filterRadiusCost}(P,R)
\,(N+1)(u/R)^{N+1},\qquad \sigma=\Re(s)-R>\tfrac12.
\]

The entire coefficient has an independent compact-circle bound. Joint
measurability, ordinary frequency integrability, all factorial moments and the
finite filter–integral exchanges are proved. This covers every fixed finite
family of entire coefficients and real frequencies.

For a finite head `S`, the exact character has the Fourier expansion

\[
\prod_{p\in S}\bigl(1+p^{-s}(1-e^{i\xi\log p})\bigr)
=\sum_{T\subseteq S} A_{S,T}(s)e^{i\xi\delta_T},
\]
\[
A_{S,T}(s)=\prod_{p\in T}(-p^{-s})
\prod_{p\in S\setminus T}(1+p^{-s}),
\qquad \delta_T=\sum_{p\in T}\log p.
\]

Every coefficient sign and subset frequency survives until the estimate.
The full head times `H-1` is therefore covered, including every interaction
between the head and the complete correction.

## One bound for all head families

The head coefficients have explicit bounds throughout a closed half-plane:

\[
C_{S,T}(\sigma)=\prod_{p\in T}p^{-\sigma}
\prod_{p\in S\setminus T}(1+p^{-\sigma}),
\qquad
\sum_{T\subseteq S}C_{S,T}(\sigma)
=\prod_{p\in S}(1+2p^{-\sigma}).
\]

The complete head budget is at most this positive Euler product times
`shiftBudget(sigma,a,delta_S,K)`. For every subset of `range(b+1)`, Lean proves
an elementary bound

\[
\operatorname{headResponseBudget}
\leq 3^{b+1}\operatorname{shiftBudget}(\sigma,a,1,K)
\bigl(1+(b+1)^2\bigr).
\]

No prime-density estimate or search over coefficients is assumed. These
bounds are sufficient, with no optimality claim. They are uniform over all
head subsets, all finite correction selections above sixteen and the chosen
tail threshold, all heights in the fixed half-plane, and physical lengths
above `a`. Constants may depend on the fixed filter and Cauchy parameters.

At the original center `3/2+i*y`, choose `R=(u+1)/2` and `gamma=u/R<1`.
There is a positive integer `d` with `3*gamma^d<1`. At order `d*n`, any head
inside `range(n+c+1)` then has allowance proportional to

\[
3^{n+c+1}\bigl(1+(n+c+1)^2\bigr)(dn+1)\gamma^{dn+1}\longrightarrow0.
\]

The remaining factor is a cubic polynomial times a strict geometric decay.
This pays a growing head, with all factorial offsets still present.

## The literal remaining carrier

At order `N` and threshold `b`, the head and tail partition the exact prime
factors of `primorial(2^(32*N))` at `p<=b` and `p>b`. For the growing estimate,
use `N=d*n` and `b=n+16`. The actual head is covered by the window bound and
all complementary correction primes satisfy the quarter-disc hypothesis.

Write `S` for this head character, `G` for its complementary finite Euler
quotient, `H` for the full complementary correction, `A` for the entire
ordinary-prime compensation, and `B` for the whole signed off-band boundary.
The exact completed-band identity is

\[
SGH-1-A-B
=\underbrace{(SG-1-A)+S(G-1)(H-1)-B}_{\text{explicit residual}}
+\underbrace{S(H-1)}_{\text{independently paid correction}}.
\]

This equality holds as a local analytic identity. It passes through every
original factorial derivative, the logarithm-marked fixed filter, both
physical Fourier phases and genuinely integrable frequency responses.
The resulting normalized difference between the literal band and the
explicit residual tends to zero along the positive stride. Cofinality and
the preserved negative-multiplicity source are separately proved.

Three pieces remain coupled: the compensated leading quotient `SG-1-A`,
the mixed `S(G-1)(H-1)`, and the signed boundary `B`. The growing leading
quotient itself is not independently bounded. The correction estimate does
not prove a separate bound for the mixed term or discard its correlation
with the boundary. The joint independent real floor above `-1` remains open;
this result proves neither RH nor a larger zero-free region.

## Modules and audit

The root library imports `ZetaRieszEulerMultiplier`, `ZetaRieszEulerHead`,
`ZetaRieszEulerHeadDeletion`, `ZetaRieszEulerGrowingHead` and
`ZetaRieszEulerWindowDeletion`. The fixed-head specialization also preserves
the source and proves the conditional implication
`rh_of_headResidual_cofinal_floors`; its floor premise is not discharged.

The [compiled status](proof-status.json) and
[RH explorer audit](rh-proof-explorer/audit.json) track the theorem endpoints
and dependencies. Ordinary CI checks the library and generated proof data;
the optional exhaustive numerical certificate is not part of this work.
