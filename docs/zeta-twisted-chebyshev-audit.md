# Twisted Chebyshev arithmetic: strength audit

This local investigation follows the frozen Riesz endpoint. It introduces
no Riesz carrier, independent prime non-coherence bound, or zero exclusion.
The question is whether arithmetic across scales can rule out the coherent
ordinary-prime source without assuming a power-error PNT.

## Exact arithmetic and the matched zero

For fixed real height `y`, put

\[
 M_y(X)=\sum_{1<n\le X}\Lambda(n)n^{-iy}-\int_1^X x^{-iy}\,dx.
\]

The omission of `n=1` makes no difference since `Lambda(1)=0`.
`ZetaTwistedChebyshev.cumulative_eq_chebyshev_error` checks the exact identity

\[
 M_y(X)=X^{-iy}(\psi(X)-X)+1+
 iy\int_1^X (\psi(x)-x)x^{-1-iy}\,dx,
 \qquad X\ge1.
\]

The `+1` is the lower-endpoint contribution. Equivalently use
`psi(x)-x+1`, in which case that explicit constant disappears. No PNT,
exposure, zero hypothesis, or phase freezing enters this identity.

For ONE specified zero component, write
`E_rho(x)=-m*(x^rho-1)/rho`. Its derivative is
`-m*x^(rho-1)`, so after twisting its cumulative contribution is

\[
 -m\int_1^X x^{\rho-1-iy}\,dx
 =-\frac{m}{\rho-iy}(X^{\rho-iy}-1).
\]

At `rho=beta+iy`, this is

\[
 \boxed{-\frac m\beta(X^\beta-1)}.
\]

Thus twisting changes the denominator from `rho` to `beta`, as well as
removing the phase. The checked `matched_zeroComponent` and
`matched_zeroBlock` express this in `T=log X` coordinates. The corresponding
unit log-block contribution is exactly

\[
 B_y(T)=-\frac m\beta(e^\beta-1)e^{\beta T}.
\]

These component identities do NOT claim that actual `M_y` has this
single-term asymptotic. Other zeros contribute at frequencies `Im(tau)-y`;
the conjugate zero, in particular, still oscillates at `-2y`. Boundary and
trivial-zero terms in a complete explicit formula must also be retained.

## Relation to the checked factorial transform

Let `s0=3/2+iy`, `c=s0-1`, and let `V_k(s0)` be the complete von Mangoldt
factorial moment. Finite Stieltjes integration by parts gives, for `k>=1`,

\[
 \begin{split}
 V_k(s_0)&=c^{-k-1}+\frac1{k!}\int_0^\infty
 M_y(e^t)e^{-3t/2}
 \left(\frac32t^k-kt^{k-1}\right)\,dt,\\
 a_k(u,y)&=u^{k+1}\left(V_k(s_0)-Q_k(s_0)\right).
 \end{split}
\]

`Q_k` is the unchanged proper-prime-power correction. The boundary at
infinity vanishes using the elementary `M_y(X)=O_y(X)` bound. At zero,
`M_y(1)=0`. The displayed infinite `M_y` formula is a paper-level derivation
in this note; it has not been added as a separate Lean theorem.

Substituting the checked finite Abel formula for `M_y` and recombining
integrals yields the EXISTING checked formula
`ordinary_moment_eq_psi_error_integral`. Its centered integral is exactly
`s0*errorMoment(k,c)-errorMoment(k-1,c)`. The explicit main term and the
proper powers decay in the campaign height regime. The checked
`errorSource_tendsto_iff` identifies its limit with the actual prime limit.

For a diagnostic zero component, the new checked `component_source` gives

\[
 u^{k+2}\{s_0E_{k+1}(\tau)-E_k(\tau)\}
 =-m_\tau\left(\frac u{s_0-\tau}\right)^{k+2}.
\]

The matched component equals `-m` EXACTLY. A fixed nonzero ordinate offset
`w` with the same real part has ratio `u/sqrt(u^2+w^2)<1` and disappears
geometrically. `offset_component_tendsto` and `coupled_components_tendsto`
check both statements, including a retained matched component.

## The benchmark is a global horizontal zero-free theorem

Suppose `|M_y(X)|<=C_y X^alpha` with `alpha<1`, for ONE fixed height and all
large `X`. Initially on `Re(s)>1`, integration by parts gives

\[
 -\frac{\zeta'}\zeta(s+iy)-\frac1{s+iy-1}
 =s\int_1^\infty M_y(X)X^{-s-1}\,dX.
\]

The bound makes the right side holomorphic on `Re(s)>alpha`. It therefore
excludes ALL zeros with real part greater than `alpha`, not only zeros
with ordinate `y`: twisting shifts the imaginary coordinate and leaves
the horizontal half-plane unchanged. This is a paper-level strength audit,
not a new unconditional Lean region.

For `alpha=19999/20000-eta` the centered factorial contribution is bounded
by a fixed constant times

\[
 \left(\frac u{3/2-\alpha}\right)^{k+1}
 \le\left(\frac{10001/20000}{10001/20000+\eta}\right)^{k+1}.
\]

The elementary main and proper powers are already paid for fixed campaign
`|y|>=54`. Merely `o(X^(19999/20000))` gives decay at the endpoint but no
fixed geometric rate without an additional power margin. The same little-o
bound rules out boundary zero residues by an Abelian limit; it remains a
strong global horizontal assertion, not the sought weaker arithmetic input.

## Detector controls and rejected mechanisms

`scripts/probe_twisted_chebyshev.py` is optional and outside normal CI. It
sieves literal integer prime powers through `2^22`, with the full twist,
and separately runs a positive continuous control. These finite prime
samples only calibrate the detector; they cannot certify the all-scale gap.

The continuous control has density

\[
 d\psi_{\rm model}/dx=1-2x^{\beta-1}\cos(y\log x)
\]

above a sufficiently large fixed lower cutoff, and density one below it.
For `beta=19999/20000`, log-cutoff `B=ceil(1/(1-beta))` makes the density
strictly positive. Its relative ripple is at most `2e^{-(1-beta)T}`.
It passes the previously checked subexponential relative-PNT controls and
its prime-density factorial moments converge to `-1`.

Above the cutoff its normalized log-block is exactly

\[
 e^{-\beta T}B_{\rm model}(T)
 =-\frac{e^\beta-1}\beta
 -\frac{e^{\beta-2iy}-1}{\beta-2iy}e^{-2iyT}.
\]

Over a full period its centered variance is strictly positive, equal to
the squared modulus of the second coefficient, while the factorial source
still converges to `-1`. The floating regression gives variance
`0.0002751331085` at `y=60` and `0.0001434919843` at `y=100`.
The exact mean is about `-1.7182318294`. This is a continuous control, not
a counterexample about ordinary primes or an ordinary zeta zero.

| Candidate | Strength check | Verdict for this pass |
|---|---|---|
| Positive raw/block variance on infinitely many scales | Oscillations coexist with a persistent constant after twisting; the Gamma/factorial average filters them out | Reject: positive variance does not even imply non-coherence for the positive control |
| Adjacent-block differences, scale increments, or phase dispersion | They annihilate the constant component that must actually be controlled | Reject as standalone anti-coherence criteria |
| `B_y(T)=o(e^(alpha T))` uniformly in all large `T` | Telescoping produces `M_y(e^T)=o(e^(alpha T))` for `alpha>0`; same power benchmark | Reject as a claimed weaker mechanism |
| PNT envelopes / finite-degree correlation estimates with only logarithmic relative savings | A ripple `X^(-epsilon)` is eventually smaller than every fixed logarithmic loss | Insufficient source precision; do not import as a floor proof |
| Positivity, integer lattice spacing, and atom sizes `O(log X)` alone | They do not prohibit a cumulative bias of size `X^beta`; finite discreteness is far smaller | No quantitative anti-coherence inference obtained |
| Archimedean phase contagion under prime dilations | `phase(y,pn)=phase(y,p)*phase(y,n)` is an EXACT character identity, checked by `phase_mul` | The twist already satisfies the structured alternative; phase compatibility is not a contradiction |
| Generic divisor/Euler identities | The existing Selberg audits and generalized-prime controls retain source modes | Preserve the no-go; literal identities require additional quantitative arithmetic information |

These are scoped failures of the listed inferences. They do not rule out a
new theorem exploiting literal primes jointly at much finer precision.

## Literature input using actual primes

The closest match is [Matomäki–Radziwiłł–Shao–Tao–Teräväinen, *Higher
uniformity of arithmetic functions in short intervals II*, v2 January
2026](https://arxiv.org/html/2411.05770v2). Theorem 3.1 handles the ACTUAL
twist `n^(-iT)` in `Lambda-Lambda^sharp`, with `H/log^A X` errors outside
an exceptional set. Section 3.4 removes a fixed/small height by partial
summation and reduces to the untwisted arithmetic estimate. The contagion
mechanism identifies archimedean characters; it does not forbid the
subleading matched ripple at the precision needed here. These facts defeat
the immediate application, not every possible refinement of that method.

[Teräväinen, *Quantitative Gowers uniformity of the primes in intervals
of length X^(5/8+epsilon)*, submitted 2 October
2026](https://arxiv.org/html/2610.03707v1) is a relevant new primary source.
It improves quantitative nonabelian Type-II machinery but gives
quasipolynomial savings and explicitly separates small-height major arcs.
It supplies no fixed power estimate for this persistent ordinary-zeta mode.

[Matomäki–Radziwiłł–Tao, *Correlations of the von Mangoldt and higher divisor
functions I*](https://arxiv.org/abs/1707.01315) uses genuine integer additive
correlations, but the displayed results average over shifts with
logarithmic error savings. Converting them by Cauchy–Schwarz cannot resolve
a rank-one bias smaller than those errors; an additional source-precision
estimate would be needed.

[Fourier uniformity of bounded multiplicative functions in short intervals
on average](https://arxiv.org/abs/1812.01224) controls non-pretentious bounded
multiplicative functions. `Lambda` is not such a function, and `n^(-iy)`
is itself an archimedean character. No direct non-coherence corollary follows.

[Broucke's prescribed-zero generalized-prime
constructions](https://arxiv.org/abs/2507.13780) and
[Révész's given-zero Beurling error
oscillation](https://arxiv.org/abs/2202.01837) reinforce the need to use
ordinary integer arithmetic beyond generic Euler structure. They are
research controls, not Lean imports or ordinary-prime counterexamples.

## Decision

No tested cross-scale candidate supplies a genuinely new arithmetic
non-coherence theorem. Do not develop a large formal transport for them.
The useful remaining target would be an estimate on the SIGNED persistent
Mellin projection of actual `Lambda`, with its mean retained, at source
precision across infinitely many growing scales. Ordinary fluctuation
variance and finite-complexity uniformity at logarithmic precision cannot
provide it. A premise that simply asserts that projection is non-coherent
is the existing terminal criterion, not newly discovered arithmetic.

Keep the exact twisted bridge and the diagnostic audits. The all-height
non-coherence estimate remains OPEN; this investigation earns no new RH,
floor, or zero-free credit. Local Lean validation and optional probes only;
no publication/root-registration gate is authorized for this slice.
The [scoped proof audit](zeta-twisted-chebyshev-audit.json) records the
warning-as-error leaf build, 14 namespace linters, standard-axiom checks
including private helpers, and separately labelled optional model probes.
