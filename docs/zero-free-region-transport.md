# Larger external regions and the complete arithmetic transport

The current proved zero-free family reaches the original marked
squarefree arithmetic response. For every fixed
`0<A<pi/(140*log(2))`, an eventual width
`A*log(log(abs(t)))/log(abs(t))` is now proved, with a coefficient-dependent,
unevaluated height threshold. These modules provide the connection:

- [ZetaZeroFreeRegionBand.lean](../RiemannGaussian/ZetaZeroFreeRegionBand.lean)
  handles general decreasing width functions and complete height bands.
- [ZetaSquarefreeEulerBandRadius.lean](../RiemannGaussian/ZetaSquarefreeEulerBandRadius.lean)
  turns those bands into actual analytic discs and signed-phase Cauchy bounds.
- [ZetaLogLogZeroFree.lean](../RiemannGaussian/ZetaLogLogZeroFree.lean)
  proves both actual zero-strip edges and complete height bands for every
  coefficient in the stated range.
- [ZetaSquarefreeLogLogRadius.lean](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean)
  discharges the actual disc and marked-response hypotheses for the log-log family.

The external optimized constants and finite starting heights below are
research inputs, not axioms or verified Lean results in this repository.
The classical Littlewood width shape itself is now formally established
with the stated coarser coefficient range and existential thresholds.

## Published targets and useful ingredients

Write `L = log(abs(t))`. These are selected stronger results, not a claim
that this table exhausts the literature. Compare widths at the same height
and respect each theorem's height and boundary conditions.

| Source | Nonvanishing region | Scope and useful ingredient |
| --- | --- | --- |
| [Platt and Trudgian, *The Riemann hypothesis is true up to 3·10¹²*, BLMS 2021](https://arxiv.org/abs/2004.09765) | Every nontrivial zero with `0 < abs(t) <= 3*10^12` has `sigma = 1/2`. | Rigorous interval-arithmetic verification of the complete finite-height range. This excludes all off-line candidates there, not just an edge region. Its computation has not been reproduced as a Lean certificate here. |
| [Yang, *Explicit bounds on zeta(s) in the critical strip and a zero-free region*, JMAA 2024](https://arxiv.org/html/2301.03165v2) | `sigma > 1 - log(L)/(21.233*L)` | `abs(t) >= 3`. Explicit higher-derivative exponential-sum bounds and the van der Corput process. |
| [Bellotti, *Explicit bounds for the Riemann zeta function and a new zero-free region*, JMAA 2024, author-uploaded published text](https://www.researchgate.net/publication/378454423_Explicit_bounds_for_the_Riemann_zeta_function_and_a_new_zero-free_region) | `sigma >= 1 - 1/(53.989*L^(2/3)*log(L)^(1/3))` | `abs(t) >= 3`; constant `48.0718` at sufficiently large height. Uniform logarithmic exponential sums, Vinogradov mean values, and nonnegative trigonometric polynomials. |
| [Bellotti, Trudgian and Yang, *Zero-free regions inspired by work of Heath-Brown*, March 2026 preprint, Theorem 1](https://arxiv.org/html/2603.21490v1) | `sigma > 1 - 1/(4.896*L)` | Stated for `t >= 3`. Combines reflection, smoothing and a finite-height argument with a larger-height Littlewood region. |

Use the theorem statement's strict inequality for the 2026 preprint;
its abstract displays a non-strict boundary. Bellotti's published constant
above improves the `54.004` in her original arXiv version. The 2026 paper
also reports thesis improvements, which have not been independently
inspected here and are not added to the checked chain.

The current proved width has the Littlewood shape `A*log(L)/L`, with
coarser coefficient range and an unevaluated threshold. Reproducing
Yang's coefficient and starting height remains separate work. The
Vinogradov--Korobov shape eventually dominates any fixed coefficient
of the Littlewood shape. These comparisons concern
widths adjoining the strip edges, not the exclusion of every off-line zero.

The [sharp Carathéodory slice](zeta-caratheodory-zero-free.md) now applies
Schwarz directly to the normalized analytic residual. This improves its
center derivative constant and the resulting proved coefficient range.
The [full-radius slice](zeta-full-radius-zero-free.md) then passes the
signed bound through zero-free circles approaching the whole strip width,
retaining possible zeros on the outer boundary and the selected correction.
The current [signed angular slice](zeta-signed-angular-zero-free.md)
uses the exact complex boundary moment to retain upper growth on the left
and the actual Euler lower bound on the right. This supplies the stated
coefficient range without changing the selected source or radial correction.
The next change of width shape needs stronger near-one zeta growth;
the uniform exponential-sum and Vinogradov mean-value input in Bellotti's
proof remains a substantive formalization target. We cannot obtain that
input by changing the constants in our current derivative recursion.

For mathematical exploration, the remaining candidate set should satisfy
all applicable established regions. For the kernel-checked proof, each
region used in a terminal inference must first have a Lean proof with its
full dependencies discharged.

In particular, the research domain for a hypothetical right-half zero is
above the verified finite-height range and to the left of every applicable
right edge. The resulting exclusion width is the maximum of the applicable
widths at that height. Preserve whether a maximum is attained by a strict
or closed edge. This research restriction is not yet a Lean theorem over
the combined external results. Our compiled global chain still uses the
repository's proved region and its unevaluated threshold.

## Literature refresh and reusable mechanisms

The September 2026 review retains a height-dependent envelope: take the
largest applicable proved width at each height, with each theorem's
threshold and strict or closed boundary intact. A single named region
need not dominate in every range.

The [March 2026 preprint, Sections 2–3](https://arxiv.org/html/2603.21490v1#S2)
combines smoothing with reflected-zero pairing. Its Fermi factor
`h(u)=1/(1+exp(-(2*sigma-1)*u))` makes the paired boundary transform
recover the nonnegative transform of the unsplit weight. This is a
useful connection to the repository's existing Fermi and Gaussian
identities. Its iterative enlargement argument also explains why using
an existing region can help the next exclusion, without implying that
iteration reaches RH. The paper reports Littlewood and
Vinogradov--Korobov constants `19.62` and `51.34` from
[Yang's 2025 thesis](https://doi.org/10.26190/unsworks/31825), and states a
further classical constant `4.8594` using that input. These remain leads
pending inspection of the thesis's precise theorems and dependencies.
The UNSW catalogue and public-file metadata were retrieved on September
12, 2026; the PDF download returned a server error. No thesis constant is
treated here as independently checked or formalized.

A [September 1, 2026 preprint by Dhiman, Kadiri and Quesada-Herrera](https://arxiv.org/abs/2609.00537)
provides explicit truncated Poisson summation and improved approximate
functional-equation errors. This is a further endpoint and truncation
toolbox to inspect if the eta width cost becomes limiting. Its abstract
does not itself claim a new zero-free region. Neither preprint has been
added as an assumed theorem or a proved repository result.

The [complete canonical-factor and Borel--Caratheodory route](zeta-arbitrary-log-zero-free.md)
has now been implemented at the shrinking radius. Canonical zero removal
preserves boundary norms and increases the center norm, avoiding a product
of inverse zero distances in the residual bound. The exact logarithmic
derivative keeps each pole coupled to its canonical correction; every
other actual local zero then contributes nonnegatively. The full prime
budget divided by logarithmic height tends to `40/(k+2)` at fixed order.
Choosing the order after a target coefficient gives the larger proved
family. The downstream [joint-order proof](zeta-log-log-zero-free.md)
now also controls every moving center and radius cost. The
[signed angular estimate](zeta-signed-angular-zero-free.md) retains the
Euler lower bound on the right semicircle. Its full budget
tends to `140*C*b/pi` for order `floor(log(log(H))/b)`, giving the stated
log-log region whenever `log(2)<b<pi/(140*C)`.

## General width functions, complete bands, and boundaries

`exists_eventual_common_margin_of_antitone` accepts any width `w` that is
positive and decreasing beyond `T`, tends to zero, and has a proved strict
zero-location theorem there. It produces a finite `H0` such that

```text
H >= H0, abs(Im(rho)) <= H  =>  w(H) < Re(rho) < 1-w(H).
```

Zeros below `T` are covered by the existing positive global margin at `T`.
Eventually `w(H)` is smaller than that margin. The proof makes no
logarithmic-shape assumption, and does not drop the low divisor.

`nontrivialZetaZero_common_margin_max` combines two proved common bands by
taking the larger width. The corresponding literal nonvanishing theorem
excludes the closed right edge, explicitly away from the pole.

For a published **open** zero-free region, the surviving zeros may obey
only non-strict bounds. The separate
`exists_eventual_common_weak_margin_of_antitone` preserves that distinction.
`exists_eventual_analytic_discs_of_weak_region` then allows every strictly
smaller closed disc. It does not assert endpoint nonvanishing and does not
impose a fixed fractional loss in the width.

## The actual arithmetic consequence

At `c = 3/2+i*y`, put `H = 2*abs(y)+3`. A positive common margin `m < 1/4`
gives the exact radius

```text
R(y,m) = 1 + min((abs(y)-1)/2, m/2).
```

The pole cap is inactive for `abs(y) >= 3/2`. The factor `1/2` in the margin
comes from the actual doubled argument of the denominator in
`Q(s) = zeta(s)/zeta(2*s)`. The proof checks the entire closed disc,
including both pole exclusions and denominator nonvanishing, before
applying Cauchy's estimate.

For every fixed `0<A<pi/(140*log(2))`, the current region supplies,
above its finite unevaluated threshold,

```text
R_A(y) = 1 + A*log(log(2*abs(y)+3))/(2*log(2*abs(y)+3)).
```

`SquarefreeLogLog.exists_eventual_radius_spec` proves this formula
and analyticity of the literal quotient on a neighbourhood of the whole
disc. Analytic validity is asserted above the coefficient-dependent
threshold. Existing global margins and radii retain their definitions
and all-height theorems.

For all valid finite prime sets `S`, squarefree marks `P`, complex
polynomials `p`, orders `N`, and `0 < r <= R_A(y)`, the actual arithmetic
series satisfies

```text
norm(response(p,S,P,N,c))
  <= C(A,y) * E(S,c,r) * r^(-N) * sum_k norm(p_k)*r^(-k),

E(S,c,r) = max_(s in closedDisc(c,r)) exp(-Re(Phi_2(S,s))),
Phi_2(S,s) = sum_(q in S) q^(-s) - (1/2)*sum_(q in S) q^(-2*s).
```

`SquarefreeLogLog.exists_eventual_response_bound` proves this with
a single constant independent of `r,S,P,p,N`. The original series is
evaluated at `Re(c)=3/2`, where it genuinely converges. Analytic continuation
is used for the Cauchy contour, not to assert convergence of that series
inside the critical strip.

`SquarefreeLogLog.exists_eventual_coefficient_scaled_decay` proves
the strict gain in a directly measurable form: for every two fixed
coefficients `0<=A<B<pi/(140*log(2))`, at sufficiently large `abs(y)`, and every fixed
valid `S,P,p`,

```text
R_A(y) < R_B(y),
(R_A(y))^N * response(p,S,P,N,c) -> 0.
```

The genuine larger disc for `B` pays for the complete geometric scale of
`A`. This does not claim that every finite-order bound improves: the phase
maximum can increase when the radius increases. It also does not make
the prime-set cost uniform for growing `S`. The earlier
[modulated-region instance](../RiemannGaussian/ZetaSquarefreeEulerModulatedRadius.lean)
remains available as proof history.

## Next formalization target

The implemented external toolbox is Yang's classical exponential-sum
strategy, before attempting the complete Vinogradov mean-value machinery.
Its basic sums have logarithmic phase, `exp(-i*t*log(n))`. Differencing
retains `-t*log((n+h)/n)` and each finite overlap. The derivative tests
must keep their scale hypotheses; they cannot be transferred blindly to
arbitrary prime weights or to the fixed-ordinate, growing-moment limit.

The implemented chain and remaining next step are:

1. **Proved:** exact finite shift and correlation identities, the weighted
   van der Corput inequality, its application to the original Dirichlet
   features, and the logarithmic phase's first and second derivatives with
   dyadic derivative bounds. See the
   [weighted differencing proof and scope](weighted-van-der-corput.md).
2. **First-derivative estimate proved:** the actual logarithmic overlaps,
   their full real Dirichlet damping and the resulting finite van der Corput
   bound are now controlled on admissible blocks. See the
   [cancellation proof and parameter range](first-derivative-dirichlet-cancellation.md).
   **Second-derivative estimate proved:** an exact finite partition pays
   for every resonance and gives the classical square-root bound for the
   full damped Dirichlet terms; see the
   [proof and scope](second-derivative-dirichlet-bound.md).
   **All-order recurrence proved:** the finite induction now holds for
   every adaptive cutoff rule, with every derivative condition discharged
   for the original logarithmic phase and full real damping. See the
   [recurrence and scope](all-order-dirichlet-recursion.md).
   **Closed uniform bound proved:** an exact analytic cutoff controls the
   complete recurrence with coefficient `32` at every order. The actual
   dyadic derivative ratio contributes at most `4` in the leading term;
   the full Dirichlet damping is retained. See the
   [power bound and scope](uniform-dirichlet-power-bound.md).
3. **Actual zeta bridge proved:** exact dyadic eta reconstruction, the
   adjacent-ratio tail and an automatic logarithmic cutoff give a full
   finite power bound for zeta, for every derivative-order selection.
   The complete small-block prefix is controlled through its exact
   transition. See the [proof and remaining range](zeta-dyadic-power-bound.md).
   **Complete line estimates proved:** exact adjacent secants and
   all-order comparisons control every transition window and final block.
   The actual zeta bound is `32768/delta_k * abs(t)^alpha_k * log(abs(t))`
   for all `k >= 1`, `abs(t) >= 2`, with `delta_k=(k+2)*alpha_k`.
   See the [complete line proof](zeta-near-one-line-bound.md).
   **Complete positive-log integral and signed windows proved:** the
   [vertical logarithmic bounds](zeta-sech-vertical-bound.md) cover all
   ordinates, retain the order-dependent logarithmic width cost and
   integrate finite signed windows through zeta zeros. The full signed
   limit and the local zero-detection identity remain; the negative
   logarithmic mass is retained explicitly.
   **Gaussian local-disc route proved through Jensen:** the
   [strip localization and local divisor estimates](zeta-gaussian-local-jensen.md)
   preserve the height exponent and pay the actual Euler center cost.
   Complete local multiplicity bounds and each selected logarithmic
   zero-distance term are controlled.
4. **Complete signed source and actual exclusion proved:** canonical
   removal and the analytic logarithm bound the full residual. Each pole
   remains coupled to its correction, preserving nonnegative real zero
   terms and the selected reciprocal-distance source. The actual prime
   phase budget proves eventual width `A/log(abs(t))` for every fixed
   `A>0`. The resulting region now reaches the complete band and marked
   arithmetic disc. See the [proof and scope](zeta-arbitrary-log-zero-free.md).
5. **Joint-order log-log region proved:** the reciprocal width grows
   at a power strictly below one in logarithmic height. Every fixed
   logarithmic correction, the moving Euler center and both oscillatory
   heights are controlled on the same schedule. The actual complete
   budget gives width `A*log(log(abs(t)))/log(abs(t))` for
   `0<A<pi/(140*log(2))`, with coefficient-dependent existential thresholds.
   This now reaches the actual marked arithmetic discs. See the
   [proof and coefficient range](zeta-log-log-zero-free.md).
6. **Remaining:** retain and control the growing-set signed prime
   envelope in the smaller domain, or find a stronger identity for the
   separate ordinary-prime source. Published optimized constants,
   numerical thresholds and Vinogradov--Korobov methods remain external
   tools to assess without importing unproved premises.

The independent signed ordinary-prime lower bound remains the RH
obstruction. The complete squarefree response is a different quantity;
its improved decay does not close that gap. RH remains open.

## Original transport-slice validation

All three modules pass strict direct elaboration and the focused build.
The full warning-as-error build passes all 10,234 jobs. Whole-project
declaration lint and verbose lint of the new modules pass. All 20 new
public theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The generated inventory contains 1,387 project modules, no project axioms
and no placeholder-dependent declarations. These counts describe the
original transport slice; the [signed angular proof](zeta-signed-angular-zero-free.md)
records the current chain and its validation.
