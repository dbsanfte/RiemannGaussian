# Vinogradov–Korobov formalization: centered Gaussian resonance

**Status:** the exact finite logarithmic expansion, product-shift averaging
of actual Dirichlet blocks, transport through their full damping, shifted
moment domination and the two-Hölder reduction of the actual polynomial
sum are proved.
The Vinogradov–Korobov zeta growth estimate
and zero-free region remain unproved in this repository. No external
analytic estimate is installed as an axiom or as a claimed discharged premise.

The research lead is [Bellotti (2023), Section 8](https://arxiv.org/html/2306.10680v1#S8).
That argument connects shifted logarithmic sums to polynomial phases and
then uses high mean-value estimates. The current implementation closes the
averaging, phase approximation, damping transport and moment reduction;
the quantitative high-moment estimates remain open.

## Exact signed expansion

For every natural degree `k` and **every `x ≥ 0`**, define

```math
P_k(x)=\sum_{j=0}^{k-1}\frac{(-1)^j x^{j+1}}{j+1},
\qquad R_k(x)=\int_0^x\frac{u^k}{1+u}\,du.
```

[VinogradovKorobovLogPhase](../RiemannGaussian/VinogradovKorobovLogPhase.lean)
proves the exact identity and bounds

```math
\log(1+x)=P_k(x)+(-1)^kR_k(x),\qquad
0\le R_k(x)\le\frac{x^{k+1}}{k+1}.
```

The proof uses an exact recurrence for consecutive integrals, not a
convergence assumption at a series endpoint. The companion complex identity
keeps `exp(-it*(-1)^k*R_k(x))` as a separate factor before bounding its effect.

## Literal powers and coupled products

[VinogradovKorobovBilinearPhase](../RiemannGaussian/VinogradovKorobovBilinearPhase.lean)
identifies the actual power `(z+a*b)^(-it)` for `z>0`, `a,b≥0` with its
unit base phase and `exp(-it log(1+a*b/z))`. The polynomial phase is exactly

```math
-tP_k(ab/z)=\sum_{j=0}^{k-1}
\frac{-t(-1)^j}{(j+1)z^{j+1}}a^{j+1}b^{j+1}.
```

For arbitrary finite complex weights `w(a,b)`, the error between the whole
logarithmic sum and the whole polynomial sum is at most

```math
\sum_{a,b}|w(a,b)|\,
\frac{|t|(ab/z)^{k+1}}{k+1}.
```

Both factors, every weight and the complete polynomial sum survive. The
proof reuses the repository's unit-phase Lipschitz theorem from
[EtaCubicBoundaryTest](../RiemannGaussian/EtaCubicBoundaryTest.lean).
The unweighted version pays the explicit cardinality and box sizes.

## Actual blocks, exact boundaries and the remaining polynomial sum

[VinogradovKorobovBlock](../RiemannGaussian/VinogradovKorobovBlock.lean)
proves an exact product-shift identity for every real `z>0`, every real
height `t`, integer block length `L`, and finite integer shift sets `A,B`.
Write `m=|A||B|`, `f(n)=(z+n)^(-it)` and

```math
C_p=\sum_{j<p}f(j)-\sum_{j<p}f(L+j),\qquad
C=\sum_{a\in A,b\in B}C_{ab}.
```

The theorem `averaged_dirichlet_identity` keeps the original signed boundary:

```math
m\sum_{n<L}f(n)=
\sum_{n<L}e^{-it\log(z+n)}
  \sum_{a\in A,b\in B}e^{-it\log(1+ab/(z+n))}+C.
```

Replacing only the inner logarithmic phases by their degree-`k` polynomials
gives `Q_k`. The outer phases remain coupled. For nonempty shift sets with
`0≤a≤M₁`, `0≤b≤M₂`, put

```math
E=\frac{|t|}{k+1}\left(\frac{M_1M_2}{z}\right)^{k+1},\qquad
F_L=\frac{Q_k+C}{m}.
```

`block_sub_approximation_le` proves the complex approximation
`|sum_(n<L) f(n)-F_L|≤L E`. This includes the exact boundary before the
error is bounded. `dirichlet_norm_le_coupled` retains `Q_k+C` under one norm;
`dirichlet_norm_le` separately pays

```math
\frac{|C|}{m}\le
2\left(\frac{\sum_{a\in A}a}{|A|}\right)
 \left(\frac{\sum_{b\in B}b}{|B|}\right).
```

Thus the boundary allowance uses the actual mean shifts, and the exact
signed expression remains available upstream. All endpoints are integers
with an explicit half-open block convention. The identities hold even
when a shift exceeds the block length; no omitted rounding correction or
small-ratio assumption is needed. A separate exact identity also allows
arbitrary complex shift weights.

[VinogradovKorobovDamping](../RiemannGaussian/VinogradovKorobovDamping.lean)
then applies exact Abel summation. For any nonnegative decreasing weights
`w_n`, the weighted approximation formed from the prefixes `F_l` satisfies

```math
\left|\sum_{n=0}^{N}w_n f(n)-
\left(w_N F_{N+1}+\sum_{n<N}(w_n-w_{n+1})F_{n+1}\right)\right|
\le E\sum_{n=0}^{N}w_n.
```

`feature_approximation_error_le` discharges the weight conditions for the
literal `zetaPrimeFeature s (a+n)`, for every positive integer `a` and
`Re(s)≥0`. The allowance pays its actual damping mass. This connects the
product-phase argument to the Dirichlet terms already used by the zeta
chain; it does not yet bound the surviving polynomial approximation.

## Exact mean values and their arithmetic correlations

[VinogradovMeanValue](../RiemannGaussian/VinogradovMeanValue.lean) proves,
for every finite family of integer frequency vectors `v_i`,

```math
\int_{(\mathbb R/\mathbb Z)^d}
\left|\sum_i e^{2\pi i\langle v_i,\alpha\rangle}\right|^{2s}d\alpha
=\#\left\{(x,y):\sum_{j=1}^s v_{x_j}=\sum_{j=1}^s v_{y_j}\right\}.
```

The monomial vector `(n,n²,...,n^k)` gives the actual Vinogradov
mean value on `1,...,N`. The torus expression is explicitly identified
with the usual polynomial-exponential integral on the unit cube. For
`k≥1`, the first mean value is proved to equal `N` exactly.

The upstream weighted identity keeps all matching-frequency cross terms,
`w_i*conj(w_j)`. Thus later bounds can use the actual frequency collisions
rather than assume independent phases. This is the classical moment/count
identity, not a new quantitative saving or a historical novelty claim.

## Shifted correlations and bounded complex weights

[VinogradovShiftedMoment](../RiemannGaussian/VinogradovShiftedMoment.lean)
identifies the entire complex coefficient

```math
G_w(h)=\sum_{v_i=v_j+h}w_i\overline{w_j}
=\int_{(\mathbb R/\mathbb Z)^d}
 \left|\sum_i w_i e^{2\pi i\langle v_i,\alpha\rangle}\right|^2
 e^{-2\pi i\langle h,\alpha\rangle}\,d\alpha.
```

It proves `|G_w(h)|≤G_w(0)` for every integer vector `h`. Applied to tuple
frequencies, this gives

```math
\#\{(x,y):\sum_jv_{x_j}-\sum_jv_{y_j}=h\}\le J_s(v).
```

The weighted even moment, and the norm of each of its shifted Fourier
coefficients, are also bounded by `J_s(v)` whenever every `|w_i|≤1`.
These are integral and correlation bounds; the original complex weights
remain in the exact expansion. `monomial_shift_le_meanValue` specializes
to the literal equal-power-sum system on `1,...,N`.

## Two Hölder steps for the actual product polynomial

[VinogradovMomentReduction](../RiemannGaussian/VinogradovMomentReduction.lean)
proves the finite reduction underlying
[Ford, Lemma 5.1, equation (5.3)](https://arxiv.org/pdf/1910.08209v1).
For any finite integer-frequency family `v_a` and torus samples `theta_b`,
let

```math
U=\sum_b\sum_a e^{2\pi i\langle v_a,\theta_b\rangle},\qquad
\mathcal C_r=\left\{\sum_{j=1}^r v_{a_j}\right\}.
```

For `F_b = sum_a exp(2*pi*i*<v_a,theta_b>)`, the weights are explicitly
`epsilon_b = |F_b^r| / F_b^r`, with value zero when `F_b=0`.
`two_holder_bound` keeps this formula in its statement, so later arguments
can use the weights' dependence on the original phases. Lean proves
`|epsilon_b|≤1` and, for every `r,s≥1`,

```math
|U|^{2rs}\le
|B|^{(r-1)2s}|A|^{r(2s-2)}J_r(v)T_{r,s},\qquad
T_{r,s}=\sum_{c\in\mathcal C_r}
 \left|\sum_b\epsilon_b e^{2\pi i\langle c,\theta_b\rangle}\right|^{2s}.
```

The literal multiplicity `n(c)` satisfies `sum n(c)=|A|^r` and
`sum n(c)^2=J_r(v)`. Both identities are proved. The support is the **joint
set of attainable tuple frequencies**, so its coordinate correlations
remain available before any later rectangular enlargement.

[VinogradovKorobovMoment](../RiemannGaussian/VinogradovKorobovMoment.lean)
identifies the original product polynomial with precisely these samples:

```math
v_a=(a,a^2,\ldots,a^k),\qquad
\theta_{b,j}=\frac{(-1)^j t\,b^j}{2\pi j z^j}\pmod1
\quad(1\le j\le k).
```

`polynomial_bound` applies to arbitrary finite shift sets, and
`interval_bound` uses the existing literal `meanValue r k M` on
`1,...,M`. The coefficient vector is exact; no rational approximation or
phase-independence premise is introduced. A saving still requires
quantitative bounds for `T_(r,s)` and `J_r`.

## Gaussian smoothing with the complete signed correlations

[VinogradovGaussianKernel](../RiemannGaussian/VinogradovGaussianKernel.lean)
now proves a Gaussian bound for that actual dual moment. Choose arbitrary
positive scales `a_j`. Put

```math
g_a(n)=\exp\!\left(-\pi\sum_j a_j n_j^2\right),\qquad
K_a(x)=\prod_j\left\{a_j^{-1/2}
  \sum_{m\in\mathbb Z}e^{-\pi(m-x_j)^2/a_j}\right\}.
```

Lean proves genuine absolute convergence on the full integer lattice,
then obtains the exact multivariate Poisson identity

```math
\sum_{n\in\mathbb Z^k}g_a(n)e^{2\pi i\langle n,x\rangle}=K_a(x).
```

The scalar transformation uses Mathlib's proved Gaussian Poisson theorem.
The product construction, translated spatial series and all sum exchanges
are checked here; the spatial kernel is proved strictly positive. Every
integer translate and every coordinate of `x` is retained.
For arbitrary complex weights, the exact Gram identity is

```math
\sum_n g_a(n)\left|\sum_b w_b e^{2\pi i\langle n,x_b\rangle}\right|^2
=\sum_{b,c}w_b\overline{w_c}\,K_a(x_b-x_c).
```

The left side is nonnegative; **individual cross terms on the right can
have either sign or be complex**. Positivity of the spatial kernel does
not justify deleting them. The theorem keeps their full complex sum.

For the original support `C_r`, define its exact finite maximum cost

```math
Q_a(\mathcal C_r)=\max\!\left(\{0\}\cup
 \left\{\pi\sum_j a_j c_j^2:c\in\mathcal C_r\right\}\right).
```

For ordered tuples `b=(b_1,...,b_s)`, write
`W_b=prod_l epsilon_(b_l)` and `X_b=sum_l x_(b_l)`. The compiled theorem
`dualMoment_le_gaussian_gram` proves

```math
T_{r,s}\le e^{Q_a(\mathcal C_r)}
 \operatorname{Re}\sum_{b,c}W_b\overline{W_c}\,K_a(X_b-X_c).
```

The Gaussian factor pays for the full support majorization. There is no
unproved cost premise: `supportCost` is computed from the literal finite
support, including the empty case. The Gaussian majorant adds weighted integer frequencies outside that
support; the original restricted moment remains available upstream in
`dualMoment`. Its maximum cost does not retain the support's holes or
multiplicities. The bound holds for every positive scale vector and
every complex weight family.

`VinogradovKorobovMoment.interval_gaussian_bound` composes this with the
two Hölder steps for the **actual interval product polynomial**, retaining
the exact sample coordinates above and the explicit phase-dependent
alignment weights. Its two remaining factors are the homogeneous mean
value and this complete signed Gaussian tuple Gram form. Near-integer
differences of the actual polynomial coordinates are now visible to an
independent spacing or correlation estimate. No such saving, or historical
novelty of the Gaussian identities, is claimed by this formalization.

## Complete power-sum difference fibres

[VinogradovGaussianResonance](../RiemannGaussian/VinogradovGaussianResonance.lean)
now groups that same Gram form by the full integer vector

```math
h=\sum_{\ell=1}^s v_{b_\ell}-\sum_{\ell=1}^s v_{c_\ell},\qquad
\mathcal D_s(v)=\{\text{all such }h\}.
```

For samples `x_b=gamma*v_b`, with coordinatewise multiplication, the
exact identity is

```math
G_s=\sum_{h\in\mathcal D_s(v)}C_w(h)K_a(\gamma h),\qquad
C_w(h)=\sum_{\substack{b,c\\\sum v_b-\sum v_c=h}}
  W_b\overline{W_c}.
```

`momentGram_eq_fibres` retains each complete complex coefficient `C_w(h)`.
The original polynomial samples have exactly this form;
`coordinates_eq_linearSample` proves it using their literal coefficients.
For every bounded complex weight family, the already proved shifted-count
majorant gives `|C_w(h)|≤J_s(v)`. The downstream theorem therefore proves

```math
\operatorname{Re}G_s\le J_s(v)\,\mathcal R_s(a,\gamma,v),\qquad
\mathcal R_s=\sum_{h\in\mathcal D_s(v)}K_a(\gamma h).
```

All coordinates, attainable differences and Gaussian translates remain in
`R_s`. Taking norms of the fibre coefficients loses their relative phases;
the exact signed identity remains available for a sharper estimate.
`interval_resonance_bound` now places the **actual interval product sum**
below its explicit cardinality factors, Gaussian support cost, both
homogeneous moments and this one joint resonance sum. No spacing premise
or unproved mean-value estimate is assumed in that reduction.

## Explicit translated tails and a centered support

[VinogradovGaussianBounds](../RiemannGaussian/VinogradovGaussianBounds.lean)
pays the complete one-coordinate translated series. With `r=fract(-x)`,
the uniform bound is

```math
K_a(x)\le E_a(x):=
\frac{e^{-\pi r^2/a}+e^{-\pi(1-r)^2/a}}
 {\sqrt a\,(1-e^{-\pi/a})},\qquad a>0.
```

The proof uses Mathlib's geometric bounds for the periodic Hurwitz
Gaussian kernel. Every translate is covered by the denominator, which is
proved strictly positive. The result holds for all real `x` and all
positive `a`, so it applies to phases changing with the height and the
original polynomial coefficients. For `d(x)=min(r,1-r)`, Lean also proves

```math
K_a(x)\le
\frac{2e^{-\pi d(x)^2/a}}{\sqrt a\,(1-e^{-\pi/a})}.
```

The full resonance sum is therefore bounded by the finite expression
`sum_(h in D_s) prod_j E_(a_j)(gamma_j h_j)`. Its entire joint attainable
support remains intact; it still needs an arithmetic spacing estimate.

[VinogradovGaussianCentering](../RiemannGaussian/VinogradovGaussianCentering.lean)
also permits centering the Gaussian on the actual support. For any integer
vector `m`, the exact complex identity is

```math
\sum_b w_b e^{2\pi i\langle c,x_b\rangle}
=\sum_b \bigl(w_b e^{2\pi i\langle m,x_b\rangle}\bigr)
 e^{2\pi i\langle c-m,x_b\rangle}.
```

Every weight keeps its norm, and its forced phase twist stays in the
signed Gram theorem. The downstream bounded-weight resonance majorant
can thus pay `Q_a(C_r-m)` while retaining the same resonance envelope.

For the actual interval `1,...,M`, the coordinate endpoints are
`r` and `r M^j`. The canonical integer midpoint is
`m_j=floor((r+r M^j)/2)`. Lean proves all rounding allowances and

```math
Q_a(\mathcal C_r-m)
\le\pi\sum_{j=1}^k a_j
 \left(\frac{rM^j-r+1}{2}\right)^2
\le\frac14 Q_a(\mathcal C_r),\qquad r,M\ge1.
```

Here the original maximum is exactly
`Q_a(C_r)=pi sum_j a_j (r M^j)^2`, attained by the all-upper-endpoint
tuple. `interval_quarter_envelope_bound` applies this improvement to the
literal product sum. This quarters the **Gaussian exponent cost**; it
does not quarter the whole estimate, establish the needed arithmetic
power saving, or enlarge the current zero-free region.

## Remaining analytic proof obligations

The averaging, boundary, Taylor and damping steps, shifted-moment majorants
and two-Hölder reduction are now proved for the actual terms, followed by
the complete Gaussian smoothing, centered exponent improvement and explicit
weighted-fibre and tail bounds. The next missing
step bounds the joint resonance sum through coefficient spacing, together
with quantitative homogeneous mean-value estimates for both factors. The
stronger signed fibre identity also remains available. Preserve
the exact alignment weights and coordinate correlations while developing
that estimate. The identities and smoothing bound alone give no
power saving. Quantitative
mean-value estimates must imply the required logarithmic exponential-sum
saving, then a proved near-one zeta growth estimate, then the zero detector
with all constants and height ranges paid. These are substantial analytic
obligations, not just numerical constant checks.

Only after that chain is discharged can a VK width join the
[complete proved region](zeta-unified-zero-free.md). Comparisons between
benchmark width functions do not supply their analytic proofs. Consult the
[literature-frontier audit](zero-free-literature-frontier.md) for source
versions and reported constants; no world-best claim follows from the
present approximation and exact-moment theorems.
