# The remaining minimum-prime correlation

The [count-boundary continuation](zeta-riesz-cardinality-chamber.md) extends
the coefficient calculation to unequal shares and proves the interior
45-prime model's sign transition at `149/215`. Its all-count coherent-mode
probe does not settle the full integrated residue or arithmetic bound.

The retained signed bound is **still open**. This pass checks a specific
possible failure of a modal estimate for the unchanged target

\[
u^{N+1}\bigl(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\bigr).
\]

It neither completes primes nor changes the packet. The existing favorable
[actual five-prime supply](zeta-riesz-signed-cutoff-profile.md) remains valid.
It cannot be used as an extra reserve without accounting for its complement.

## Exact minimum transform

[`ZetaRieszMinimumCollisionAudit`](../RiemannGaussian/ZetaRieszMinimumCollisionAudit.lean)
evaluates a model that retains both choices of a least coordinate. Write
`a=d+i eta`, `b=d-i eta`, with `d>0`. The two chambers are
`x=r,y=r+v` and `x=r+v,y=r`, with `r,v>0`. Factoring their exponentials and
integrating gives the exact factorial minimum transform

\[
M_h=\frac{1}{ab(a+b)^h}.
\]

The Lean definition is the factored chamber integral; `chamber_factor`
checks its original two exponentials. Both chambers are included before
evaluation. Consequently,

\[
(2u)^h M_h=\frac{(u/d)^h}{d^2+\eta^2}.
\]

For `u=10001/20000`, `d=u-1/40000`, `eta=3/500`, Lean proves
`|a|>u`, `|b|>u`, yet the real normalized minimum moment tends to positive
infinity. The separate-leg exponential rate is approximately
`-0.0000219914`; the minimum-moment rate is approximately `+0.0000499963`.
This is an exact **continuum model counterexample** to transferring
separate-leg decay through a minimum. The model omits the Riesz kernel,
owner band, count sum and actual prime measure. It is **not** a
counterexample to the retained signed target.

## Does the original factorial selection exclude the candidate?

An equal-cofactor boundary gives a concrete quantitative test. Keep owner
share `p=21/40`; let `k` cofactor shares all equal `r=(1-p)/k`, with balanced
opposite synthetic mode frequencies. The common real gain is `delta=1/40000`.
These are synthetic mode parameters, not asserted zeros of zeta. Equal logs
describe a continuum boundary, not a squarefree integer with repeated primes.

At the boundary least-order fraction `b`, the three grouped multinomial
shares are `(p,r,1-p-r)`, while the tested order fractions are
`(21/40,b,19/40-b)`. Define their relative entropy `D`. The candidate radial
gain minus this factorial cost is

\[
\Phi=\log\frac{u}{u-\delta(1-p)}-D.
\]

Lean certifies, using rational bounds for logarithms,

| Total count | Boundary | Least share | Proved candidate budget |
| --- | --- | --- | --- |
| 13 | upper, `b=1/25` | `19/480` | `Phi>1/60000` |
| 49 | lower, `b=1/100` | `19/1920` | `Phi>1/50000` |

The numerical values are approximately `2.13632e-5` and `2.31899e-5`.
These are inequalities between explicit real numbers, **not** proved
asymptotics for a response. In particular they omit the oscillatory residue
and the signed integration across count classes.

The Riesz factor is not pointwise zero at these boundaries. At the strict-core
ratio `lambda=693/1000`, the existing finite-difference kernel is exactly

\[
H_k(d;r,\ldots,r)=\sum_{j=0}^k(-1)^j\binom{k}{j}(d-jr)_+,
\quad d=\lambda-21/40.
\]

`kernel_equal_shares` proves this is the existing kernel with every subset
sign. Lean evaluates `H_12=-39/25` and proves `H_48>0`. A nonzero value
at a point still does not establish a nonzero integrated collision residue.

There is also an interior candidate at total count 45: the owner share is
`14/25`, and its 44 cofactor shares are exactly `1/100`. The grouped
multinomial order fractions equal their share parameters, so their relative
entropy is **exactly zero**. Lean proves that for every `0<delta<u` the
candidate budget `log(u/(u-(11/25)*delta))` is positive. Thus reducing the
radius interval alone cannot make every such budget negative. At the same
rational `lambda`, Lean evaluates this kernel as `106328047/125>0`.
This remains a candidate-rate audit, not an integrated-response theorem.

## Numerical regression and exact remaining test

The optional [probe](../scripts/probe_riesz_minimum_collision.py) and
[report](riesz-minimum-collision-probe.json) check the two-chamber integral
with 90-digit quadrature. They separately evaluate the original two beta
faces, including the `+1` least-order shift and the complete owner-order
band, through `N=1048576`. The radial saddle is recomputed; it is not frozen
at `2N`. The original moving floor length is used at small orders and a
proved `4/X_N` length enclosure at large orders. Floating-point face values
and quadrature checks are not interval certificates.

The [renewal-curvature audit](zeta-riesz-renewal-curvature.md) now resolves
the sign of one selected-background pair coefficient. The remaining test is
**the coefficient of the collision contribution in the
whole joined response**, after summing marked incidences, both least-order
faces and counts 3–55. It must retain the prime-density denominators and every
Riesz subset sign. Either that coefficient cancels exactly, or it requires a
new estimate using actual prime/zero information. A positive candidate rate
alone is not permission to abandon the route, and a small finite numerical
response is not evidence that this coefficient vanishes.

There is no claim here that a pole at an averaged denominator survives that
complete calculation. Nor is there a new independent floor, zero exclusion,
or proof that the arithmetic target is impossible.

## Summed balanced cones

The new `collisionChambers_eq` theorem evaluates the factored orthant
Laplace integrals after summing **every** least-coordinate incidence:

\[
\sum_{j\in S}\prod_{i\ne j}
  \int_0^\infty e^{-a_i v}\,dv
=\frac{\sum_{j\in S}a_j}{\prod_{i\in S}a_i},
\qquad \Re a_i>0.
\]

For `m` copies each of `a+i*eta` and `a-i*eta`, this is
`2*m*a/(a^2+eta^2)^m`. In the fixed-total coordinate map
`x_i=(s-sum y)/(2m)+y_i`, the Jacobian is `1/(2m)`.
`chamber_jacobian` proves that determinant by the matrix determinant lemma.
`diagonalCone_eq` and `diagonalCone_re_pos` therefore give the strictly
positive cone factor

\[
\boxed{\mathcal C_m(a,\eta)=\frac{a}{(a^2+\eta^2)^m}>0.}
\]

This formula also gives the algebraic scaling
`C_m(N*a,N*eta)=N^(-(2m-1))*C_m(a,eta)` for `N>0`.
The 12- and 48-leg cones therefore carry powers `N^-11` and `N^-47`,
before any further prefactors. Small finite-order model values cannot
decide whether their positive candidate exponential budgets eventually
win. This scaling is not an asymptotic formula for the complete response.

This is an exact finite integral calculation, **not** a proved asymptotic
expansion of the carrier. The factored chambers are the definition of the
model integral; neither a multivariable change of variables for the actual
masked sum nor its arithmetic transport is assumed.

The real normal slope is derived from the correlated factorial profile,
not from an independent least-slot approximation. Write `s=1-p`, let `b`
be the least-order fraction, and let `q` denote total excess above the
equal-cofactor corner. The varying part of that profile is

\[
\Psi(q)=b\log\frac{s-q}{k}
 +(s-b)\log\left(s-\frac{s-q}{k}\right),
\qquad
-\Psi'(0)=\frac{kb-s}{(k-1)s}.
\]

`factorialProfile_hasDerivAt` proves this derivative. At owner share
`p=21/40`, `boundary_normal_slopes` gives:

| Original boundary | Cofactor count | Least-order fraction | Normal slope |
| --- | ---: | ---: | ---: |
| Upper | 12 | `1/25` | `1/1045` |
| Lower | 48 | `1/100` | `1/4465` |

`upper_kernel_negative_on_window` and `lower_kernel_positive_on_window`
retain every Riesz subset sign and prove the two kernel signs on
`693/1000<=lambda<=694/1000`. The second proof crosses the seventeenth
hinge without dropping it. `source_ratio_window` places `-2*u*log u`
in that interval for the whole original restricted radius range.

Consequently `paired_face_cones_window_neg` proves, for **any** positive
real amplitudes `A,B`,

\[
A H_{12}(\lambda-21/40;19/480)\,\mathcal C_6(1/1045,\eta)
-B H_{48}(\lambda-21/40;19/1920)\,\mathcal C_{24}(1/4465,\eta)<0.
\]

Here the minus sign in the second term includes the owner's negative mode;
the upper factorial boundary has the opposite subtraction, leaving the
first term with the displayed plus sign. Thus these two cone factors
reinforce, rather than cancelling each other. The positive amplitudes are
model weights, not assumed nonzero residues of the actual prime sum.

**The unresolved step is precise:** prove or refute the passage from these
local cone integrals to the full moving radial/factorial response, including
other corners and all other count/mode assignments. The actual prime measure
and the complementary carrier's signed floor remain further obligations.
Neither this calculation nor the candidate positive exponent establishes
divergence of the full model, let alone of the literal prime sum.

## Literature applicability checks

The [higher-order Alladi–Sengupta dualities](https://arxiv.org/html/2604.17832v1)
give exact signed divisor identities involving ordered prime factors and
prime-count weights. Their stated quantitative asymptotics do not retain our
joint factorial/Riesz masks. Applying the unweighted identity would therefore
leave a weighted error requiring an estimate; it does not pay this target.

[Alamoudi's subradically sifted sums, Theorem 1.1](https://arxiv.org/html/2601.10636v1)
give quantitative higher-order Möbius estimates only for
`y <= Y0 exp(p log x/(log log(x+1))^(1+epsilon))`, with fixed parameters.
Our retained minimum-prime share is bounded below by a fixed positive
constant, so its cutoff `y=x^c` eventually lies outside that range. This
range comparison is our applicability inference. The paper also gives a
general-range bound in Theorem 5.1, but it supplies no fixed power saving
and does not retain the factorial/Riesz weights or complex phase. Neither
theorem closes the signed target as presently stated.

As a separate possible escape, a genuinely bounded-step rightward-zero chain
would conflict with a sublinear zero count. Such counts follow from classical
zero-density results, including the
[explicit Ingham estimate](https://arxiv.org/html/2507.15184v1). That density
theorem is not imported here, and we have not shown that the full masked
response supplies a successor with a uniformly bounded height step. The prior
multi-mode chain counterexample remains valid. This observation is not a
replacement proof or a new zero-location theorem.
