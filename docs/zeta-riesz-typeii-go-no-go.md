# Harmonic Type-II route: quantitative go/no-go audit

21 September 2026. **Decision: no-go with the presently proved inputs.**
The sufficient quantitative reduction is now formalized. Its localized
arithmetic estimate is not proved here or supplied by the audited literature.
Stop expanding this route until an independent estimate for that input is
available. This supersedes the exploratory recommendation in the
[preceding literature audit](zeta-riesz-next-path-literature-audit-2026-09-21.md).

This is an applicability verdict, not a theorem that cancellation is
impossible, an equivalence to RH, or a new zero-free region.

## The exact sufficient statement

Fix

\[
\frac12<u\le U=\frac{5001}{10000},\qquad y\in\mathbb R.
\]

Keep the original schedule \(N=N_j\), \(K=K_j\), physical length \(L=L_N\),
prime allocation \(\theta_N(n)\), and all masks of `nondominantBand`.
Intersect that set with

\[
\frac{39}{20}N<\log n\le\frac{41}{20}N.
\]

Let \(S_{N,k}\) be its further intersection with \(k\le\log n<k+1\).
The prime-count restrictions, central unpaired mask, cancelling-sector
deletion and dominant-prime deletion remain. On nonzero surviving labels
the existing theorem still gives \(\log p<(13/20)\log n\).
Nonsquarefree labels have identically zero original coefficients.

For \(n=pqa\), with distinct primes \(p,q\) and squarefree \(a>1\) coprime
to both, define the **full** discrepancy

\[
\begin{aligned}
E_{L,p,q}(a)
 &=\mathcal R_{L-\log p}(a)+\mathcal R_{L-\log q}(a)
     -\mathcal R_L(a)-\Lambda(a),\\
\Delta_{L,p,q}(a)
 &=\Lambda(a)-\mathcal R_{L-\log p-\log q}(a)+E_{L,p,q}(a).
\end{aligned}
\]

The checked identity is

\[
c_L(pqa)=\frac{\log(pqa)}{L}\Delta_{L,p,q}(a).
\]

Put

\[
A_{N,k}=\frac{(k+1)^N}{N!}e^{-3k/2},\qquad
w_{N,k}(n)=
 \left(\frac{\log n}{k+1}\right)^N e^{-3(\log n-k)/2}.
\]

The exact original kernel is \(A_{N,k}w_{N,k}(n)e^{-iy\log n}\), with
\(0\le w_{N,k}\le1\) on its cell. Lean defines `cellKernel` by dividing
the literal original kernel by \(A_{N,k}>0\), and proves its norm is at
most one. The factorial is accounted for exactly, not silently omitted.

The literal finite form is

\[
\mathcal T_{N,k}=
\sum_{\substack{n\in S_{N,k}\\n\ {\rm squarefree}}}
\ \sum_{\substack{p,q\mid n\\p,q\ {\rm prime}\\p\ne q}}
\frac{1-\theta_N(n)}{\omega(n)(\omega(n)-1)}
\frac{\log n}{L}
\Delta_{L,p,q}\!\left(\frac{n}{pq}\right)
w_{N,k}(n)e^{-iy\log n}.
\tag{T}
\]

This divisor-incidence parametrization is trilinear in \((p,q,a)\) with
\(pqa=n\). `primePair_data` and `primePair_cofactor` prove its product,
coprimality, squarefreeness and nonunit conditions. Ordered pairs are
averaged, not counted with multiplicity. The masks and allocation depend
jointly on the product and its factors: “Type-II” does **not** assert
that the form already satisfies separated rectangular coefficient hypotheses.

The named open hypothesis, `LocalizedTypeIIBound u y`, is: there exist fixed
\(C\ge0\), \(A\in\mathbb N\), allowed to depend on \(u,y\), such that
eventually along the **original** schedule, for every \(k<3N+1\),

\[
\boxed{
|\mathcal T_{N,k}|\le C(N+1)^A e^{(999/1000)k}
       =C(N+1)^A x^{1-1/1000},\qquad x=e^k .
}
\tag{II}
\]

This is passed explicitly to the reduction. It is not an axiom, an imported
result, or a premise absorbed into a definition of the floor.
Empty cells contribute zero.

## The checked quantitative implication

Exact reconstruction and the exponential-series inequality give

\[
R_j^{\rm narrow}
 =u^{N+1}\sum_{0\le k<3N+1}A_{N,k}\mathcal T_{N,k},\qquad
A_{N,k}e^{(999/1000)k}\le e^{501/1000}(1000/501)^N.
\]

Consequently (II) implies the explicit finite estimate

\[
\boxed{
|R_j^{\rm narrow}|
\le 3CUe^{501/1000}(N+1)^{A+1}
       \left(\frac{1667}{1670}\right)^N
\longrightarrow0 .
}
\]

The ratio \(1667/1670=U/(1/2+1/1000)<1\) is checked with exact rational
arithmetic. The triangle inequality is applied to **complete signed cell
sums after (II)**, never to their individual arithmetic terms.

Independently of (II) and any zero hypothesis, one \(r<1\) and a finite
\(C_0\) bound the entire discarded window by \(C_0r^N\), uniformly in
height, count cutoff and \(0\le u\le U\). Thus

\[
R_j-R_j^{\rm narrow}\longrightarrow0,\qquad
\text{(II)}\Longrightarrow R_j\longrightarrow0
\Longrightarrow \operatorname{Re}R_j\ge-3/40\quad\text{eventually}.
\]

| Compiled declaration | Role |
| --- | --- |
| [`exists_narrow_window_error`](../RiemannGaussian/ZetaRieszTypeIILocalization.lean) | Independent geometric bound for both discarded tails |
| [`coefficient_prime_minus_hinge`](../RiemannGaussian/ZetaRieszPairDiscrepancy.lean) | Short identity with its necessary saturation hypotheses |
| `pairForm_eq_sum` in the same module | Full correction and exact incidence normalization |
| [`norm_narrow_of_typeII`](../RiemannGaussian/ZetaRieszTypeIIReduction.lean) | Explicit numerical transport from (II) |
| `eventually_signed_floor_of_typeII` in the same module | Requested floor for the original carrier |
| `not_typeII_of_simple_exposed_zero` in the same module | Contradiction between (II) and the existing source |
| [`logarithmic_envelope_eventually_exceeds`](../RiemannGaussian/ZetaRieszTypeIIRateAudit.lean) | Fixed logarithmic errors cannot imply this power-saving envelope |
| `fixed_height_outside_repo_vmvt` in the same module | Existing rectangle is unavailable cofinally at fixed height |

The conditional exclusion concerns **simple exposed zeros** with
\(0.9999\le\operatorname{Re}\rho<1\), since \(u=3/2-\operatorname{Re}\rho\).
It neither removes simplicity/exposure nor covers all right-half zeros.
No converse from zero exclusion to (II) is asserted: this cellwise norm
estimate is stronger than the required one-sided floor.

## Why the shorter discrepancy is insufficient

The correction vanishes when

\[
\log a\le L-\log p,\qquad \log a\le L-\log q.
\]

Both marked prime logarithms must therefore be at least \(\log n-L\).
Balanced triples satisfy this in the relevant regime, with all three
unordered pair choices potentially qualifying. The six ordered choices
explain the incidence denominator.

The support restrictions do not imply saturation for all prime counts.
Near the middle of the window, four approximately balanced prime factors
have logarithms near \((\log n)/4\), below the reflected cutoff near
\(0.307\log n\). `no_saturated_pair_of_small_primes` checks the underlying
scalar implication; it is not an existence theorem for primes in
asymptotic boxes.

No independent source-scale bound for the unsaturated correction was found.
Accordingly (T) retains it **inside the same estimate**. A bound just for
\(\Lambda-\mathcal R\) on the saturated subfamily does not instantiate
the floor theorem.

## Literature hypotheses

**Friedlander–Iwaniec, _Asymptotic sieve for primes_, Theorem 1.**
The inputs include a nonnegative sequence, a multiplicative density model,
distribution remainder condition (R) beyond \(x^{2/3}\), and a separate
signed bilinear condition (B). Its coefficient
\(\gamma(n,C)=\sum_{d\mid n,d\le C}\mu(d)\) resembles the integrated hinge.
The theorem does not prove (B). Its stated logarithmic errors do not give
(II). We have not verified its distribution model or full bilinear range
for these masks. Their Liouville example explains why Type-I information
alone is insufficient.
[Primary paper, conditions (R), (B), (B1)–(B3), pp. 1043–1045](https://arxiv.org/pdf/math/9811186).

**Bombieri-style generalized Selberg identities, in Ramaré's explicit
formulation.** Theorems 1–2 compare a sequence with a model under
(H1)–(H5)/(H8); the main term still needs evaluation. Complex oscillation
can be handled through suitable nonnegative comparisons, with their
hypotheses retained. Growing-order costs are explicit, including
\(\delta\le1/(4\nu)\) and
\(\nu^2\delta\log(1/\delta)\le1/6\). No verified choice for our moving masks
and order supplies (II).
[Primary paper, sections 1–2](https://ramare-olivier.github.io/Maths/V12BombieriSieve.pdf).

**Ford–Maynard, _On the theory of prime-producing sieves_.**
This framework optimizes conclusions from specified Type-I/II information;
it does not supply those inputs for a new sequence. Introduction (I) and
(II) concern a sequence-minus-model discrepancy. No checked model,
required range or fixed power error is available for (T).
[Primary paper, introduction and section 4](https://arxiv.org/html/2407.14368v1).

Our inference is limited: (II) is a **new parity-sensitive cancellation
input with at least the restricted exclusion strength proved above**.
We have not shown equivalence to classical sieve axioms or full RH.
Nor have we proved that its natural main term vanishes unconditionally.
A source identity cannot replace that evaluation.

## Existing tools: applicability audit

| Tool | Checked capability | Missing requirement for (T) |
| --- | --- | --- |
| [Vinogradov Dirichlet saving](../RiemannGaussian/VinogradovDirichletSaving.lean) | Unweighted blocks at fixed degree \(d\ge12\), with \(M^{2d-2}\le |y|\le M^{2d}\) | At fixed \(y\), the lower-height premise eventually fails. Prime/sieve weights are also absent from that theorem. |
| [Damped Vinogradov transport](../RiemannGaussian/VinogradovDampedSaving.lean) | Nonnegative decreasing amplitudes on those rectangles | Allocation, prime-count masks and signed sieve coefficients do not form such an amplitude. |
| [Multiplicative phase transport](../RiemannGaussian/ZetaMultiplicativePhase.lean) | Exact phase factorization; all-coefficient norm bounds are equivalent at every height | \((pqa)^{-iy}=p^{-iy}q^{-iy}a^{-iy}\) can be absorbed into coefficients. Actual prime/Möbius correlations are still needed. |
| [Weighted differencing](../RiemannGaussian/ZetaFiniteDifferencing.lean) | Exact signed shift correlations and an inequality using them | The weighted correlations of (T) have no independent sufficient bound. |
| [Montgomery–Vaughan interface](../RiemannGaussian/MontgomeryVaughan.lean) | Separated-frequency quadratic estimates | No reduction pays the actual near-diagonal arithmetic correlations at the required fixed height and rate. |
| [Möbius resonance decay](../RiemannGaussian/ZetaMoebiusResonanceDecay.lean) | Independent decay outside shrinking resonant interactions | The source survives inside the resonant part; the theorem does not bound (T). |
| [Joint cofactor estimate](../RiemannGaussian/ZetaRieszJointCofactor.lean) | One-prime wing plus its complete composite companion | The new pair correction and prime response are not covered by that estimate. |

Two failures are now Lean theorems:

\[
\frac{e^t/t^B}{e^{999t/1000}}=\frac{e^{t/1000}}{t^B}\longrightarrow+\infty,
\qquad
\forall y,\ d>0,\quad M^d>|y|\quad\text{eventually}.
\]

The first compares **error envelopes**, not lower bounds for an actual
signed sum. The second rules out the direct fixed-degree rectangle
application, not every conceivable use of Vinogradov ideas.

## Stop rule

Do not add another completion, general sieve interface or carrier
decomposition merely to rename (II). Reopen this route only with an
independent signed estimate for the full discrepancy, or a weaker direct
one-sided floor whose differences from the carrier are independently
source-scale \(o(1)\).

The new unconditional arithmetic bounding milestone is the narrower-window
error. The quantitative implication is conditional. The independent surviving
floor and first restricted zero exclusion remain open.
