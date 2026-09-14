# The signed arithmetic tail and its exact Fourier carrier

The original finite Riesz band now has a checked two-frequency integral
representation with its actual factorial filter and physical cutoff.
Its complete composite divisor measure now factors exactly over the
observed integer's primes. Separately, the nonlinear multiplicative
correction has a decreasing integrated arithmetic allowance that tends to
zero as the lower prime threshold grows, uniformly in finite prime
selections and imaginary height at every fixed real part greater than
one half. **The independent signed arithmetic floor remains open.**
These component bounds do not prove RH or enlarge the proved zero-free region.

[Open the supporting Fourier view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=signed-fourier-tail).
[Open the prime-factor and vanishing-allowance view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=prime-factor-tail).
The default RH view remains the original
[`ZetaRieszCriticalProfile.exists_original_band_critical_profile`](../RiemannGaussian/ZetaRieszCriticalProfile.lean).
The new identities complement that bound; no dependency arrow to an
unproved arithmetic estimate is asserted.

The subsequent [fixed-cofactor decay audit](zeta-riesz-fixed-cofactor-decay.md)
now pays a full original-band contribution for every fixed squarefree
composite cofactor, and gives an explicit bound after its full factorial
filter. It also identifies the remaining semiprime coefficients and strengthens
the isolated nonlinear allowance to a uniform closed-half-plane estimate.

The [full Euler correction continuation](zeta-riesz-euler-correction-energy.md)
now supplies a separate finite Euler-quotient factorization. Every interaction
order of its correction has a vanishing even paired-integral allowance and
odd-energy allowance. The leading quotient and both weighted couplings are
retained; this does not bound the complete original carrier.

## The exact target

For a hypothetical nontrivial zero \(\rho\) with \(\Re\rho>1/2\), set

\[
u=\tfrac32-\Re\rho\in(\tfrac12,1),\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
L_N=\log((D_N+2)^2).
\]

Write

\[
R_L(n)=\sum_{d\mid n}\mu(d)(L-\log d)_+,\qquad
C_L(n)=\begin{cases}
-\log(n)R_L(n)/L,&n\text{ squarefree and not prime},\\
0,&\text{otherwise}.
\end{cases}
\]

The original filter is `zetaRightHalfPoleJetFilter rho hrho`. The actual
finite band is `zetaPrimeLogBand N`, containing the positive integers
\(n\le2^{32N}\) with \(\log n>N\log(2)/4\). With that filter and band,

\[
B_N=u^{N+1}\operatorname{zetaArithmeticBand}
 (C_{L_N},P_\rho,N,\Im\rho)\longrightarrow-\operatorname{mult}(\rho),
\qquad \operatorname{mult}(\rho)\ge1.
\]

[`false_of_cofinal_original_riesz_floor`](../RiemannGaussian/ZetaSquarefreeRieszCompletion.lean)
proves that the following **unproved premise** would close the contradiction:

\[
\boxed{\exists c<1:\quad \Re B_N\ge-c\quad\text{for arbitrarily large }N.}
\]

The constant may depend on the fixed hypothetical zero, but stays fixed
along that cofinal sequence. Absolute-value decay and a bound at every
large order are unnecessary. A margin tending to zero does not suffice for
this criterion. Internal factorial shifts keep both \(L_N\) and the base
band fixed.

## A genuine, integrable Fourier identity

[`CosineHinge`](../RiemannGaussian/CosineHinge.lean) proves

\[
\int_0^\infty\frac{1-\cos(b\xi)}{\xi^2}\,d\xi
 =\frac\pi2|b|,\qquad
x_+=\frac{x}{2}+\frac1\pi\int_0^\infty
 \frac{1-\cos(x\xi)}{\xi^2}\,d\xi.
\]

Its proof establishes the Laplace identities, absolute integrability on
the positive quadrant and the required Fubini exchange. The integrals are
ordinary Lebesgue integrals, with integrability proved rather than inferred
from Lean's totalized integral notation.

For any finite complex weights \(w_j\), real positions \(x_j\), and cutoff
\(L\), define

\[
\Phi(\xi)=\sum_jw_je^{i\xi x_j},\qquad
K_L(\xi)=\sum_jw_j-
 \frac{e^{-i\xi L}\Phi(\xi)+e^{i\xi L}\Phi(-\xi)}2.
\]

[`FiniteSignedFourierHinge.finite_hinge_eq_paired_integral`](../RiemannGaussian/FiniteSignedFourierHinge.lean)
gives the exact identity

\[
\sum_j(x_j-L)_+w_j
 =\frac12\sum_j(x_j-L)w_j+
   \frac1\pi\int_0^\infty\frac{K_L(\xi)}{\xi^2}\,d\xi.
\]

The same module identifies \(K_L\) with
\(\sum_jw_j(1-\cos((x_j-L)\xi))\), proves its zero-frequency cancellation,
and proves the complex quotient integrable. Both frequencies and the first
moment remain present. Arbitrary complex weights do not justify replacing
\(\Phi(-\xi)\) by \(\overline{\Phi(\xi)}\).

## Connection to the original factorial-filtered band

For a finite observation set \(T\) and arbitrary complex observation
\(f(n)\), the exact cofactor weight is

\[
w_d=\mu(d)\frac{-1}{L}
 \sum_{n\in T}\mathbf1_{n\text{ squarefree},\ d\mid n}\log(n)f(n).
\]

Take the squarefree divisors \(1\le d\le D\), with
\(L\le\log(D+1)\), and put \(x_d=-\log d\), with hinge cutoff \(-L\).
[`ZetaRieszFourierCarrier.original_sum_eq_fourierResponse`](../RiemannGaussian/ZetaRieszFourierCarrier.lean)
then identifies \(\sum_{n\in T}C_L(n)f(n)\) with that signed first moment
plus the paired integral **and** the ordinary-prime correction

\[
\sum_{\substack{p\in T\\p\text{ prime}}}
 \frac{\log p\min(L,\log p)}{L}\,f(p).
\]

`actual_physical_band_eq_fourierResponse` specializes this equality to the
literal factorial kernel, the original band and
\(D=(D_N+2)^2\), discharging the cutoff condition.
`tendsto_actual_fourierResponse` transports the original negative
multiplicity source under the hypothetical-zero assumption. It is not an
independent arithmetic lower bound.

The cofactor marks retain all filtered complex amplitudes. They cannot be
replaced by an unweighted prime product without another proved identity.
The finite prime-subset tail has its own exact paired integral and product
character in `signedSubsetTail_eq_paired_integral` and
`subset_finiteCharacter_eq_product`.

## Complete divisor cancellation and the literal prime factors

For every squarefree nonunit composite, Lean now proves both cancellations
before applying the hinge identity:

\[
\sum_{d\mid n}\mu(d)=0,\qquad
\sum_{d\mid n}\mu(d)\log d=-\Lambda(n)=0.
\]

These are complete per-integer divisor measures. The previously truncated
common-divisor marks still retain their first moment and ordinary-prime
correction. The two representations agree; their measures are different.

Define the full prime product and its paired response by

\[
P_n(\xi)=\prod_{p\mid n}(1-p^{-i\xi}),\qquad
H_{n,L}(\xi)=e^{i\xi L}P_n(\xi)+e^{-i\xi L}P_n(-\xi).
\]

[`ZetaRieszPrimeFourier.riesz_eq_primePair_integral`](../RiemannGaussian/ZetaRieszPrimeFourier.lean)
proves the genuinely integrable identity

\[
R_L(n)=-\frac1{2\pi}\int_0^\infty
 \frac{H_{n,L}(\xi)}{\xi^2}\,d\xi.
\]

`actual_band_eq_primePair_integral` applies this formula to the original
coefficient and factorial kernel, with exactly the original band and common
physical length. `tendsto_actual_primePair_integral` preserves its
hypothetical-zero source. The exact phase factorization is

\[
P_n(\xi)=(2i)^{\omega(n)}e^{-i\xi\log(n)/2}
 \prod_{p\mid n}\sin\!\left(\frac{\xi\log p}{2}\right).
\]

Thus prime count, central phase and every signed sine factor remain
available. This identity alone is not an upper or lower bound on the band.

## A controlled nonlinear contribution

For finite prime labels \(Q\), write
\(q_p=p^{-s}\), \(a_p=q_p/(1+q_p)\), and \(\ell_p=\log p\).
The finite signed subset tail contains every subset size:

\[
T_{L,Q}(s)=\sum_{S\subseteq Q}
 \left(\sum_{p\in S}\ell_p-L\right)_+\prod_{p\in S}(-a_p).
\]

Its normalized character factors as
\(\prod_{p\in Q}[1+q_p(1-e^{i\xi\ell_p})]\).
[`ZetaPrimeCharacterRemainder.normalized_character_eq_exp`](../RiemannGaussian/ZetaPrimeCharacterRemainder.lean)
proves, for \(|q_p|\le1/4\), that this equals

\[
\exp(A_Q(\xi;s)+E_Q(\xi;s)),\qquad
A_Q=\sum_{p\in Q}q_p(1-e^{i\xi\ell_p}),
\]

where \(E_Q\) is the sum of the corresponding **local** logarithm errors.
No principal-logarithm identity for the whole product is assumed.
Keeping the phase in each local estimate yields

\[
|\log(1+q(1-z))-q(1-z)|\le |q|^2|1-z|^2,
\qquad |q|\le\tfrac14,\quad |z|\le1.
\]

The exact cosine kernel therefore pays the complete frequency integral:

\[
\int_0^\infty\frac{|E_Q(\xi;s)|}{\xi^2}\,d\xi
 \le\pi\sum_{p\in Q}|q_p|^2|\ell_p|.
\]

`integral_norm_actual_logRemainder_div_le` bounds this by a convergent
integer majorant independent of finite \(Q\), when every label is at least
16 and \(\sigma=\Re s>1/2\):

\[
\frac{\pi}{\sigma-1/2}\sum_{n\ge0}
 \operatorname{zetaPrimeExpWeight}(\sigma+1/2,n).
\]

The harmless totalized \(n=0\) term is included in this Lean majorant.
The bound is at fixed \(\sigma\), not uniform as \(\sigma\downarrow1/2\).
Small primes remain explicit.

[`ZetaPrimeNonlinearFactor`](../RiemannGaussian/ZetaPrimeNonlinearFactor.lean)
now also pays the multiplicative correction. Put

\[
M_\sigma=4\sum_{n\ge0}\operatorname{zetaPrimeExpWeight}(2\sigma,n),
\qquad C_\sigma=\pi(2+e^{M_\sigma}).
\]

The pointwise bound \(|E_Q|\le M_\sigma\) and genuine integrability give

\[
\int_0^\infty\frac{|e^{E_Q(\xi;s)}-1|}{\xi^2}\,d\xi
 \le C_\sigma\sum_{p\in Q}p^{-2\sigma}\log p.
\]

## Bounding milestone: the nonlinear arithmetic allowance tends to zero

[`ZetaPrimeNonlinearTail`](../RiemannGaussian/ZetaPrimeNonlinearTail.lean)
proves summability of the literal square-log weights and defines

\[
J_\sigma(K)=\sum_{n\ge K}n^{-2\sigma}\log n.
\]

Here the Lean weight at zero is zero; for positive integers it has the
displayed ordinary value. The definition is the convergent total minus
its finite prefix. Lean proves

\[
J_\sigma(K)\ge0,\quad
J_\sigma(K+1)=J_\sigma(K)-K^{-2\sigma}\log K,\quad
J_\sigma(K)\downarrow0
\]

with the same zero convention. For every finite selection \(Q\) of labels
at least \(\max(16,K)\), `integral_norm_nonlinearFactor_le_tail` gives

\[
\boxed{\int_0^\infty\frac{|e^{E_Q(\xi;s)}-1|}{\xi^2}\,d\xi
 \le C_\sigma J_\sigma(K)\longrightarrow0.}
\]

`exists_uniform_nonlinearFactor_tail_lt` proves the quantifiers explicitly:
for every fixed \(\sigma>1/2\) and \(\varepsilon>0\), one threshold
\(K\ge16\) works for **every** finite \(Q\) above it and **every**
\(s\) with \(\Re s=\sigma\). No threshold is numerically evaluated.
This strengthens the earlier constant bound to a vanishing allowance for
the nonlinear correction. It does not bound that correction after
multiplication by \(e^{A_Q}\), or after the original high-order filter.
The remaining finite small-prime factors must also stay in the full carrier.

## Recompletion retains the prime subtraction and the band boundary

For squarefree \(m\), the complete divisor sum satisfies

\[
\sum_{n\mid m}n^{-s}P_n(\xi)
 =\prod_{p\mid m}[1+p^{-s}(1-p^{-i\xi})].
\]

[`ZetaRieszCompositeProduct`](../RiemannGaussian/ZetaRieszCompositeProduct.lean)
then deletes the unit and ordinary primes exactly. If all participating
primes are at least 16 and \(\Re s\ge1/2\), the composite sum is

\[
\sum_{\substack{n\mid m\\n\ne1,\ n\text{ not prime}}}n^{-s}P_n(\xi)
 =e^{A+E}-1-A
 =(e^A-1-A)+e^A(e^E-1),
\]

where \(A=A_{\{p:p\mid m\}}(-\xi;s)\) and likewise for \(E\).
The negative frequency matches the original imaginary-power feature.
The finite Euler-product identity itself also includes the small primes
without a small-weight hypothesis. The explicit singleton subtraction
must survive any further manipulation.

`actual_band_symbol_eq_completed_sub_boundary` chooses the primorial of
the original band endpoint \(2^{32N}\). Every original squarefree label
divides this canonical integer. Its complete composite response minus the
entire omitted signed divisor sum equals the original band symbol.
Completion therefore introduces an explicit boundary, whose smallness is
**not** proved. This is a generating-function identity; it does not yet
estimate that boundary after the factorial filter.

## Classification of what remains

| Information or operation | Checked result | Remaining obligation |
|---|---|---|
| All affine lags and gcd collisions | Exact compatibility and recovery of the original carrier square | Mass-preserving orthogonality alone gives no saving. |
| Original signs and phases | Exact pair sum and signed divisor-window integral | Phase proximity needs amplitude matching and unmatched-mass control. |
| Bare Riesz coefficient | An exact example is below \(-1\) | A generic unit floor is false; the actual normalized filtered floor is still undecided. |
| All prime-subset sizes | Exact insertion recurrence and Fourier product | The full coupled sum needs a signed estimate. |
| Shared primes in pairs | The shared phase becomes a squared norm | Shared factors still move both cutoff ramps. |
| Frequency zero and first moment | Both moments vanish for each complete squarefree composite divisor measure; the actual band has an integrable prime product | Truncated common-divisor marks still retain their moment and prime correction. |
| Prime-factor phase | Exact centered sine product and original filtered integral | Exploit cross-integer correlations before taking norms. |
| Nonlinear local-log remainder | Uniform finite-cutoff integrated bound at fixed \(\sigma>1/2\) | The complete first-order coupling still needs control. |
| Nonlinear multiplicative correction | Decreasing integrated allowance tending to zero above a growing prime threshold, uniformly in height at fixed \(\sigma>1/2\) | Pay multiplication by \(e^A\), the finite small primes and the original factorial filter. |
| Composite Euler completion | Exact \(e^{A+E}-1-A\) and explicit actual-band boundary | Bound the coupled compensated response and boundary without discarding their signs. |
| First-order prime phase | Exact \(A_Q=P_Q(s)-P_Q(s-i\xi)\) algebra | A usable signed bound coupled to the cutoff integral is open. |
| Source normalization | Original Fourier response still tends to \(-\operatorname{mult}(\rho)\) under the zero hypothesis | Prove the independent fixed cofinal floor above \(-1\). |

The next target is an estimate for the coupled compensated response and
its signed boundary that survives the original filter and source scale.
The vanishing nonlinear allowance supplies one controlled ingredient;
it is not the independent signed floor. Generic absolute completion has a
checked exponential cost at least \(2u>1\); retrying that estimate without
new signed information cannot close the current argument.

## Handoff integration and audits

The 14 September arithmetic handoff was independently checked, then its
129 declarations were promoted into five focused ordinary-library modules:
`ZetaArithmeticAffine`, `ZetaArithmeticBandCorrelation`,
`ZetaSquarefreeRieszWindows`, `ZetaSquarefreeRieszCompletion`, and
`ZetaSquarefreeSignedTail`. The first Fourier and integrated-remainder
slice added four modules. The next slice adds `ZetaRieszPrimeFourier`,
`ZetaPrimeNonlinearFactor`, `ZetaPrimeNonlinearTail`, and
`ZetaRieszCompositeProduct`. The original source hash and declaration mapping are
recorded in [handoff provenance](arithmetic-tail/handoff-provenance.json).

The integrated sources participate in the ordinary root, full build,
declaration lint and complete transitive axiom audit. The allowed axioms
are only `propext`, `Classical.choice` and `Quot.sound`. The
[generated project status](proof-status.json) and
[RH graph audit](rh-proof-explorer/audit.json) supply the evergreen checks
and source links. These gates do not run the optional exhaustive numerical
certificate. Handoff floating-point model-filter diagnostics are not
actual-zero estimates and are not promoted as theorem evidence.
No historical novelty claim is made for these identities.
