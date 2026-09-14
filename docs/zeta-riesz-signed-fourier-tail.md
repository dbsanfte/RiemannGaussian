# The signed arithmetic tail and its exact Fourier carrier

The original finite Riesz band now has a checked two-frequency integral
representation with its actual factorial filter and physical cutoff.
Separately, the nonlinear prime-character logarithmic remainder has a
cutoff-independent integrated bound at every fixed real part greater than
one half. **The independent signed arithmetic floor remains open.**
Neither result proves RH or enlarges the proved zero-free region.

[Open the supporting Fourier view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=signed-fourier-tail).
The default RH view remains the original
[`ZetaRieszCriticalProfile.exists_original_band_critical_profile`](../RiemannGaussian/ZetaRieszCriticalProfile.lean).
The new identities complement that bound; no dependency arrow to an
unproved arithmetic estimate is asserted.

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
Small primes remain explicit. Crucially, this controls the logarithmic
remainder itself. It does not bound \(e^{A_Q+E_Q}\), its high derivatives,
or its original factorial-filtered contribution.

## Classification of what remains

| Information or operation | Checked result | Remaining obligation |
|---|---|---|
| All affine lags and gcd collisions | Exact compatibility and recovery of the original carrier square | Mass-preserving orthogonality alone gives no saving. |
| Original signs and phases | Exact pair sum and signed divisor-window integral | Phase proximity needs amplitude matching and unmatched-mass control. |
| Bare Riesz coefficient | An exact example is below \(-1\) | A generic unit floor is false; the actual normalized filtered floor is still undecided. |
| All prime-subset sizes | Exact insertion recurrence and Fourier product | The full coupled sum needs a signed estimate. |
| Shared primes in pairs | The shared phase becomes a squared norm | Shared factors still move both cutoff ramps. |
| Frequency zero and first moment | Exact paired hinge identity and genuine integrability | Retain the moment and correction when estimating the complete response. |
| Nonlinear local-log remainder | Uniform finite-cutoff integrated bound at fixed \(\sigma>1/2\) | Control its effect inside the exponential and through the actual filter. |
| First-order prime phase | Exact \(A_Q=P_Q(s)-P_Q(s-i\xi)\) algebra | A usable signed bound coupled to the cutoff integral is open. |
| Source normalization | Original Fourier response still tends to \(-\operatorname{mult}(\rho)\) under the zero hypothesis | Prove the independent fixed cofinal floor above \(-1\). |

The next structural test is whether complete divisor-mass and log-moment
cancellation on squarefree composites exposes the original prime-factor
Fourier response more directly. This is a proposed continuation, not a
bound supplied by this slice. Generic absolute completion already has a
checked exponential cost at least \(2u>1\); retrying that estimate without
new signed information cannot close the current argument.

## Handoff integration and audits

The 14 September arithmetic handoff was independently checked, then its
129 declarations were promoted into five focused ordinary-library modules:
`ZetaArithmeticAffine`, `ZetaArithmeticBandCorrelation`,
`ZetaSquarefreeRieszWindows`, `ZetaSquarefreeRieszCompletion`, and
`ZetaSquarefreeSignedTail`. The new Fourier and integrated-remainder work
adds four modules. The original source hash and declaration mapping are
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
