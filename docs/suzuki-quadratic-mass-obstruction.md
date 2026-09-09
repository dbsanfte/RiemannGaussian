# A finite obstruction to the uniform Suzuki quadratic condition

The independent-input search checked the older prime-sum route before
adopting its quadratic sufficient condition. The resulting module
[SuzukiQuadraticMassObstruction.lean](../RiemannGaussian/SuzukiQuadraticMassObstruction.lean)
proves that the proposed condition cannot hold at every cutoff: it fails
at the actual prime prefix ending at `5`.

This is not a zero exclusion. It does not refute the exact Suzuki entropy
condition, and a finite counterexample does not rule out an eventual
quadratic condition. The original implication from the uniform quadratic
condition remains mathematically correct.

## Literal certified inequality

Let `r=suzukiFirstTailChebyshevCenter 3`, the unchanged canonical center
of the prefix ending at `count+2=5`, and let
`q=suzukiChebyshevCorrectedMassRatio r 5`. Write

\[
Q=\operatorname{suzukiChebyshevQuadraticMassCost}(r,5),
\qquad
B=\operatorname{suzukiChebyshevEndpointCenteredError}(5)
  +\operatorname{suzukiChebyshevLegendreLowerOrder}(r,q).
\]

The terminal theorem
`suzukiChebyshevQuadraticMassCost_five_exceeds_allowance` proves

\[
\boxed{B+\frac1{4000}\le Q.}
\]

The proof actually supplies `B <= 7083/100000` and `Q >= 712/10000`.
Consequently `suzukiChebyshevQuadraticMassCost_five_not_le_allowance`
proves `not (Q <= B)`, and
`not_forall_suzukiChebyshevQuadraticMassCost_le_allowance` negates the
exact all-cutoff antecedent of
`riemannXiSuzukiPsiNonnegative_on_logTwo_tail_of_quadraticMassMoment`.
No zero hypothesis or numerical oracle is used.

## Arithmetic and analytic checks

The actual mass and log-moment retain the prime-power weights at
`2,3,4,5`, including `Lambda(4)=log(2)`. Rational logarithm and square-root
bounds give

\[
M(5)\ge 2190749/10^6,\qquad L(5)\le 2675431/10^6.
\]

Euler's constant is bounded from below using the proved harmonic sequence
at index `1000`. A finite digamma difference sum plus a telescoping
lower bound controls the full quarter-point digamma. A separate
telescoping upper bound controls the complete Lerch constant. These give

\[
c=\tfrac12(\Re\psi(1/4)-\log\pi)<-26857/10000,
\qquad \tfrac14\Phi(1,2,1/4)-8\le-370054/100000.
\]

The zeroth Lerch slope term cancels the negative exponential exactly.
For `X=exp(r/2)`, the remaining positive slope tail `T(r)` satisfies

\[
\operatorname{Arch}'(r)=2X+c+T(r),\qquad
0\le T(r),\qquad T(r)(X^5-X)\le2/5.
\]

The exact canonical slope equation `Arch'(r)=M(5)` then yields
`X >= 12/5`, `r >= log(5)`, and `T(r) <= 13/2500`. These are bounds on
the repository's defined center, not on a substituted numerical root.
The Legendre identity retains the signed tail; only proved nonnegative
terms are discarded in the upper estimate for `B`.

A floating-point screen located the candidate and a higher-precision
evaluation suggested a larger failure margin. Those computations are
exploration only. The stated rational margin is proved independently
in Lean.

## Research consequence

The exact entropy requirement uses
`4*sqrt(5)*(q*log(q)-q+1)`, while the quadratic sufficient condition uses
`4*sqrt(5)*(q-1)^2`. This replacement adds a real burden: its uniform
arithmetic antecedent is false. It should not become the next goal as
currently quantified.

A future attack can retain the exact entropy expression, or seek an
eventual quadratic bound with the finite range handled separately. Neither
estimate is proved here. The source of the pointwise positivity criterion
is [Suzuki's screw-function paper](https://arxiv.org/html/2206.03682v3#S1);
this module only audits the repository's stronger quadratic reduction.

The active objective remains an independent inequality excluding every
hypothetical right-half zero. This check prevents pursuing a false
uniform premise; it does not supply that independent inequality.

Validation is local while commits are held: direct Lean elaboration,
focused module/root build, module declaration lint, and terminal axiom
audit. No new commit, push, or CI run belongs to this slice.
