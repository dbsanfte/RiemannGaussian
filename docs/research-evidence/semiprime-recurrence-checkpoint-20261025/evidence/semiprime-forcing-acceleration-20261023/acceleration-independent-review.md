# Acceleration formulas and implementation audit

23 October2026. Verdict: PASS, with no required correction and no new
speed claim. Scope: independent review of the paired-norm source; fresh
algebra/cost recheck of `joint-forcing-attempt.md`, whose author is also
this reviewer. The latter is not represented as a second-author review.
No literature search, tests, examples, or tracked edits in this audit.

Reviewed exact input bytes:

* `paired-norm-execution.md`: SHA256
  `d2d09b95ac3ac721f49a5f7e7bab4d93e2bbc78d3561e38424fc510209a76b11`.
* `joint-forcing-attempt.md`: SHA256
  `34ebb3bcc289c03a0d825a9bc37cbefd1f949a610354e062641fa22a0728a5a7`.

## Paired norm

With z_j=Y_j^-1, the original row product is exactly
Y_j^L P_L(z_j;q); these powers and the product of their unit prefactors
are paid in soft J for polynomial-size indices. No scalar normalization
is silently assumed.

In A=R[X]/F, X is a unit since F has unit constant term. Thus the
difference of the two roots X,qX is (q-1)X, a certified unit. Evaluation
and interpolation in the displayed quadratic algebra are legitimate
even when cross-row virtual targets overlap. The determinant formula

    Norm(a+bT)=a^2+(1+q)Xab+qX^2b^2

has the correct signs. Its product identity pairs original seed indices
2i and2i+1; for length2n+1 the remaining factor is precisely
1-q^(2n)X. No field-only squarefree-quotient identification is required.

The q² coefficient denominators are certified: 1-(q²)^k=1-q^(2k)
lies in the parent horizon for k<=n. Odd local orders also show that
all successive dyadic powering preserves those orders. Monic MPE at
the 2J virtual targets does not require cross-target difference inverses.
The child workload is 2J times n, with2n=L up to the explicitly handled
odd tail; its soft(J+sqrt(JL)) bound is correct. Norm assembly costs
soft J afterwards. Recursive literal branching preserves that workload
product and does not by itself improve the exponent.

The omitted term in the shifted remainder is exactly
Q(q^(2n)X)F(q^(2n)X) mod F. The report correctly retains it. The sign
identity P_L(T)P_L(-T)=P_L(T²;q²) keeps length L, and its plus factors
are units only under the stated actual odd-order-root promise. Neither
that identity nor an inherited reflection fold supplies a new update
of the unacquired shifted source.

## Joint forcing

For the first-row companion convention used, f=chi_A is correct and
p->p(A)e_1 is unit triangular Toeplitz, giving the stated soft-J Krylov
conversion. The reversal constant is exactly

    c_L=(-1)^L q^(L(L-1)/2),
    X^L P_L(1/X;q)=c_L P_L(X;q^-1).

It is acquired with polynomial-bit exponent length. q^-1 has the same
unit-denominator horizon. The complete-block indices Bn+s are all<=L;
the separate ragged block covers precisely BK through L. Transposing
the cached scalar-linear circuit over E=R[X]/f therefore produces the
claimed H_s, and contraction followed by the Krylov map gives ALL J
tail coordinates, not just one projection. L=0 and J=0 are explicitly
handled.

The implementation really carries rank-J coefficients through the
lifted circuit. Generating K quotient weights, executing its B+K-size
scalar transform over E, and contracting them has the claimed bound
soft(sqrt L+J(B+K)+J). Its stated dense-quotient storage is also charged.
For polynomial-size indices, nearlinear modular polynomial arithmetic
over Z/N gives the displayed bit bound after a soft(log N) factor;
there are no growing integer-exponent actions hidden inside ring ops.
At B~sqrt L the result is soft(J sqrt L), slower than the inherited
soft(sqrt(JL)) native query.

## Implementation/design consequence checked

No acquired implementation gain was overlooked in these two executions.
The paired norm contracts already supplied child values cheaply; the
joint lift returns all coordinates but computes B separate quotient
elements first. Combining those steps literally does not acquire the
missing child data or fuse that quotient contraction at a lower cost.
This does not exclude a direct relative-norm or fused-contraction
algorithm that avoids the exposed intermediates. The reports correctly
make only implementation-specific cost statements, without a general
lower bound or a whole-input factoring-rate claim.
