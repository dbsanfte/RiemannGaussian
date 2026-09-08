# Coprime cancellation, reduced products, and the completion boundary

The objective remains one independent signed inequality that beats the
original source and all errors for each hypothetical zero right of one
half. This slice proves cancellation among the divisors of each physical
integer, separately inside every gcd block. It does not prove the needed
cancellation between different physical integers, a new zero exclusion,
or RH. The user's new
`RiemannGaussian_reduced_product_or_signed_current_steer.md`, referring to
head `8759725`, prompted the complete-product and prime-coefficient audit
below while the coprime bulk proofs were being verified.

## Complete product fibres and finite prime cancellation

`EtaGammaGcd.reducedProductCoefficient` is the exact complete sum over
`r*s=n` with all three original coprimality conditions and coefficients
`mu(r)*mu(s)`. It has no factor cutoff. The theorem
`reducedProductCoefficient_eq` proves

\[
c_g(n)=\begin{cases}
\mu(n)2^{\#\operatorname{primeFactors}(n)},
 &n\text{ squarefree and }(g,n)=1,\\
0,&\text{otherwise.}
\end{cases}
\]

`reducedZetaSquareCoefficient` is the actual arithmetic-function
convolution `zeta^2*c_g`. For every prime `p` not dividing `g` and every
natural `k`, `reducedZetaSquareCoefficient_prime_pow` proves

\[
(\zeta^2*c_g)(p^k)=1-k.
\]

Thus `reducedZetaSquareCoefficient_prime` gives zero at `p`, and
`reducedZetaSquareCoefficient_prime_sq` gives minus one at `p^2`.
After just one zeta convolution, `zeta_mul_reducedProduct_prime_pow`
gives minus one at every positive prime power. These are proved finite
coefficient identities, not a formal infinite Euler-product argument.
The restriction `p` not dividing `g` is essential.

This confirms the memo's local cancellation mechanism. Absolute Dirichlet
mass at `sigma>1/2` and a useful signed estimate for the actual finite
boundary do not follow from these identities alone. Neither is claimed
as proved here. The clipped coefficient below is one cofactor sum later
than `c_g`, and retains both factor cutoffs.

## Arithmetic identity before norms

For a fixed gcd `g`, let `r_g(n)` be the product of the distinct primes
dividing `n` that do not divide `g`. The empty product is one. Define the
literal integer coefficient

\[
C_{g,L,V}(n)=\sum_{\substack{a\le L,\ b\le V\\ab\mid n\\
 (a,b)=(g,a)=(g,b)=1}}\mu(a)\mu(b),
\]

where both divisor indices start at one. The definitions are
`EtaCoprimeRadical.eligibleRadical` and `coefficient`.

`coefficient_eq_radical_cutoffs` proves, for `1<=n<=L*V`,

\[
C_{g,L,V}(n)=\mu(r_g(n))
 \bigl(\mathbf1_{r_g(n)\le L}+\mathbf1_{r_g(n)\le V}-1\bigr).
\]

For equal cutoffs, `coefficient_square_eq_signed_radical` gives

\[
C_{g,N,N}(n)=
\begin{cases}
 \mu(r_g(n)),&r_g(n)\le N,\\
 -\mu(r_g(n)),&r_g(n)>N,
\end{cases}
\qquad 1\le n\le N^2.
\]

`abs_coefficient_le_one` bounds the complete rectangular coefficient by
one in absolute value throughout its product bulk. It is uniform in
`g,L,V,n` under the stated physical cutoff; it uses no zeta-zero
hypothesis. Outside that range, `abs_coefficient_le_cutoffs` retains the
unconditional bound `L*V`.

The proof identifies supported divisor pairs with disjoint subsets of
the eligible prime set. Summing all choices in one subset cancels unless
the other subset contains every eligible prime. The product cutoff rules
out a pair whose two factors are both omitted. Both cutoff indicators and
the remaining Moebius sign survive this cancellation.

## The complete original gamma core

Write `s=rho.1`, `sigma=Re(s)`, `chi=pairedEtaXiCompletionFactor(s)`, and
use the unchanged `gammaCarrier` and `reducedGcdCore` from the previous
gcd slice. `EtaGammaGcd.hasSum_coefficient_gamma` proves convergence and
the exact identity

\[
K_{s,T,N}(g)=-\sum_{n\ge1}C_{g,N,N}(n)\gamma_{s,T}(n).
\]

Each complete positive-cofactor row is included. The finite divisor
square is interchanged with the convergent rows using their proved
`HasSum` statements; no formal interchange of divergent series is used.

`radicalBulk` is the negative sum through `n=N^2`, with the displayed
radical signs. `radicalTail` is the entire negative sum beyond `N^2`,
with the original coefficients. The checked identities
`radicalBulk_eq_coefficient_prefix` and
`reducedGcdCore_eq_radicalBulk_add_tail` connect both objects exactly to
the original reduced core. In particular,

\[
\|\mathrm{radicalBulk}\|\le
 \sum_{1\le n\le N^2}\|\gamma_{s,T}(n)\|
\]

is `norm_radicalBulk_le`. This bound takes norms only after the complete
coprime divisor coefficient has been evaluated.

For `T>0`, `2T<=N^2`, `norm_radicalTail_le` proves

\[
\|\mathrm{radicalTail}\|\le
16\|\chi\|T N^2(N^2)^{-\sigma}e^{-N^2/(2T)}.
\]

This uses the actual exponentially damped gamma kernel, the complete
coefficient bound outside the bulk, and a summable geometric envelope.
`norm_reducedGcdCore_sub_radicalBulk_le` applies that allowance directly
to the original reduced core.

## All original gcd blocks, with their actual divided cutoffs

`radicalQuadratic` keeps the full finite sum

\[
Q^{\mathrm{rad}}_{s,A,U}=
\sum_{1\le g\le U}\mu(g)^2g^{-2s}
 \mathrm{radicalBulk}_{s,A/g^2,U/g}(g).
\]

The division `U/g` is natural-number division. For every `1<=g<=U`,
Lean proves `U<=2*g*(U/g)`. Consequently `U^2>=8A` puts **every**
divided core beyond its required tail threshold. The exact theorem
`smoothQuadratic_eq_radicalQuadratic_add_tail` retains all complex gcd
tails before estimating them. The terminal theorem
`norm_smoothQuadratic_sub_radicalQuadratic_le` proves

\[
\|Q_{s,A,U}-Q^{\mathrm{rad}}_{s,A,U}\|
\le32\|\chi\|A U^2e^{-U^2/(8A)},
\qquad A>0,\quad U^2\ge8A.
\]

The proof sums the actual scaled tails over every gcd and uses the
existing checked bound `sum_Icc_inv_sq_le_two`. It holds for every
actual nontrivial zero throughout the open strip. Completion phases,
squarefree gcd weights, and all signs remain in the richer exact identity.
No reflected off-diagonal is deleted.

## The full completion boundary carries twice the source

The new module `EtaGammaCompletionBoundary` tests the full completion
operation directly on the unchanged quadratic. `cofactor_moebius` proves
the exact arithmetic-function identity `zeta*mu^2=mu`. The definition
`completeQuadratic` uses that complete cofactor at every positive physical
integer, with the same negative sign and gamma carrier as the original
clipped quadratic. `completeQuadratic_eq_neg_source` evaluates its
convergent sum exactly:

\[
Q^{\mathrm{complete}}_{s,A}=-S_{s,A}.
\]

`completionBoundary` is defined coefficientwise as the negative gamma sum
of `cofactor(shortMoebius U)-cofactor(mu)`. Both full series are convergent.
`completionBoundary_eq_sub` proves

\[
B_{s,A,U}=Q_{s,A,U}-Q^{\mathrm{complete}}_{s,A}
         =Q_{s,A,U}+S_{s,A}.
\]

On the already checked schedule `A=u^8`, `U=u^5`,
`completeQuadratic_eighth_tendsto_neg_source` and
`completionBoundary_eighth_tendsto_two_source` consequently give

\[
Q^{\mathrm{complete}}\longrightarrow-S_s,
\qquad B\longrightarrow2S_s.
\]

`completionBoundary_eighth_not_tendsto_zero` uses the established
`S_s!=0` to prove that this exact boundary does not tend to zero. This
statement holds at every actual nontrivial zero; it is an audit of the
full rectangular completion, not a claim that each individual gcd
boundary has the same limit. It does not assume an infinite Euler product
for the reduced coefficients.

## What this changes, and the next primary target

The new arithmetic bound is **inside each individual gcd block**. The
existing global identity `EtaGammaQuadratic.moebius_eq_short_sub_cofactor`
already permits a one-dimensional Moebius reduction after recombining
all gcds. The new result should therefore not be presented as the first
scalar reduction of the full quadratic, or as an improved global
Moebius cancellation rate. Its additional information is the exact
coefficient and uniform bound before those gcd channels are combined.

At `g=1`, the surviving sign is `mu(rad(n))`, with the explicit cutoff
reversal. Bounding each such sign by one still leaves a sum of gamma
norms; it does not supply a signed saving below the source. The next
estimate must use the phases across physical integers, or their complete
reflected cross correlations, while paying the new tail allowance and
all existing source-comparison errors. The elementary radical identity
alone does not establish that estimate. No novelty-priority claim over
existing number theory is made.

The complete-product audit has confirmed local prime cancellation, but
the full finite completion boundary retains a leading source contribution.
We are therefore stopping the sequence of additional Gamma/gcd layers as
the primary attack, following the new memo's decision rule. This does not
prove that all possible Gamma-boundary estimates fail; it identifies why
the proposed completion-and-small-error shortcut fails.

The next primary target is a uniform bound for the **signed** weighted
partial sums of the actual `pairedEtaTopPrefixFiniteEnergyLeadingFlux`.
The existing principal-endpoint formula and summable weighted error should
first be used to prove one-sided divergence at an off-line zero. That
signed-divergence statement is not part of this slice. The independent
upper bound is still open and must not be introduced as an assumption
disguised as a proof. The original goal remains an actual contradiction
for every hypothetical zero right of one half.

## Verification

All five modules passed direct elaboration with warnings treated as
errors and are imported by the root library. The focused radical build
passed (`4576` jobs), and the complete five-module root build passed
(`9730` jobs). All 14 verbose root declaration-lint checks and the
whole-project declaration lint passed. The 16 audited terminal theorems
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The compiled inventory contains 883 project modules, 18808 declarations,
and 16178 theorems, with zero project axioms, zero placeholder-dependent
declarations, and no nonstandard theorem axioms. The compiled-environment
soundness generator passed; `rhImplied` remains false. Source placeholder
and whitespace checks passed. The tracked pre-commit hook repeats the
required build, lint, inventory-freshness, and staged-source gates;
exact-commit GitHub Actions success is required after the push.
