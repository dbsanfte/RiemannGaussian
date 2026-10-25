# Research project: local Suzuki cancellation and a one-sided prime estimate

Date: 23 October 2026.

## Objective and status

Investigate whether the cancellation techniques developed during the
semiprime-factorization research can supply an **independent arithmetic
estimate strong enough to prove RH**. The concrete target below compares two
overlapping, triangularly smoothed prime sums. It retains the original Suzuki
signal and every prime power.

This document records a paper derivation from a read-only side investigation.
The new identities and conditional implication have **not** been formalized
or independently checked in Lean. The arithmetic inequality is unproved.
There is no new RH proof, zero-free region, or claimed historical novelty.
The dedicated agent should first audit the derivation, then concentrate on
the missing estimate rather than accumulating equivalent criteria.

**Main research target:** prove that the explicit function G below satisfies

$$
\forall\varepsilon>0\ \exists C_\varepsilon\ge0,\ X_\varepsilon\ge2,
\quad\forall X\ge X_\varepsilon,\qquad
G(X)\ge-C_\varepsilon X^\varepsilon.
\tag{T}
$$

Here X is real. Constants and starting cutoffs may depend on epsilon, but
not on X. Large positive values of G are allowed. The derivation below shows
why (T), if proved independently, would imply RH through an existing
repository theorem. It does not prove (T).

## 1. Explicit arithmetic quantity

All logarithms are natural. Set

$$
h=\log 2,\qquad c=\sqrt2,\qquad
\tau(v)=\max\{0,h-|v-h|\}.
$$

Thus tau is triangular, supported on [0,2h], with height h. Define

$$
A(X)=\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}
       \tau\!\left(\log\frac nX\right),\qquad
G(X)=cA(X)-A(2X).
\tag{1}
$$

These sums are finite. Only X<n<4X contributes to A(X), and only
X<n<8X contributes to G(X). Endpoint terms vanish, so including either
endpoint does not change the definitions. Lambda is the actual von Mangoldt
function, including all proper prime powers.

The equivalent single signed kernel is

$$
G(X)=\sum_n\frac{\Lambda(n)}{\sqrt n}
       W\!\left(\log\frac nX\right),\qquad
W(v)=c\tau(v)-\tau(v-h).
\tag{2}
$$

Explicitly,

$$
W(v)=
\begin{cases}
cv,&0\le v\le h,\\
(2c+1)h-(c+1)v,&h\le v\le2h,\\
v-3h,&2h\le v\le3h,\\
0,&\text{otherwise}.
\end{cases}
$$

The interior sign change is at v=(3-sqrt(2))h. This is one fixed signed
prime-band weight, not an arbitrary family of test coefficients.

## 2. Exact connection to the existing Suzuki signal

The repository's literal signal is

$$
S(t)=4e^{t/2}-\sum_{n\le e^t}
       \frac{\Lambda(n)}{\sqrt n}(t-\log n),\qquad t\ge0.
\tag{3}
$$

Its identification with the existing definition is the theorem
`suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime` in
[SuzukiPositivityRH.lean](RiemannGaussian/SuzukiPositivityRH.lean#L40).

Write E_h f(t)=f(t+h), and define

$$
U(t)=(E_h-1)^2S(t).
$$

For every real v, the second forward difference of (t-v)_+ is
tau(v-t). Checking the three intervals v<=t, t<v<t+h, and
t+h<=v<t+2h, and the region v>=t+2h, gives the identity including endpoints.
Consequently

$$
U(t)=4(c-1)^2e^{t/2}-A(e^t).
\tag{4}
$$

The old prime history has canceled exactly. Applying one more difference
cancels the exponential main term:

$$
\boxed{G(e^t)=U(t+h)-cU(t)=(E_h-c)(E_h-1)^2S(t).}
\tag{5}
$$

In particular the four signal coefficients, in increasing shift order,
are -c, 1+2c, -(2+c), 1. No prime contribution, boundary correction, or
Archimedean term of the signal (3) is omitted.

## 3. The asymptotic boundary needed to invert the recurrence

The prime number theorem gives

$$
A(X)=4(c-1)^2\sqrt X+o(\sqrt X),\qquad
U(t)=o(e^{t/2}).
\tag{6}
$$

This is unconditional and weaker than (T). A direct derivation uses
psi(x)=x+o(x) in the Stieltjes integral

$$
A(X)=\int_X^{4X}x^{-1/2}\tau(\log(x/X))\,d\psi(x).
$$

The smooth-density contribution is

$$
\sqrt X\int_0^{2h}e^{v/2}\tau(v)\,dv
=4(c-1)^2\sqrt X.
$$

For the error, the test function is continuous, piecewise smooth, and zero
at both endpoints. Its total variation is O(X^(-1/2)). On this fixed
multiplicative interval, sup |psi(x)-x|=o(X), so integration by parts gives
o(sqrt(X)). The kink at 2X introduces no jump in the test function.

An existing local PNT entry point is `chebyshevPsi_div_tendsto_one` in
[ChebyshevMoebiusCancellation.lean](RiemannGaussian/ChebyshevMoebiusCancellation.lean#L450).
See also [the existing arithmetic transfer](docs/suzuki-arithmetic-cancellation.md).
No RH-strength error term is assumed here.

**Do not omit this boundary condition.** The homogeneous recurrence
U(t+h)=cU(t) has an e^(t/2) mode. The local difference alone does not
control it; (6) is what removes it for the actual arithmetic signal.

## 4. Paper proof that target (T) implies RH

Fix 0<epsilon<1/2 and take t beyond the threshold in (T). Iterating (5)
through an integer number r of shifts gives the exact finite identity

$$
U(t)=c^{-r}U(t+rh)
 -\sum_{j=0}^{r-1}c^{-j-1}G(e^{t+jh}).
\tag{7}
$$

By (6), the first term tends to zero. The hypothesized lower bound on G
therefore yields

$$
U(t)\le
\frac{C_\varepsilon}{c-2^\varepsilon}\,e^{\varepsilon t}.
\tag{8}
$$

The denominator is positive. This argument uses finite partial-sum
inequalities and a limit; it does not presume absolute convergence of an
uncontrolled infinite forcing series.

Now fix a base point t_0 in a compact interval [T,T+h], and put
s_n=S(t_0+nh). Summing second differences exactly gives, for n>=2,

$$
s_n=s_0+n(s_1-s_0)
 +\sum_{j=0}^{n-2}(n-1-j)U(t_0+jh).
\tag{9}
$$

For a=2^epsilon>1,

$$
\sum_{j=0}^{n-2}(n-1-j)a^j
=\frac{a^n-na+n-1}{(a-1)^2}
\le\frac{a^n}{(a-1)^2}.
$$

The finite prime sum defining S is continuous on compact intervals, including
at prime-power entry points because the entering atom is zero there.
Thus the initial terms in (9) are uniformly bounded over t_0. Equation (8)
and the displayed geometric sum imply

$$
S(t)\le C'_\varepsilon e^{\varepsilon t}
\quad\text{for all sufficiently large }t.
\tag{10}
$$

The finite initial interval is absorbed into the constant. Exponents
0<epsilon<1/2 suffice to obtain a bound of this form for every positive
epsilon, by using a smaller exponent when necessary.

Finally apply
`riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound`
from [SuzukiLaplaceCompensator.lean](RiemannGaussian/SuzukiLaplaceCompensator.lean#L246)
with orientation **a=-1**. Its required lower bound on -S is exactly the
upper bound (10). Its existing analytic proof handles every zero multiplicity.

The dedicated agent must check this implication before treating (T) as an
accepted interface. The implication is a proposed reduction, not evidence
that its arithmetic premise holds.

## 5. Source retention and the density cancellation

For an exponential mode e^(lambda*t), the operator in (5) multiplies by

$$
p_h(\lambda)=(2^\lambda-c)(2^\lambda-1)^2.
\tag{11}
$$

At a hypothetical right-half zeta zero, lambda=rho-1/2 has
0<Re(lambda)<1/2. Hence 1<|2^lambda|<c, and neither factor in (11)
vanishes. The filter cancels the density exponent 1/2 and the constant/linear
homogeneous channels without erasing an exponential mode from a right-half
zero. This modal check is supplementary; the proof in section 4 does not
require an unproved interchange with a zero expansion.

The finite kernel also has an explicit transform:

$$
\int_{\mathbb R}e^{\lambda v}W(v)\,dv
=(c-2^\lambda)\frac{(2^\lambda-1)^2}{\lambda^2},
\qquad \lambda\ne0.
\tag{12}
$$

At lambda=0 use the removable limit (c-1)h^2, not division by zero.
At lambda=1/2 the transform vanishes, confirming exact mean-density
cancellation. No bound on the remaining prime fluctuation follows from
that cancellation alone.

## 6. Proper prime powers have only a bounded cost

Define A_pr(X) by restricting (1) to ordinary primes, and put
G_pr(X)=cA_pr(X)-A_pr(2X). The proposed elementary bound is

$$
G(X)-G_{\rm pr}(X)=O(1),\qquad X\ge2.
\tag{13}
$$

Here is a proof to audit. The fixed kernel W is bounded. The total absolute
prime-power contribution is therefore bounded by a constant times

$$
\sum_{\substack{k\ge2,\ p\ {m prime}\\X\le p^k\le8X}}
\frac{\log p}{p^{k/2}}.
$$

Use the unconditional Chebyshev bound theta(y)<=C*y. The squares contribute
at most theta(sqrt(8X))/sqrt(X)=O(1). The exponents k>=3 number O(log X),
and their total is at most

$$
X^{-1/2}\sum_{k=3}^{\lfloor\log_2(8X)\rfloor}
\vartheta((8X)^{1/k})
=O(X^{-1/6}\log X)=O(1).
$$

Thus (T) can equivalently be sought for G_pr, with constants adjusted.
This is a bounded arithmetic deletion, not an assumption that prime powers
or analytic zero multiplicities can be discarded for free.

## 7. What the present estimates do and do not establish

Equation (6) gives only G(X)=o(sqrt(X)) by direct substitution. This is not
the one-sided X^epsilon estimate for every epsilon>0 required in (T).
It is the bound used in this calculation, not a claim to have surveyed the
strongest available literature estimates or all imported zero-free regions.

The main density and the entire earlier prime history have canceled.
The remaining expression is a fixed signed comparison of actual prime
populations. Positivity of Lambda, a fast recurrence evaluator, a low-rank
representation, or exact character orthogonality alone does not give the
needed lower bound. Finite successful examples would not establish it.

A bound G(X)>=-C*X^delta for one fixed positive delta does not complete
this project. Any partial zero-free consequence would need its own exact
transfer and comparison with the existing imported baseline.

## 8. Why the direct eta-current transplant was not selected

The initial idea was to combine the new semiprime commutator cancellations
with the literal eta leading-current formula. For higher multiplicity,
symmetrizing the two adjacent centered powers introduces t+u-2*ell:

$$
\tfrac12\left[(t-\ell)^{k-1}(u-\ell)^k
 +(t-\ell)^k(u-\ell)^{k-1}\right]
=\tfrac12[(t-\ell)(u-\ell)]^{k-1}(t+u-2\ell).
$$

This naturally produces an anticommutator, whereas the recent commutator
identities involve coordinate differences. Reflection changes the measure
and its support; those changes cannot be silently ignored. The simple-zero
head branch also needs its own identity.

More decisively, existing work already identifies the unchanged eta current's
positive leading term at a hypothetical right-half zero:

$$
W_\rho(K)/K^{2\Re\rho-1}\longrightarrow4A_\rho>0.
$$

See [the dominant-energy audit](docs/eta-current-dominant-energy-asymptotic.md)
and
[EtaCurrentDominantEnergyAsymptotic.lean](RiemannGaussian/EtaCurrentDominantEnergyAsymptotic.lean#L335).
Exact rearrangement preserves that coefficient. Subtracting it leaves a
summable error without excluding the hypothetical zero. Do not reopen that
route merely to obtain another representation; require independent input
that controls the full original current. The present project instead tests
an explicit arithmetic inequality on the Suzuki prime sum.

## 9. Work plan for the dedicated agent

1. **Audit the reduction first.** Check signs, shift orientation, the PNT
   boundary in (7), real-cutoff uniformity, the finite head in (10), the
   choice a=-1, and the bounded prime-power deletion. Report any correction
   before investigating the arithmetic target. No extra zero-location
   hypothesis may enter this audit.
2. **Check prior art and repository overlap.** Search primary sources on
   one-sided smoothed prime estimates, Riesz means, finite differences,
   Suzuki/Landau criteria, and fixed Mellin filters. Determine whether (T)
   is an existing criterion in another notation. Record actual quantitative
   hypotheses and uniformity; do not claim novelty from a new notation.
3. **Investigate G as one coupled expression.** Explore common divisor or
   character expansions of the two overlapping packets, retaining their
   relative coefficient sqrt(2), all phase information, and all boundaries.
   Apply a norm only after cancellations that have been proved for this
   actual arithmetic family. Finite-ring identities need a justified
   analytic bridge before they can estimate this real prime sum.
4. **Attempt a substantive estimate.** The goal is (T), or a rigorous
   arithmetic bound that improves a specified part of the unresolved
   signed expression. If a chosen mechanism fails, identify its exact
   remaining term and redirect toward another mechanism; a collection of
   reformulations or obstructions is not the project objective.
5. **Formalize established progress proportionately.** Follow the repo's
   soundness, build, lint and axiom-audit requirements for any Lean work.
   A conditional transfer may be recorded as such, but do not present its
   formalization as a proof of (T) or as a new RH milestone. Prioritize
   finding the independent arithmetic estimate.

Useful starting sources, in addition to those cited above:

- [Global Gaussian/Weil and Suzuki direction](docs/gaussian-suzuki-pivot.md).
- [General compensator notes](docs/suzuki-subexponential-compensator.md).
- [Existing Suzuki bilinear work](docs/suzuki-bilinear-work.md).
- [Arithmetic-operator investigation](docs/arithmetic-operator-research.md),
  especially prior source-preserving density cancellations and their
  unresolved signed estimates.
- [Eta signed-current application audit](docs/rh-overnight-signed-flux-review.md).
- Masatoshi Suzuki, [Aspects of the screw function corresponding to the
  Riemann zeta-function](https://arxiv.org/abs/2206.03682), for primary context.

## 10. Deliverable and success criterion

Return a concise derivation audit, a literature/duplicate check, and the
strongest independently established estimate for the exact G or G_pr.
State every remaining premise and the range and uniformity of every bound.
If no improvement is obtained, say so and identify one concrete next
arithmetic operation or estimate, without claiming a general impossibility.

Full success requires proving (T), validating its complete implication to
Mathlib's literal `RiemannHypothesis`, and completing the required Lean and
axiom checks. This research brief itself changes no proof-status claim.
