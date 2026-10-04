# Rate gate for the literal Selberg-convolution route

The target remains the independent cofinal
`Re prefixPairDefect <=399/5000+o(1)` for ordinary primes. The preceding
continuous countertest does not refute a theorem using the literal
integer Möbius identity. This investigation checks the rate of the most
direct literature transfer before adding a new carrier or framework.
It produces **no arithmetic floor saving**.

## The exact integer constraint is already available

`SuzukiLogarithmicConvolution` proves

\[
\Lambda\log+\Lambda*\Lambda=\mu*\log^2
\]

pointwise at every integer. Its weighted theorem retains arbitrary complex
phases. `ZetaRieszPairPrimePowerPayment` permits the current whole joined
quadratic to use the full von Mangoldt arrays, with the proper-power cost
spent once. The central/successor factorial weights remain coupled; the
integer identity alone is not an estimate for them.

An alternative literature approach uses a convolution seminorm and its
spectral radius to prove the prime number theorem. The seminorm is a
limsup of translated prime discrepancies for a **fixed compactly supported
test function**. The argument supplies qualitative cancellation; its
author explicitly does not supply a quantitative error rate through this
method. [Tao's Banach-algebra proof of the prime number theorem](https://terrytao.wordpress.com/2014/10/25/a-banach-algebra-proof-of-the-prime-number-theorem/).

This is relevant because the radial factorial kernel is itself related
to repeated convolution. It does not license exchanging the fixed-test
translation limit with the growing order and width of our kernel.

There is a second applicability gate. Saidak studies how an input error
for `psi(x)-x` controls the remainder in the second Selberg formula after
its linear secondary term is removed. That is a direction from a
prime-counting error estimate to a Selberg estimate; it does not supply
an independently stronger prime-counting error. The published paper's
historical benchmark discussion is not used as a current record claim.
[Saidak, *On the prime number lemma of Selberg*](https://doi.org/10.7146/math.scand.a-15065).

Neither scalar cumulative formula is already an estimate for the
correlated central/successor factorial weights and their complex phase.
No theorem from this paper has been imported as a Lean bound here.

## Exact critical rate, not a frozen radial saddle

For `delta>=0`, the repository's checked
`ZetaRieszSelectedGamma.complex_factorial_laplace` gives exactly

\[
u^{N+1}\int_0^\infty
 \frac{T^N}{N!}e^{-T/2}e^{-\delta T}\,dT
 =\left(\frac{u}{1/2+\delta}\right)^{N+1}.
\]

This retains the whole radial integral. At `u=10001/20000`, strict decay
requires `delta>1/20000`. The critical error `exp(-T/20000)` tends to zero
in ordinary translation tests, but its source-normalized factorial
average is **exactly one at every order**. Thus qualitative cancellation
can hold without the source-scale decay needed by this approach.

The optional checker
[`CheckRieszSelbergSpectralRate.lean`](../scripts/CheckRieszSelbergSpectralRate.lean)
instantiates the existing factorial Laplace theorem. It kernel-checks the
general exact rate, qualitative decay of the critical synthetic error,
the mass-one identity at every order, and the hypothetical stronger rate
`10001/10002`. These four regressions are not actual-prime estimates. They
are outside the project root and ordinary CI, and use only standard axioms.

This is a diagnostic of the proposed positive-budget transfer, not a
counterexample about actual primes. The final one-sided signed floor
need not be proved through a norm bound or a fixed-power estimate.

An actual exponent `delta=1/10000` would give the exact rate
`10001/10002<1`. Such an arithmetic estimate has **not** been supplied
by the Selberg identity or the Banach-algebra literature input. It must
not be hidden inside a purported reduction.

## Why the angular contraction cannot be spent yet

The unweighted angular average `2/pi<1` appears in the literature proof.
If a genuine source-aware convolution inequality permitted that
contraction through a linear number of radial convolutions, it would
provide ample exponential margin. No such inequality is currently proved
for the actual moving factorial/phase weights.

The threshold for a radial root contraction is

\[
q<\frac1{2u}=\frac{10000}{10001}.
\]

An exposed selected mode is exactly critical, rather than strictly
subcritical. The already-proved `radius_le_of_nonzero_ordinary_source`
prevents silently choosing a Cauchy radius past it. The geometric decay
of competing modes does not furnish this missing strict contraction.

Furthermore, only `O(log N)` applications of a fixed contraction produce
a polynomial saving. For example

\[
(2u)^{N+1}(2/\pi)^{\log(N+1)/16}\to\infty.
\]

A many-bin hypothesis with that depth cannot, by itself, fund a positive
source-scale allowance. This does not reject a signed identity across
the bins or an arithmetic estimate which retains their correlations.

## Numerical probe and decision

[`probe_riesz_selberg_spectral_rate.py`](../scripts/probe_riesz_selberg_spectral_rate.py)
checks exact rational critical rates, and compares linear/logarithmic
iteration depths and labelled subexponential factors. It samples no
primes or zeta values. Unknown constants are factored out; no finite
factor is reported as a carrier bound in units of 0.0798.

The decision is to **stop the unweighted spectral-seminorm transplant**.
It lacks a uniform estimate for the source-scaled moving kernel. Do not
formalize the qualitative PNT argument again or count its spectral
radius as a new payment for the selected resonance. A source-aware
signed arithmetic inequality may still be investigated, but it is an
additional theorem, not a consequence proved by this rate check.

The full literal integer-convolution route remains available. Its next
test must retain the signed weighted Möbius boundary or produce an actual
uniform contraction for the joined sum. An absolute inverse-zeta bound
crossing the selected zero would assume away the obstruction: the actual
reciprocal series represents the Möbius factor to the right of one, and
the reciprocal has the selected zero as a pole.

No new project Lean module, arithmetic estimate, floor constant, zero
exclusion or RH proof is claimed. The focused rate checker is supporting
negative evidence, not floor progress. Earlier proofs and snapshots remain
fixed. Both the probe and checker stay optional outside ordinary builds
and CI; work remains local.
