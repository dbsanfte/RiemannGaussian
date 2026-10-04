# Selberg trace and the full positive-density countertest

The target remains an independent cofinal
`Re prefixPairDefect <=399/5000+o(1)` for the ordinary-prime carrier.
This slice supplies **no arithmetic floor saving**. It tests, and rules out,
closing that target from generic positive-density/common-phase moment
information plus the normalized Selberg source cancellation.

The new leaf is
[`ZetaRieszSelbergSourceAudit.lean`](../RiemannGaussian/ZetaRieszSelbergSourceAudit.lean).
The preceding whole-support completion and independent geometric payment
of the complete joined square correction are preserved.

## What the exact signed calculation retains

Let `a_k` be the normalized logged factorial moments, `M=N+1`,
`K=floor(13N/32)`, and `L=length u N`. The audit evaluator
`momentPolynomial` has exactly the central, successor, logged-prefix and
full Selberg-trace slots of `factorialQuadratic`.
`factorialQuadratic_eq_polynomial` checks this against the actual finite
ordinary-prime expression, including the prime assigned to each order.
It does not bound that expression.

For `P_k=a_(k-1)/(k*u^k)`, `model_polynomial_eq_harmonic` collects the
source-normalized polynomial exactly into

\[
\begin{aligned}
Q_N(a)={}&\frac1N\sum_{k=0}^{N-1}a_k a_{N-1-k}\\
&+\sum_{k=K+1}^{N-K}
  \frac{a_{k-1}a_{N-k}}{N+1-k}\\
&-\frac{N+1}{uL}
  \sum_{k=1}^{N+1-K}
  \frac{a_{k-1}a_{N+1-k}}{N+2-k}.
\end{aligned}
\]

Reflection and partial fractions retain both unequal order marginals.
The successor central band and logged prefix combine before taking a
limit. Their genuine integer endpoints are not rounded or replaced by
a continuum selection. Logged order zero remains in both the trace and
the successor prefix. Ordinary order zero was already cancelled by the
preceding exact endpoint identity; it is not a deleted exceptional mass.
The proof uses the original moving length, not `L=-2N log u` at finite N.

## The generic trace does not distinguish the source model

For every complex array with `a_k -> -1`, Lean proves

\[
-a_{N+1}-\frac1{N+1}\sum_{k=0}^N a_k a_{N-k}\longrightarrow0.
\]

This is `traceError_tendsto`. The earlier continuous positive-density
model has that same limit, so `density_traceError_tendsto` applies to its
exact common-phase moments, with their finite lower threshold retained.

This statement concerns the normalized **trace test**. It does not claim
that the continuous density satisfies the literal integer Möbius/Selberg
coefficient identity. That stronger arithmetic identity is not a premise
or a conclusion of this countertest.

## Cofinal failure, now proved rather than inferred from samples

The joined polynomial is continuous at the entire convergent moment array:

\[
a_k\to-1\quad\Longrightarrow\quad
Q_N(a)\to
1+\log(19/13)-\frac{\log(32/13)}{-2u\log u}
=1-c_{\rm ret}(u).
\]

Both harmonic intervals use their exact endpoints. The error proof pays
the two reflected marginals by one centered Cesàro mean; it does not
discard finitely many logged orders or replace independently masked prime
legs by their limits.

For the strictly positive model

\[
\nu(T)=\frac{e^T-2e^{(3/2-u)T}\cos(yT)}T,
\qquad u=10001/20000,\quad T\ge20000,
\]

the preceding leaf proves normalized moments tend to `-1` at every fixed
`|y|>=1`. The new `density_polynomial_tendsto` therefore proves the limit
of its complete four-term signed evaluation, not only the limit of each
moment. `eventually_density_polynomial_gt_target` then gives

\[
\Re Q_N(\nu)>399/5000
\]

eventually. `density_cofinal_floor_impossible` rules out even a cofinal
`399/5000+err_N` upper bound when `err_N -> 0` for this model.
No numerical threshold crossing is used as a proof step.

The previous optional probe's first sampled crossing at `N=83886080`
remains a finite regression result. The cofinal theorem does not certify
that this is the first crossing, nor assign a numerical entry order to
its eventual statement. The model is not the ordinary-prime measure and
does not assert a zeta zero.

## Small relative density errors still permit this test failure

`relative_density_stretched_exponential` proves, for every fixed `c>=0`,
that the same density satisfies

\[
\left|\frac{T\nu(T)}{e^T}-1\right|\le e^{-c\sqrt T}
\]

when `T>=40000` and `T>=(40000*c)^2`. This is an explicit model estimate.
It is not a transport from a prime number theorem to the literal carrier.
Consequently, adding only an eventual stretched-exponential relative
error to this generic density/trace argument does not remove its source.

There is a related literature warning: Diamond, Montgomery and Vorhauer
construct discrete **Beurling** prime systems with regular generalized
integer counting and zeros approaching `Re s=1`. Thus generalized
discreteness and multiplicative Euler structure are not, by themselves,
a license to assume the missing ordinary-prime estimate. This result is
literature context, not a theorem imported into the Lean leaf and not a
counterexample about the ordinary primes.
[Beurling primes with large oscillation](https://deepblue.lib.umich.edu/bitstream/handle/2027.42/46253/208_2005_Article_638.pdf).

## Consequence for the next arithmetic step

Do not spend the Selberg cancellation a second time or seek a stronger
generic positivity/common-phase bound: this model passes the normalized
trace cancellation and still violates the desired joined inequality.
An estimate must use an additional proved constraint on the **actual
ordinary-prime** sum. The exact integer coefficient identity may be
investigated, but its normalized source cancellation alone is insufficient.
No such new independent correlation bound is established here.

The original cofinal `399/5000` upper bound, arithmetic floor and
higher-multiplicity ceiling remain open. No zero exclusion is claimed.
Validation is limited to the leaf, namespace lint and complete axiom audit;
the module is not registered in the root. Existing numerical snapshots
are preserved, and no exhaustive probe or wider CI gate is added.
