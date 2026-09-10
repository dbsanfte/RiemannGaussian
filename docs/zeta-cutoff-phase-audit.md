# Exact cutoff and phase checks

Two Lean identities clarify the scope of estimates for the surviving
rough squarefree sum. They do not supply its missing signed upper bound.
The [reflected head bound](zeta-rough-moebius-hyperbola.md) remains valid;
the complete multiplicity source survives above that head.

Write

\[
M_D(n)=\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d),\qquad
L_D(n)=\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d)\log d.
\]

Let \(B_{D,S}(n)\) be \(M_D(n)L_D(n)\) on rough squarefree integers,
and zero elsewhere. Let \(b_S(n)\) be \(\log n\) on rough squarefree
composites, and zero elsewhere. The theorem
`RoughMoebiusHyperbola.coefficient_half_cutoff` proves exactly

\[
B_{\lfloor n/2\rfloor,S}(n)=b_S(n).
\]

All excluded cases, ordinary primes, zero and the unit are included.
`response_one` lifts this equality to the complete arithmetic response
with the original complex kernel. Genuine series convergence for
\(\Re s>1\) is supplied by `hasSum_response` in the
[same module](../RiemannGaussian/ZetaRoughMoebiusHyperbola.lean).
Thus a bound for one cutoff per moment order cannot simply be reused
when the cutoff depends on each summation integer: such dependence
already recovers the full composite logarithmic source in this example.

For the phase calculation define \(\chi_y(x)=e^{-iy\log x}\). It has
unit norm, and for positive integers \(d,m\),

\[
\chi_y(dm)=\chi_y(d)\chi_y(m).
\]

For arbitrary finite positive index sets and an arbitrary complex matrix
\(c(d,m)\), retain the whole factorial kernel in

\[
\mathcal B_y(a,b)=\sum_d\sum_m a(d)b(m)c(d,m)
K_{p,N}(\sigma+iy,dm).
\]

The theorem `MultiplicativePhase.bilinear_shift` proves

\[
\mathcal B_{y+z}(a,b)=\mathcal B_y(a\chi_z,b\chi_z).
\]

The polynomial amplitude and the matrix stay fixed. The matrix may
contain all cutoff, sieve, coprimality and other coupled restrictions.
Because the modulation preserves coefficient magnitudes,
`uniform_bound_iff_zero_height` proves that a bound for **every complex
coefficient pair** under fixed magnitude budgets is equivalent at height
\(y\) and at height zero. Both results are in
[`ZetaMultiplicativePhase.lean`](../RiemannGaussian/ZetaMultiplicativePhase.lean).

This equivalence does not apply to a family constrained to be the actual
fixed Möbius coefficients: arbitrary complex phase modulation need not
preserve that constraint. It therefore does not rule out a useful
coefficient-specific correlation estimate, or all matrix methods. It
identifies which information a magnitude-only uniform estimate cannot
use. Neither identity establishes the required cofinal signed saving,
improves the existing zero-free region, or proves RH.
