# Global signed density-prefix cancellation

This local slice improves an arithmetic scalar already present in the
whole masked-carrier estimate. It does not prove the numerical floor,
source-scale decay, a contradiction, or a zero exclusion. No additional
population is paid at source scale.

The preceding many-bin audit ruled out automatic within-label
orthogonality. The present proof instead uses an integer divisor
convolution across all Möbius parities. Its classical ingredient is the
weighted reciprocal-prefix inequality in [Terence Tao, *A remark on partial
sums involving the Möbius function*](https://arxiv.org/abs/0908.4323),
Theorem 1.1 and Remark 2.1. The Lean proof is elementary and requires no
prime-distribution estimate, hypothetical zero, or bilinear hypothesis.

The source is [ZetaRieszSignedDensityCancellation.lean](../RiemannGaussian/ZetaRieszSignedDensityCancellation.lean).

## The exact arithmetic quantity improved

Write \(\rho_S=\mathrm{density}(S)\) for the original rough squarefree
density. For every actual excluded-prime set \(S\), the existing coefficient
is exactly

\[
\operatorname{Re}\bigl(\mu(n)\,\mathrm{markedDensity}(S,n)\bigr)
=\rho_S\frac{\mu(n)}{n}\prod_{p\mid n}\alpha_S(p),
\qquad
\alpha_S(p)=
\begin{cases}
0,&p\in S,\\
p/(p+1),&p\notin S.
\end{cases}
\]

Nonsquarefree labels and excluded-prime hits remain exactly zero. The
weights lie in \([0,1]\). The new checked theorem therefore gives, uniformly
over every integer cutoff and every finite prime exclusion,

\[
\boxed{|\mathrm{roughDensityPrefix}(S,D)|\le\rho_S.}
\]

The previous rough-prefix allowance was \(1+\log D\). Without exclusions,
the new bound is the exact squarefree density \(\rho\), improving the
previous constant two. The classical unweighted reciprocal Möbius prefix
also now has allowance one rather than two.

This is cancellation across the complete arithmetic prefix, including all
prime counts. It does not assert cancellation of arbitrary masked
subsets of that prefix.

## Propagation to the actual retained carrier

Let \(c_p=L-\log p\), and retain the literal hinge increments

\[
\beta_{p,D}=(c_p-\log D)_+-(c_p-\log(D+1))_+.
\]

Their complete sum is \((c_p)_+\), including the exact terminal cutoff.
After exact owner normalization,

\[
\Lambda_p=\frac{p+1}{p}
\sum_{D\le\lfloor e^{c_p}\rfloor}
\beta_{p,D}\,\mathrm{roughDensityPrefix}(\{p\},D)
\quad\text{satisfies}\quad
|\Lambda_p|\le\rho(c_p)_+.
\]

The old logarithmic prefix estimate allows a quadratic hinge-height
loss. This proof reduces that scalar allowance to a linear one before
introducing any cofactor price.

For the SAME squarefree owner rows and original masked weight \(w\), put

\[
U_p=\sum_a w(a,p)\,R_L(a),\qquad V_p=\sum_a w(a,p).
\]

`literal_whole_carrier_signed_bounds` applies directly to every
\(B\subseteq\mathrm{coreBand}\), with all counts, phases, physical support,
factorial and allocation masks retained:

\[
\boxed{
\rho\sum_p\bigl(U_p-(c_p)_+|V_p|\bigr)-E_N
\le\rho J_B
\le\rho\sum_p\bigl(U_p+(c_p)_+|V_p|\bigr)+E_N.
}
\]

Here \(J_B\) is the original scaled residual sum, not a new carrier.
The cofactor moment \(U_p\) remains signed. The second price uses
\(\left|\sum_a w(a,p)\right|\), never \(\sum_a|w(a,p)|\).

The comparison error is still exactly the previously established

\[
E_N=6C e^{-N/128}\sum_p(2+(c_p)_+)(c_p)_+
\sum_k k\,|q(k,p)-q(k+1,p)|.
\]

The smooth row weight \(q\) retains the original physical/count masks
before squarefreeness is placed inside the arithmetic measure. Its
variation is **unpaid**. The exponential prefactor alone is not a payment.
Both \(U_p\) and the source-scaled aggregate cost of \(V_p\) remain open.
No claim of a fixed power saving follows from the new scalar bound.

## Phase boundary checked rather than assumed

The real-weight theorem cannot be extended unchanged to complex phase
weights. For actual integer labels one and two, at
\(y=19\pi/\log 2>54\), Lean proves exactly

\[
\sum_{n=1}^{2}\frac{\mu(n)}n
\prod_{p\mid n}\frac{p}{p+1}\cos(y\log n)=\frac43>1.
\]

This is a counterexample to a universal phase-twisted prefix theorem,
not to the literal core floor or a particular zeta ordinate. It explains
why the new real density estimate does not independently pay the
correlated cofactor phase.

The optional `scripts/probe_riesz_signed_density.py` checks six actual
prime-exclusion cases, with exact rational prefix checks through128 and
floating regressions through20000. It checks the original hinge means
and the same phase example. It is outside ordinary CI and is not a
floor certificate.

## Local verification and remaining goal

The companion audit lists all12 public proofs, their transitive standard
axioms, focused warning-as-error checks, source hashes and the optional
regression. Wide publication checks are deferred under the current local
iteration instruction. Public README/explorer endpoints are unchanged.

The remaining quantitative target is still an independent joint
\(-79/1000\) floor. This slice removes an avoidable scalar cutoff loss;
the actual signed cofactor correlations, mask variation, funding debit
and final aggregate estimate still require proof.
