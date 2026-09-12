# Gaussian source, complete divisor remainder and half-plane sign

This slice proves the actual zero-side ingredients for a Gaussian-smoothed
strip comparison. It contains six modules and 56 public theorems. It does
not by itself prove the smoothed prime/strip comparison or a larger zero-free
region. The subsequent [exact bridge](zeta-gaussian-strip-bridge.md) now
provides that comparison at `Re(s)>1`. The independent ordinary-prime floor in the global RH contradiction
remains open. Commits and pushes remain on hold.

## Original complex endpoints

For every `B>0`, define the genuine half-line moments

```text
M_n(B,z) = integral_0^infinity v^n exp(-B*v^2) exp(-z*v) dv,
F_B(z)   = M_0(B,z).
```

Every original complex integrand is absolutely integrable at every complex
`z`; its boundary value at positive infinity is zero. The exact recurrences
in [GaussianComplexHalfMoments](../RiemannGaussian/GaussianComplexHalfMoments.lean)
retain the damping phase and every endpoint:

```text
2B*M_1 + z*M_0 = 1,
2B*M_(n+2) + z*M_(n+1) = (n+1)*M_n,
z^3*F_B(z)-z^2 = -2B + 12B^2*M_1 - 8B^3*M_3.
```

The last identity is undivided and remains valid at `z=0`. Away from zero,
it gives the complete pole remainder `R_B(z)=F_B(z)-1/z`. On `Re(z)>=0`,
the first and third complex moments are bounded by their actual positive
zero-damping values `1/(2B)` and `1/(2B^2)`. Therefore

```text
norm(R_B(z)) <= 12B / norm(z)^3.
```

[norm_remainder_le](../RiemannGaussian/GaussianLaplacePoleRemainder.lean)
uses the vanishing first Gaussian endpoint derivative. It introduces no
artificial square-root-scale endpoint cost. Both signed odd moments remain
available in the upstream exact identity.

## All-window positivity and actual zeta mass

[PositiveCosineLaplace](../RiemannGaussian/PositiveCosineLaplace.lean)
proves an all-window theorem: a continuous real window with all real
exponential moments and nonnegative complete boundary cosine transform has
nonnegative real Laplace transform on the entire closed right half-plane.
The proof exhausts the existing Fermi reflection strips. A genuine complex
dominated-convergence argument removes the moving reflected partner; the
exact partition recovers the original window with its full normalization.

The exact Gaussian Fourier identity supplies every boundary sign, so
`Re(F_B(z))>=0` for all `B>0` and `Re(z)>=0`. At every actual nontrivial
zero `rho`, the known strict inequality `Re(rho)<1` makes `s-rho` have
positive real part whenever `Re(s)>=1`.

Writing `m_rho` for its analytic multiplicity, Lean proves

```text
mass_B(s,rho) = m_rho * Re(F_B(s-rho)) >= 0,

sum_rho mass_B(s,rho)
  = Re(xi'/xi(s)) + Re(sum_rho m_rho * R_B(s-rho)).
```

Every real mass and the full complex remainder are absolutely summable.
The proof does not split or claim absolute convergence of the unpaired
complex pole series. At `s=sigma+i*Im(rho)`, the selected source is exactly
`m_rho*halfGaussian(B,sigma-Re(rho))`; any finite selected zero set is bounded
by the entire nonnegative mass. See
[tsum_mass_eq and selected_source_le](../RiemannGaussian/ZetaGaussianLaplaceMass.lean).

## Complete height tails

[ZetaGaussianPoleRemainder](../RiemannGaussian/ZetaGaussianPoleRemainder.lean)
retains the original complex term `m_rho*R_B(s-rho)`. Its complete finite
height windows and outside tails reconstruct that term and its full sum
exactly. If `H>=max(2*abs(Im(s)),1)`, then

```text
norm(sum_(abs(Im(rho))>H) m_rho*R_B(s-rho))
  <= (192B/H) * divisorTail(H),

divisorTail(H) = sum_(abs(Im(rho))>H) m_rho/(1+Im(rho)^2).
```

The existing genuine divisor tail tends to zero. The outside complex sum
vanishes and the complete finite windows converge to the original full
complex remainder. The extra inverse-height factor is retained.

## An elementary allowance outside a distance cutoff

The distance comparison in
[ZetaGaussianDistanceRemainder](../RiemannGaussian/ZetaGaussianDistanceRemainder.lean)
is stronger for the strip argument. For `Re(z)>=0` and `norm(z)>=eta>0`,

```text
1/norm(z)^2 <= (2/eta) * (Re(z)+eta)/norm(z+eta)^2.
```

This follows from the nonnegative product
`(2Re(z)+eta)*(norm(z)^2-eta^2)`, before adding any zero terms.
With cubic Gaussian decay and the complete actual Poisson identity it gives

```text
norm(sum_(norm(s-rho)>=eta) m_rho*R_B(s-rho))
  <= (24B/eta^2) * Re(xi'/xi(s+eta)),    Re(s)>=1.
```

The near ball has genuinely finite support in the actual divisor. It and
the far complement reconstruct the entire complex remainder exactly;
near-zero terms are not charged to this bound or silently discarded.

On the boundary `s=1+i*t`, for `0<eta<=1/4`, the terminal theorem
`norm_tsum_farTerm_le_elementary` removes the remaining xi value:

```text
norm(sum_(norm(1+i*t-rho)>=eta) m_rho*R_B(1+i*t-rho))
  <= (24B/eta^2) * C_eta(t),

C_eta(t) = eta/(eta^2+t^2) + 1/eta + 448*log(22)
             + log(1+eta+abs(t))/2.
```

The proof uses the actual global xi identity, the exact nonreal pole,
the complete prime-series bound by the real axis, the proved real-axis
zeta allowance and the existing half-logarithm completion estimate.
No unknown zeta value, integral, divisor constant or tail is left in this
outside-distance allowance.

The sharper theorem `norm_tsum_farTerm_le_elementary_reserve` retains the
exact nearby Poisson mass:

```text
P_near(eta,s) = sum_(norm(s-rho)<eta)
  m_rho*(Re(s-rho)+eta)/norm(s+eta-rho)^2,

norm(sum_(norm(1+i*t-rho)>=eta) m_rho*R_B(1+i*t-rho))
  <= (24B/eta^2) * (C_eta(t)-P_near(eta,1+i*t)).
```

For each nearby zero, `nearPoisson_lower` proves its individual reserve is
at least `m_rho/(2*eta)`. The full phase and distance dependence remain
available in `P_near`; this lower bound is a downstream estimate. The
retained negative cost pays the nearby cotangent correction in the subsequent
[complete compensation theorem](zeta-gaussian-near-cancellation.md).

## Remaining bridge and scope

These results provide a positive actual Gaussian zero source, a complete
complex residue correction and a proved elementary allowance for the
entire distant complement. The subsequent
[exact Gaussian bridge](zeta-gaussian-strip-bridge.md) identifies the source
with the original complex smoothed prime series and proves its signed strip
bound at `Re(s)>1`. It retains the cotangent-minus-pole correction, all nearby
zeros, the original prime phases and the smoothed pole and Archimedean terms.
The subsequent [full phase-family cost](zeta-gaussian-phase-band.md) now
establishes an explicit zero-free band and three exact width comparisons
at matching heights, with every source and cost premise discharged.

The sign of `Re(F_B)` alone does not establish the sign of
`Re(F_B(z)+pi/(2*eta)*cot(pi*z/(2*eta))-1/z)`. The subsequent
[nearby-source theorem](zeta-gaussian-near-cancellation.md) now bounds this
entire expression and matches its loss exactly to each zero's own Poisson
reserve. It retains any finite selected source in the full signed bound.
That compensation is now used in the exact smoothed prime/strip bridge.

The classical smoothed strip comparison in
[Yang, Lemma 4.7](https://arxiv.org/html/2301.03165v2) is a guide for that
construction. The existing
[complete unsmoothed strip budget](zeta-strip-phase-budget.md) remains
available. The downstream band has an explicit starting height. No coefficient
search, exhaustive world-record or historical novelty audit, independent
ordinary-prime floor or RH proof is claimed by this upstream slice.

## Validation of this six-module slice

All six modules pass direct elaboration with warnings treated as errors and
are imported by the root library. The focused build passes 4,621 jobs; the
full build passes 10,327. Root verbose lint reports zero errors in 19,634
declarations plus 11,567 generated declarations, across all 14 linters.
Whole-project declaration lint passes. All 56 new public theorems have
explicit transitive axiom audits containing only `propext`, `Classical.choice`
and `Quot.sound`.

The compiled inventory contains 1,480 project modules, 31,237 declarations
and 27,406 theorems, with zero project axioms and zero placeholder-dependent
declarations. `rhImplied` remains false. The source audit includes untracked
Lean files. These are local results; no new commit, push or remote CI result
is claimed.
