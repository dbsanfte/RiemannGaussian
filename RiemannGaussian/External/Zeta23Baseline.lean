import Zeta23

/-!
# Kernel-checked external zeta-zero proportion baselines

This module re-exports the unconditional headline zero-proportion theorems
from the Apache-2.0 `anthropics/zeta-23-lean` development.  The imported
source is pinned and vendored under `vendor/zeta23`; it is external prior work,
not a RiemannGaussian certificate.

The counting functions below are exactly `Zeta23.Ncount` and
`Zeta23.N0star`: nontrivial zeros in the positive-ordinate dyadic window
`T < Im rho <= 2T`, counted with analytic multiplicity in the denominator and
as distinct critical-line points in the numerator.

The first theorem is the exact unconditional two-thirds baseline.  The second
is the stronger unconditional Montgomery--Taylor theorem with exact constant
`Zeta23.ThmD.HD 1`.  No decimal approximation and no bandwidth-one method
ceiling is promoted to a theorem here.
-/

namespace RiemannGaussian

noncomputable section

/-- External unconditional baseline: asymptotically at least `2/3` of zeta
zeros counted with multiplicity are represented by distinct critical-line
zeros, in the precise epsilon-form and dyadic windows of `Zeta23.thmA₀`. -/
theorem externalZeta23_twoThirds_distinctCritical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) :=
  Zeta23.thmA₀

/-- External unconditional Montgomery--Taylor baseline, with the exact
constant `HD 1` (reported numerically by the source paper as about `0.6725`). -/
theorem externalZeta23_montgomeryTaylor_distinctCritical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) :=
  Zeta23.ThmD.thmD₀

end

end RiemannGaussian
