import RiemannGaussian.EtaMoebiusHyperbolaSplit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic square windows for the exact Möbius hyperbola

The divisor cut is `2^k`, the starting cutoff and averaging length are
its square. The quotient representation is valid at every physical point
in that window, including its first point.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

/-- The dyadic divisor cutoff used in the completed-source hyperbola split. -/
def pairedEtaMoebiusHyperbolaCutoff (k : ℕ) : ℕ := 2 ^ k

/-- The physical starting cutoff and window length are both the square of the divisor cutoff. -/
def pairedEtaMoebiusHyperbolaScale (k : ℕ) : ℕ := pairedEtaMoebiusHyperbolaCutoff k ^ 2

/-- Every scheduled divisor cutoff is positive, including the initial one. -/
theorem pairedEtaMoebiusHyperbolaCutoff_pos (k : ℕ) : 0 < pairedEtaMoebiusHyperbolaCutoff k :=
  pow_pos (by norm_num) k

/-- Every scheduled physical square window has positive length. -/
theorem pairedEtaMoebiusHyperbolaScale_pos (k : ℕ) : 0 < pairedEtaMoebiusHyperbolaScale k :=
  pow_pos (pairedEtaMoebiusHyperbolaCutoff_pos k) 2

/-- The divisor cutoff tends to infinity along the actual dyadic schedule. -/
theorem pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop :
    Tendsto pairedEtaMoebiusHyperbolaCutoff atTop atTop := by
  apply tendsto_atTop_mono (fun k ↦ (show k < 2 ^ k from Nat.lt_two_pow_self).le) tendsto_id

/-- Every physical point in a scheduled square window has exactly the stated fixed quotient-family reconstruction. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_hyperbola_eq_quotientFamily
    (rho : NontrivialZetaZero) (k : ℕ) {n : ℕ} (hn : n < pairedEtaMoebiusHyperbolaScale k) :
    pairedEtaCompletedMoebiusLargeAggregate rho (pairedEtaMoebiusHyperbolaScale k + n)
      (pairedEtaMoebiusHyperbolaCutoff k) =
      ∑ q ∈ Finset.Icc 1 (2 * pairedEtaMoebiusHyperbolaCutoff k),
        pairedEtaCompletedMoebiusLargeQuotientFamily rho (pairedEtaMoebiusHyperbolaCutoff k)
          (pairedEtaMoebiusHyperbolaScale k + n) q := by
  apply pairedEtaCompletedMoebiusLargeAggregate_eq_fixedQuotientFamily rho
    (pairedEtaMoebiusHyperbolaCutoff_pos k)
  · exact Nat.le_add_right _ _
  · change pairedEtaMoebiusHyperbolaScale k + n < 2 * pairedEtaMoebiusHyperbolaScale k
    omega

end RiemannGaussian
