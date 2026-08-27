import RiemannGaussian.FiniteHardyCanonicalConclusion
import RiemannGaussian.FiniteToEntireSeparableApproximation

/-!
# The finite-to-entire Hardy frontier

This file composes the spectral-xi approximation theorem with the canonical
finite Hardy theory.  Given an upper zero of the positive spectral-xi
homotopy, it constructs separable real polynomial approximants which retain
that zero exactly.  At every finite stage, Lean proves that the canonical
influence core carries the full negative pole budget and is nonempty.

The remaining cardinality alternative is explicit: either the core is a
singleton, or the complete finite Hardy determinant satisfies the strict
multipoint bound for a positive finite-stage height floor.  No root list,
separability premise, or root-persistence premise remains to be supplied by a
future limit argument.
-/

open Filter Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The complete checked finite-stage data now available at a pinned upper
homotopy root. -/
structure CanonicalFiniteHardyFrontier
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) : Prop where
  separable : A.Separable
  homotopyRoot : (finiteEPolynomial A eta).eval z = 0
  coreBudget :
    (((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
      onePairLogDerivativeContribution eta alpha z).sum).im ≤ -1
  coreCardPos : 0 < (canonicalInsideInfluenceDiskRoots A z).card
  singletonOrStrictBound :
    (canonicalInsideInfluenceDiskRoots A z).card = 1 ∨
      ∃ a0 : ℝ, 0 < a0 ∧
        Real.sqrt
            (LinearMap.det
              (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
          eta / Real.sqrt (eta ^ 2 + a0 ^ 2)

/-- Every separable finite model with a pinned upper root satisfies the full
canonical frontier package. -/
theorem canonicalFiniteHardyFrontier_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    CanonicalFiniteHardyFrontier A eta z where
  separable := hA
  homotopyRoot := hroot
  coreBudget :=
    canonicalInsideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA heta hz hroot
  coreCardPos :=
    canonicalInsideInfluenceDiskRoots_card_pos_of_finiteE_root
      hA heta hz hroot
  singletonOrStrictBound :=
    canonicalInsideCore_card_eq_one_or_exists_finiteHardy_sqrt_det_strict_bound
      hA heta hz hroot

/-- Spectral-xi specialization of the complete current Hardy frontier.  A
single locally uniform sequence simultaneously has real coefficients,
separability, exact root pinning, the full canonical pole budget, nonempty
influence cores, and the singleton-versus-strict-determinant alternative at
every index. -/
theorem exists_riemannXiSpectral_canonicalFiniteHardyFrontier_sequence
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hroot : analyticEValue riemannXiSpectral eta z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      ∀ n, CanonicalFiniteHardyFrontier (B n) eta z := by
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence
      heta hz hroot
  refine ⟨B, hBlimit, ?_⟩
  intro n
  exact canonicalFiniteHardyFrontier_of_finiteE_root
    (hB n).1 heta hz (hB n).2

end

end RiemannGaussian
