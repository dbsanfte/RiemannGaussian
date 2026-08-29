import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEntropy

/-!
# Quadratic majorant for the Suzuki entropy frontier

The center-eliminated frontier contains the nonnegative scalar entropy
`q log q - q + 1`.  This file bounds that entropy from above by the square
`(q - 1)^2` and transports the bound through the exact canonical mass ratio.

The result is a concrete sufficient condition for every unresolved Suzuki
gap: a fixed-endpoint Chebyshev mass--moment inequality in which the endpoint
error must dominate corrected mass error squared over the endpoint square
root.  The condition is not asserted here; this file proves rigorously that
it is sufficient.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-- Corrected weighted Chebyshev mass error squared at its natural
square-root scale. -/
def suzukiChebyshevQuadraticMassCost (center b : ℝ) : ℝ :=
  (suzukiChebyshevWeightedMassError b -
      suzukiChebyshevArchimedeanSlopeLowerOrder center) ^ 2 /
    b ^ (1 / 2 : ℝ)

/-! ## Scalar entropy majorization -/

/-- On the positive half-line, relative entropy is at most squared distance
from the reference ratio one. -/
theorem suzukiChebyshevRelativeEntropy_le_sq_sub_one
    {ratio : ℝ} (hratio : 0 < ratio) :
    suzukiChebyshevRelativeEntropy ratio ≤ (ratio - 1) ^ 2 := by
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hscaled := mul_le_mul_of_nonneg_left hlog hratio.le
  unfold suzukiChebyshevRelativeEntropy
  nlinarith

/-! ## Arithmetic form of the quadratic cost -/

/-- The squared corrected mass ratio has exactly the arithmetic scale
`corrected mass error squared / sqrt(b)`. -/
theorem
    four_mul_rpow_half_mul_correctedMassRatio_sub_one_sq_eq_quadraticMassCost
    (center : ℝ) {b : ℝ} (hb : 0 < b) :
    4 * b ^ (1 / 2 : ℝ) *
        (suzukiChebyshevCorrectedMassRatio center b - 1) ^ 2 =
      suzukiChebyshevQuadraticMassCost center b := by
  have hpower : b ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hb _).ne'
  unfold suzukiChebyshevCorrectedMassRatio
    suzukiChebyshevQuadraticMassCost
  field_simp [hpower]
  ring

/-- For every positive endpoint and positive corrected ratio, the exact
entropy cost is bounded by the quadratic corrected-mass cost. -/
theorem four_mul_rpow_half_mul_relativeEntropy_le_quadraticMassCost
    (center : ℝ) {b : ℝ} (hb : 0 < b)
    (hratio : 0 < suzukiChebyshevCorrectedMassRatio center b) :
    4 * b ^ (1 / 2 : ℝ) *
        suzukiChebyshevRelativeEntropy
          (suzukiChebyshevCorrectedMassRatio center b) ≤
      suzukiChebyshevQuadraticMassCost center b := by
  calc
    4 * b ^ (1 / 2 : ℝ) *
          suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio center b) ≤
        4 * b ^ (1 / 2 : ℝ) *
          (suzukiChebyshevCorrectedMassRatio center b - 1) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (suzukiChebyshevRelativeEntropy_le_sq_sub_one hratio)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hb.le _))
    _ = suzukiChebyshevQuadraticMassCost center b :=
      four_mul_rpow_half_mul_correctedMassRatio_sub_one_sq_eq_quadraticMassCost
        center hb

/-- Canonical specialization of the entropy-to-quadratic comparison. -/
theorem four_mul_sqrt_mul_relativeEntropy_firstTail_le_quadraticMassCost
    (count : ℕ) :
    4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        suzukiChebyshevRelativeEntropy
          (suzukiChebyshevCorrectedMassRatio
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ))) ≤
      suzukiChebyshevQuadraticMassCost
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ)) := by
  apply four_mul_rpow_half_mul_relativeEntropy_le_quadraticMassCost
  · exact_mod_cast (show 0 < count + 2 by omega)
  · exact suzukiChebyshevCorrectedMassRatio_firstTail_pos count

/-! ## Quadratic mass--moment positivity criterion -/

/-- A fixed-endpoint quadratic mass--moment estimate suffices for positivity
of the corresponding literal canonical gap. -/
theorem suzukiFirstTailResetTransportGap_succ_nonnegative_of_quadraticMassCost_le
    (count : ℕ)
    (hquadratic :
      suzukiChebyshevQuadraticMassCost
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) ≤
        suzukiChebyshevEndpointCenteredError
            (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)))) :
    0 ≤ curvatureTransportGap
      (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
      (Real.log 2) suzukiSmoothCurvature
      (suzukiResetLocation (Real.log 2) 1)
      (suzukiResetWeight
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
      (suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
      (count + 1) := by
  apply
    (suzukiFirstTailResetTransportGap_succ_nonnegative_iff_entropy_le
      count).2
  exact
    (four_mul_sqrt_mul_relativeEntropy_firstTail_le_quadraticMassCost count).trans
      hquadratic

/-- Uniform validity of the quadratic mass--moment estimate beyond the two
discharged initial cutoffs implies nonnegativity of Suzuki's literal tail.
This is a sufficient implication, not a proof of its arithmetic premise. -/
theorem riemannXiSuzukiPsiNonnegative_on_logTwo_tail_of_quadraticMassMoment
    (hquadratic : ∀ count : ℕ, 1 ≤ count →
      suzukiChebyshevQuadraticMassCost
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) ≤
        suzukiChebyshevEndpointCenteredError
            (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)))) :
    ∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t := by
  apply
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_transportGap.2
  intro cutoff hcutoff
  let count : ℕ := cutoff - 1
  have hcount : 1 ≤ count := by
    dsimp only [count]
    omega
  have hgap :=
    suzukiFirstTailResetTransportGap_succ_nonnegative_of_quadraticMassCost_le
      count (hquadratic count hcount)
  have hcutoffEq : cutoff = count + 1 := by
    dsimp only [count]
    omega
  simpa only [hcutoffEq] using hgap

end

end RiemannGaussian
