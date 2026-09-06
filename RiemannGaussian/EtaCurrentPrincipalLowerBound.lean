import RiemannGaussian.EtaCurrentPrincipalDominance

/-!
# A displacement-power lower bound at actual arithmetic endpoints

The original odd endpoint weight times the logarithmic step is bounded
below uniformly. Together with the slower-channel dominance this gives
an explicit positive eventual power lower bound for the actual principal
term at every hypothetical off-critical zero.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual logarithmic step has a positive rational endpoint lower bound. -/
theorem pairedEtaCurrent_shiftIncrement_lower (N : ℕ) :
    2 / (2 * N + 5 : ℝ) ≤ pairedEtaLogTailShiftIncrement (N + 1) := by
  let q : ℝ := 2 * N + 3
  have hq : 0 < q := by dsimp [q]; positivity
  have hd : pairedEtaLogTailShiftIncrement (N + 1) = Real.log ((q + 2) / q) := by
    rw [Real.log_div (by positivity) hq.ne']
    unfold pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff q
    push_cast
    congr 2 <;> ring
  have he : 1 - ((q + 2) / q)⁻¹ = 2 / (q + 2) := by field_simp; ring
  rw [hd, show (2 * N + 5 : ℝ) = q + 2 by dsimp [q]; ring, ← he]
  exact Real.one_sub_inv_le_log_of_pos (by positivity)

/-- The literal odd endpoint weight cannot suppress the logarithmic step. -/
theorem pairedEtaCurrent_odd_weight_mul_shift_lower (N : ℕ) :
    (2 / 5 : ℝ) ≤ (2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) := by
  calc
    _ ≤ (2 * N + 1 : ℝ) * (2 / (2 * N + 5 : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N + 5)).2
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairedEtaCurrent_shiftIncrement_lower N) (by positivity)

/-- The slower completed endpoint decay has the same displacement power
as the prior upper bound, with an explicit factor from the endpoint ratio. -/
theorem pairedEtaCurrent_dominant_decay_lower (rho : NontrivialZetaZero) (N : ℕ) :
    (5 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) *
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) ≤
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) := by
  have hr : pairedEtaCurrentHorizontalDisplacement rho - 1 ≤ 0 := by
    linarith [(pairedEtaCurrentHorizontalDisplacement_bounds rho).2]
  have hq : 0 < (2 * N + 5 : ℝ) := by positivity
  calc
    _ = (5 * (N + 1 : ℝ)) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (by positivity)]
    _ ≤ (2 * N + 5 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) :=
      Real.rpow_le_rpow_of_nonpos hq (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hr
    _ = _ := by
      rw [Real.rpow_def_of_pos hq]
      unfold pairedEtaLogTailCutoff
      push_cast
      rw [show (2 * ((N : ℝ) + 2) + 1) = 2 * N + 5 by ring]
      congr 1
      ring

/-- An explicit positive coefficient in the eventual principal-term
power lower bound; it retains the actual dominant completion channel. -/
def pairedEtaCurrentPrincipalGrowthFloor (rho : NontrivialZetaZero) : ℝ :=
  (pairedEtaCurrentDominantCoefficient rho / 5) * (5 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1)

/-- The principal growth coefficient is strictly positive. -/
theorem pairedEtaCurrentPrincipalGrowthFloor_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCurrentPrincipalGrowthFloor rho := by
  have hA := pairedEtaCurrentDominantCoefficient_pos rho
  unfold pairedEtaCurrentPrincipalGrowthFloor
  positivity

/-- At every hypothetical off-critical zero, the actual principal
term eventually has a positive odd-weighted displacement-power lower bound. -/
theorem pairedEtaCurrentPrincipalEndpoint_weighted_lower_eventually (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    ∀ᶠ N : ℕ in atTop, pairedEtaCurrentPrincipalGrowthFloor rho *
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) ≤
        (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N| := by
  have hA := pairedEtaCurrentDominantCoefficient_pos rho
  filter_upwards [pairedEtaCurrentPrincipalEndpoint_dominant_lower_eventually rho hrho] with N hN
  calc
    _ = ((2 / 5 : ℝ) * ((5 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) *
        (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1))) *
          (pairedEtaCurrentDominantCoefficient rho / 2) := by unfold pairedEtaCurrentPrincipalGrowthFloor; ring
    _ ≤ (((2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2))) *
          (pairedEtaCurrentDominantCoefficient rho / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (pairedEtaCurrent_odd_weight_mul_shift_lower N)
        (pairedEtaCurrent_dominant_decay_lower rho N) (by positivity)
        (mul_nonneg (by positivity) (pairedEtaLogTailShiftIncrement_pos (N + 1)).le)) (by positivity)
    _ = (2 * N + 1 : ℝ) * (pairedEtaLogTailShiftIncrement (N + 1) *
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
          (pairedEtaCurrentDominantCoefficient rho / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

end

end RiemannGaussian
