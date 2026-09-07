import RiemannGaussian.EtaCoherentBandLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The actual short-window obstruction to the region logarithmic budget

The original coherent band exceeds every constant multiple of the
previous region budget on proportional physical windows. This identifies
a false strengthening of the finite-region theorem, independently of
whether the actual zero lies on the critical line. The full moving
complement, rather than a uniform separate-region estimate, must remain
available for the current bound.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A fixed scaled logarithmic region budget is subquadratic in the window parameter. -/
theorem tendsto_scaled_nat_log_budget_div_sq_zero {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    Tendsto (fun K : ℕ ↦ ((c * K : ℕ) : ℝ) * (1 + Real.log (c * K : ℕ)) ^ k / (K : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  let z : ℕ → ℝ := fun K ↦ Real.exp 1 * ((c * K : ℕ) : ℝ)
  have hz : Tendsto z atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop.const_mul_atTop hcR).const_mul_atTop (Real.exp_pos 1)
    simpa only [z, Nat.cast_mul] using h
  have ht : Tendsto (fun K : ℕ ↦ Real.log (z K) ^ k / z K) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp hz
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using h
  have hs : Tendsto (fun K : ℕ ↦ (Real.exp 1 * (c : ℝ) ^ 2) * (Real.log (z K) ^ k / z K))
      atTop (𝓝 0) := by simpa only [mul_zero] using ht.const_mul (Real.exp 1 * (c : ℝ) ^ 2)
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : Real.log (z K) = 1 + Real.log (c * K : ℕ) := by
    dsimp [z]
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
  rw [hlog]
  dsimp [z]
  push_cast
  field_simp

/-- Every actual zero supplies a strictly positive coherent physical-energy coefficient. -/
theorem coherentBand_physical_lower_coefficient_pos (rho : NontrivialZetaZero) :
    0 < ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 := by
  have hX : 0 < ‖pairedEtaXiCompletionFactor rho.1‖ := norm_pos_iff.mpr
    (pairedEtaXiCompletionFactor_ne_zero (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))
  positivity

/-- No zero-dependent constant restores the region logarithmic budget on all
full doubling windows: an explicit original inverse band exceeds it. -/
theorem exists_coherentBand_dyadic_window_exceeding_region_budget
    (rho : NontrivialZetaZero) (C : ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧
      C * pairedEtaInverseRegionBudget ((pairedEtaInverseCoherenceScale rho + 2) * K) <
        pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0
          ((pairedEtaInverseCoherenceScale rho + 2) * K)
          ((pairedEtaInverseCoherenceScale rho + 2) * K)
          (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) := by
  let c := pairedEtaInverseCoherenceScale rho + 2
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ht : Tendsto (fun K : ℕ ↦ C * (pairedEtaInverseRegionBudget (c * K) / (K : ℝ) ^ 2))
      atTop (𝓝 0) := by
    simpa only [pairedEtaInverseRegionBudget, mul_zero] using
      (tendsto_scaled_nat_log_budget_div_sq_zero hc 5).const_mul C
  have hpos : 0 < ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / (4 * (c : ℝ)) := by
    have h := div_pos (coherentBand_physical_lower_coefficient_pos rho) hcR
    simpa only [div_div] using h
  have he := ht.eventually_lt_const hpos
  obtain ⟨K, hK, hbound⟩ := ((eventually_ge_atTop 1).and he).exists
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨K, hK, ?_⟩
  have hdiv : C * pairedEtaInverseRegionBudget (c * K) / (K : ℝ) ^ 2 <
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / (4 * (c : ℝ)) := by
    simpa only [mul_div_assoc] using hbound
  exact ((div_lt_iff₀ (sq_pos_of_pos hKR)).mp hdiv).trans_le
    (pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_dyadic_lower rho hK)

end

end RiemannGaussian
