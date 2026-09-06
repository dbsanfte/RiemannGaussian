import RiemannGaussian.EtaCurrentPrincipalLowerBound

/-!
# Sharp displacement-power growth for the actual weighted return moment

The principal-term lower bound survives the finite initial arithmetic
segment and the proved summable return error. At a hypothetical actual
off-critical zero, the original return's first absolute moment is bounded
above and below by positive multiples of the same displacement power.
This tests the sharpness of the current estimates; it supplies no argument
excluding such a zero.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The integral comparison gives the matching finite lower bound for
the displacement power sum, including its initial endpoint correction. -/
theorem sub_one_div_le_sum_range_nat_add_one_rpow {r : ℝ} (hr : -1 < r) (hr0 : r ≤ 0) (K : ℕ) :
    ((K + 1 : ℝ) ^ (r + 1) - 1) / (r + 1) ≤ ∑ N ∈ Finset.range K, (N + 1 : ℝ) ^ r := by
  have hant : AntitoneOn (fun x : ℝ ↦ x ^ r) (Icc 1 (1 + (K : ℝ))) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab hr0
  calc
    _ = ∫ x : ℝ in (1 : ℝ)..1 + (K : ℝ), x ^ r := by
      rw [integral_rpow (Or.inl hr), Real.one_rpow, add_comm 1 (K : ℝ)]
    _ ≤ ∑ N ∈ Finset.range K, (1 + (N : ℝ)) ^ r := hant.integral_le_sum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N _
      rw [add_comm 1 (N : ℝ)]

/-- An eventual nonnegative term comparison bounds every finite sum
with exactly one finite initial-segment allowance. -/
theorem sum_range_le_sum_add_initial_of_eventual_bound {f g : ℕ → ℝ}
    (hf : ∀ N, 0 ≤ f N) (hg : ∀ N, 0 ≤ g N) (N₀ : ℕ)
    (htail : ∀ N, N₀ ≤ N → f N ≤ g N) (K : ℕ) :
    (∑ N ∈ Finset.range K, f N) ≤ (∑ N ∈ Finset.range K, g N) + ∑ N ∈ Finset.range N₀, f N := by
  by_cases hK : K ≤ N₀
  · have hsum : (∑ N ∈ Finset.range K, f N) ≤ ∑ N ∈ Finset.range N₀, f N :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hK) (fun N _ _ ↦ hf N)
    exact hsum.trans (le_add_of_nonneg_left (Finset.sum_nonneg (fun N _ ↦ hg N)))
  · have hN₀ : N₀ ≤ K := by omega
    have hsum : (∑ N ∈ Finset.Ico N₀ K, f N) ≤ ∑ N ∈ Finset.Ico N₀ K, g N :=
      Finset.sum_le_sum (fun N hN ↦ htail N (Finset.mem_Ico.mp hN).1)
    rw [Finset.sum_Ico_eq_sub _ hN₀, Finset.sum_Ico_eq_sub _ hN₀] at hsum
    have hstart : 0 ≤ ∑ N ∈ Finset.range N₀, g N := Finset.sum_nonneg (fun N _ ↦ hg N)
    linarith

/-- The explicit coefficient of the accumulated return's power lower
bound. Positivity is asserted only when the displacement is positive. -/
def pairedEtaCurrentReturnGrowthLowerCoefficient (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCurrentPrincipalGrowthFloor rho / pairedEtaCurrentHorizontalDisplacement rho

/-- At an actual off-critical zero the lower coefficient is strictly positive. -/
theorem pairedEtaCurrentReturnGrowthLowerCoefficient_pos (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho :=
  div_pos (pairedEtaCurrentPrincipalGrowthFloor_pos rho) (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)

/-- The lower-bound offset retains the complete proved return error,
the power-integral endpoint correction, and the finite pre-dominance segment. -/
def pairedEtaCurrentReturnGrowthLowerOffset (rho : NontrivialZetaZero) (N₀ : ℕ) : ℝ :=
  (∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N) + pairedEtaCurrentReturnGrowthLowerCoefficient rho +
    ∑ N ∈ Finset.range N₀, pairedEtaCurrentPrincipalGrowthFloor rho *
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1)

/-- Every term in the explicit finite lower-bound allowance is nonnegative. -/
theorem pairedEtaCurrentReturnGrowthLowerOffset_nonneg (rho : NontrivialZetaZero) (N₀ : ℕ) :
    0 ≤ pairedEtaCurrentReturnGrowthLowerOffset rho N₀ := by
  have hE : 0 ≤ ∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N :=
    tsum_nonneg (pairedEtaCurrentPrincipalErrorMajorant_nonneg rho)
  have hc : 0 ≤ pairedEtaCurrentReturnGrowthLowerCoefficient rho :=
    div_nonneg (pairedEtaCurrentPrincipalGrowthFloor_pos rho).le (pairedEtaCurrentHorizontalDisplacement_bounds rho).1
  have hsum : 0 ≤ ∑ N ∈ Finset.range N₀, pairedEtaCurrentPrincipalGrowthFloor rho *
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) :=
    Finset.sum_nonneg (fun N _ ↦ mul_nonneg (pairedEtaCurrentPrincipalGrowthFloor_pos rho).le (Real.rpow_nonneg (by positivity) _))
  exact add_nonneg (add_nonneg hE hc) hsum

/-- At a hypothetical off-critical zero, an actual finite initial
cutoff supplies the explicit all-cutoff power lower bound for the
unchanged complex Gaussian return's first absolute moment. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_lower_with_offset (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∃ N₀ : ℕ, ∀ K : ℕ,
      pairedEtaCurrentReturnGrowthLowerCoefficient rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
        pairedEtaCurrentReturnGrowthLowerOffset rho N₀ ≤
          ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (pairedEtaCurrentPrincipalEndpoint_weighted_lower_eventually rho hrho)
  refine ⟨N₀, fun K ↦ ?_⟩
  have he := pairedEtaCurrentHorizontalDisplacement_pos rho hrho
  have he1 := (pairedEtaCurrentHorizontalDisplacement_bounds rho).2
  have hc := (pairedEtaCurrentPrincipalGrowthFloor_pos rho).le
  have hsum := sum_range_le_sum_add_initial_of_eventual_bound
    (fun N ↦ mul_nonneg hc (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N + 1) _))
    (fun N ↦ by positivity : ∀ N : ℕ, 0 ≤ (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N|) N₀ hN₀ K
  have hpow := mul_le_mul_of_nonneg_left
    (sub_one_div_le_sum_range_nat_add_one_rpow (by linarith : -1 < pairedEtaCurrentHorizontalDisplacement rho - 1)
      (by linarith) K) hc
  rw [sub_add_cancel, Finset.mul_sum] at hpow
  have hstability := (abs_le.mp (pairedEtaLeadingCurrentLinearHeatReturn_principal_firstMoment_stability rho K)).1
  unfold pairedEtaCurrentReturnGrowthLowerOffset pairedEtaCurrentReturnGrowthLowerCoefficient
  have heq : pairedEtaCurrentPrincipalGrowthFloor rho / pairedEtaCurrentHorizontalDisplacement rho *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
      ((∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N) +
        pairedEtaCurrentPrincipalGrowthFloor rho / pairedEtaCurrentHorizontalDisplacement rho +
          ∑ N ∈ Finset.range N₀, pairedEtaCurrentPrincipalGrowthFloor rho *
            (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1)) =
      pairedEtaCurrentPrincipalGrowthFloor rho *
        (((K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho - 1) / pairedEtaCurrentHorizontalDisplacement rho) -
          (∑' N : ℕ, pairedEtaCurrentPrincipalErrorMajorant rho N) -
            ∑ N ∈ Finset.range N₀, pairedEtaCurrentPrincipalGrowthFloor rho *
              (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by ring
  rw [heq]
  linarith

/-- Off the critical line, the actual return's first absolute moment
has matching eventual upper and lower displacement powers. The lower
coefficient is explicit and strictly positive by the preceding theorem. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_power_bounds_eventually (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∀ᶠ K : ℕ in atTop,
      (pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2) * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho ≤
        (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ∧
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
        pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_lower_with_offset rho hrho
  have hc := pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (by positivity : 0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2)
  filter_upwards [ht.eventually_ge_atTop (pairedEtaCurrentReturnGrowthLowerOffset rho N₀)] with K hK
  constructor
  · have hb := hN₀ K
    dsimp only [Function.comp_apply] at hK
    linarith
  · exact pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K

/-- The unchanged weighted return moment would diverge at every actual
off-critical zero. This follows with an explicit positive power rate;
it is not an argument establishing that no such zero exists. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_tendsto_atTop_of_re_ne_half (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : Tendsto
      (fun K : ℕ ↦ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) atTop atTop := by
  have hc := pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (by positivity : 0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2)
  exact tendsto_atTop_mono' atTop
    ((pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_power_bounds_eventually rho hrho).mono (fun _ h ↦ h.1)) ht

end

end RiemannGaussian
