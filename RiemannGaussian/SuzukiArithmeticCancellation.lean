/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ChebyshevMoebiusCancellation
import RiemannGaussian.SuzukiMassShiftBudget

/-!
# Arithmetic cancellation in the original Suzuki mass and work

The proved Chebyshev cancellation is transported through the original Abel
mass, keeping the finite old mass and every prime-power event. This is an
unconditional arithmetic estimate; it does not give the logarithmic signed
floor needed to exclude an off-critical zero.
-/

open Filter MeasureTheory
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual Chebyshev error admits every positive linear coefficient with one finite remainder valid on the whole multiplicative range. -/
theorem exists_chebyshevPsi_error_linear_remainder {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ e * x + C := by
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp chebyshevPsi_error_div_tendsto_zero e he
  let B := max A 1
  refine ⟨5 * B, by dsimp [B]; positivity, fun x hx ↦ ?_⟩
  by_cases hBx : B ≤ x
  · have h := hA x ((le_max_left _ _).trans hBx)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (zero_lt_one.trans_le hx),
      div_lt_iff₀ (zero_lt_one.trans_le hx)] at h
    have hB : 0 ≤ 5 * B := by dsimp [B]; positivity
    linarith
  · have h := abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hx
    have hsmall : x ≤ B := le_of_not_ge hBx
    have hpos : 0 ≤ e * x := mul_nonneg he.le (zero_le_one.trans hx)
    linarith

private theorem power_integrable (r b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (Set.Ioc 1 b) := by
  apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  exact (Real.continuousAt_rpow_const x r
    (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt

private theorem psi_weight_integrable (b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-3 / 2 : ℝ) * Chebyshev.psi x) (Set.Ioc 1 b) := by
  have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-3 / 2 : ℝ)) (Set.Icc 1 b) := by
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact (Real.continuousAt_rpow_const x (-3 / 2 : ℝ)
      (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  have h := integrableOn_mul_sum_Icc (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hp
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  exact h.mono_set Set.Ioc_subset_Icc_self

private theorem weighted_linear_eq (a c : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) * (a * x + c) = a * x ^ (-1 / 2 : ℝ) + c * x ^ (-3 / 2 : ℝ) := by
  have hp : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hx.ne']
    norm_num
  rw [mul_add]
  linear_combination a * hp

private theorem linear_weight_integrable (a c b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-3 / 2 : ℝ) * (a * x + c)) (Set.Ioc 1 b) := by
  apply ((power_integrable (-1 / 2) b).const_mul a |>.add
    ((power_integrable (-3 / 2) b).const_mul c)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (weighted_linear_eq a c (zero_lt_one.trans hx.1)).symm

private theorem linear_mass_transform (a c : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    b ^ (-1 / 2 : ℝ) * (a * b + c) +
        (1 / 2 : ℝ) * ∫ x in Set.Ioc 1 b, x ^ (-3 / 2 : ℝ) * (a * x + c) =
      a * (2 * Real.sqrt b - 1) + c := by
  have hbpos := zero_lt_one.trans_le hb
  have hp : b ^ (-1 / 2 : ℝ) * b = Real.sqrt b := by
    rw [← Real.rpow_add_one hbpos.ne', Real.sqrt_eq_rpow]
    norm_num
  have hi : (∫ x in Set.Ioc 1 b, x ^ (-3 / 2 : ℝ) * (a * x + c)) =
      a * (2 * (Real.sqrt b - 1)) + c * (2 * (1 - b ^ (-1 / 2 : ℝ))) := by
    calc
      _ = ∫ x in Set.Ioc 1 b, a * x ^ (-1 / 2 : ℝ) + c * x ^ (-3 / 2 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        exact weighted_linear_eq a c (zero_lt_one.trans hx.1)
      _ = a * (∫ x in Set.Ioc 1 b, x ^ (-1 / 2 : ℝ)) +
          c * (∫ x in Set.Ioc 1 b, x ^ (-3 / 2 : ℝ)) := by
        rw [integral_add ((power_integrable (-1 / 2) b).const_mul a)
          ((power_integrable (-3 / 2) b).const_mul c), integral_const_mul, integral_const_mul]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hb, ← intervalIntegral.integral_of_le hb,
          integral_rpow (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num)),
          integral_rpow (r := (-3 / 2 : ℝ)) (Or.inr ⟨by norm_num, by
            rw [Set.uIcc_of_le hb]; simp⟩), Real.sqrt_eq_rpow]
        norm_num
        ring
  rw [hi]
  linear_combination a * hp

private theorem mass_linear_bounds {a c d f : ℝ} {b : ℝ} (hb : 1 ≤ b)
    (hlo : ∀ x : ℝ, 1 ≤ x → a * x + c ≤ Chebyshev.psi x)
    (hhi : ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ d * x + f) :
    a * (2 * Real.sqrt b - 1) + c ≤ suzukiChebyshevWeightedMass b ∧
      suzukiChebyshevWeightedMass b ≤ d * (2 * Real.sqrt b - 1) + f := by
  have hw : 0 ≤ b ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hb) _
  have hboundlo := mul_le_mul_of_nonneg_left (hlo b hb) hw
  have hboundhi := mul_le_mul_of_nonneg_left (hhi b hb) hw
  have hintlo := setIntegral_mono_on (linear_weight_integrable a c b) (psi_weight_integrable b)
    measurableSet_Ioc (fun x hx ↦ mul_le_mul_of_nonneg_left (hlo x hx.1.le)
      (Real.rpow_nonneg (zero_lt_one.trans hx.1).le (-3 / 2)))
  have hinthi := setIntegral_mono_on (psi_weight_integrable b) (linear_weight_integrable d f b)
    measurableSet_Ioc (fun x hx ↦ mul_le_mul_of_nonneg_left (hhi x hx.1.le)
      (Real.rpow_nonneg (zero_lt_one.trans hx.1).le (-3 / 2)))
  rw [suzukiChebyshevWeightedMass_eq_explicit]
  constructor
  · rw [← linear_mass_transform a c hb]
    linarith
  · rw [← linear_mass_transform d f hb]
    linarith

/-- A complete Chebyshev error envelope transfers through the actual weighted Abel mass without losing the finite constant. -/
theorem abs_suzukiWeightedMassError_le_of_chebyshev_envelope {e C : ℝ} (he : 0 ≤ e)
    (hbound : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ e * x + C)
    {b : ℝ} (hb : 1 ≤ b) :
    |suzukiChebyshevWeightedMassError b| ≤ 2 * e * Real.sqrt b + C := by
  have hlo (x : ℝ) (hx : 1 ≤ x) : (1 - e) * x + -C ≤ Chebyshev.psi x := by
    have h := (abs_le.mp (hbound x hx)).1
    linarith
  have hhi (x : ℝ) (hx : 1 ≤ x) : Chebyshev.psi x ≤ (1 + e) * x + C := by
    have h := (abs_le.mp (hbound x hx)).2
    linarith
  obtain ⟨hl, hu⟩ := mass_linear_bounds hb hlo hhi
  rw [suzukiChebyshevWeightedMassError, suzukiChebyshevContinuousMass,
    ← Real.sqrt_eq_rpow, abs_le]
  constructor <;> nlinarith

/-- The original weighted-mass error is smaller than the square-root arithmetic scale, unconditionally. -/
theorem suzukiWeightedMassError_div_sqrt_tendsto_zero :
    Tendsto (fun b : ℝ ↦ suzukiChebyshevWeightedMassError b / Real.sqrt b) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := exists_chebyshevPsi_error_linear_remainder (by linarith : 0 < eps / 4)
  have hlim : Tendsto (fun b : ℝ ↦ C / Real.sqrt b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hlim (eps / 2) (by linarith)
  refine ⟨max 1 A, fun b hb ↦ ?_⟩
  have hb1 := (le_max_left _ _).trans hb
  have hbs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hb1)
  have h := abs_suzukiWeightedMassError_le_of_chebyshev_envelope (by linarith : 0 ≤ eps / 4) hbound hb1
  have hs := hA b ((le_max_right _ _).trans hb)
  rw [Real.dist_eq, sub_zero] at hs ⊢
  rw [abs_div, abs_of_pos hbs]
  calc
    _ ≤ (2 * (eps / 4) * Real.sqrt b + C) / Real.sqrt b :=
      div_le_div_of_nonneg_right h hbs.le
    _ = eps / 2 + C / Real.sqrt b := by field_simp; ring
    _ < eps := by have := le_abs_self (C / Real.sqrt b); linarith

/-- The full arithmetic mass has leading coefficient two at the square-root scale. -/
theorem suzukiWeightedMass_div_sqrt_tendsto_two :
    Tendsto (fun b : ℝ ↦ suzukiChebyshevWeightedMass b / Real.sqrt b) atTop (𝓝 2) := by
  have hi : Tendsto (fun b : ℝ ↦ 1 / Real.sqrt b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h := (suzukiWeightedMassError_div_sqrt_tendsto_zero.add_const 2).sub hi
  norm_num only [zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [suzukiChebyshevWeightedMassError, suzukiChebyshevContinuousMass, ← Real.sqrt_eq_rpow]
  have hs := (Real.sqrt_pos.mpr hb).ne'
  field_simp
  ring

private theorem endpoint_tendsto_atTop (k : ℕ) :
    Tendsto (fun j : ℕ ↦ ((j + k : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_add] using
    (tendsto_atTop_add_const_right atTop (k : ℝ) tendsto_natCast_atTop_atTop)

private theorem next_weight_div_sqrt_tendsto_zero :
    Tendsto (fun j : ℕ ↦ suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fun _ ↦ div_nonneg (suzukiPrimeWeight_nonnegative _) (Real.sqrt_nonneg _))
  · exact Eventually.of_forall (fun j ↦ div_le_div_of_nonneg_right (suzukiPrimeWeight_le_two (j + 1))
      (Real.sqrt_nonneg _))
  · exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 3))

/-- The corrected old-mass ratio tends to one at its actual next-event endpoint; the intervening atom is included in the estimate. -/
theorem suzukiFirstTailCorrectedMassRatio_tendsto_one :
    Tendsto suzukiFirstTailCorrectedMassRatio atTop (𝓝 1) := by
  have hM := suzukiWeightedMass_div_sqrt_tendsto_two.comp (endpoint_tendsto_atTop 3)
  have hc : Tendsto (fun j : ℕ ↦ suzukiArchimedeanSlopeConstant / Real.sqrt (j + 3 : ℕ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 3))
  have h := ((hM.sub next_weight_div_sqrt_tendsto_zero).sub hc).div_const 2
  norm_num only [sub_zero, div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
  apply h.congr'
  exact Eventually.of_forall fun j ↦ by
    change ((suzukiChebyshevWeightedMass (j + 3 : ℕ) / Real.sqrt (j + 3 : ℕ) -
      suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ)) -
      suzukiArchimedeanSlopeConstant / Real.sqrt (j + 3 : ℕ)) / 2 = _
    have he := suzukiOldPrimeMass_succ j
    have hmass : suzukiOldPrimeMass (j + 1) = suzukiChebyshevWeightedMass (j + 3 : ℕ) := by
      rw [suzukiOldPrimeMass, screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
    rw [← hmass, he]
    unfold suzukiFirstTailCorrectedMassRatio suzukiOldPrimeMass
    ring

private theorem log_ratio_abs_tendsto_zero :
    Tendsto (fun j : ℕ ↦ |Real.log (suzukiFirstTailCorrectedMassRatio j)|) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.log_one, abs_zero] using
    ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      suzukiFirstTailCorrectedMassRatio_tendsto_one).abs

private theorem sum_next_weights_le_old_mass (count : ℕ) :
    (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1)) ≤ suzukiOldPrimeMass count := by
  have he : (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1)) =
      suzukiOldPrimeMass count - suzukiOldPrimeMass 0 := by
    calc
      _ = ∑ j ∈ Finset.range count, (suzukiOldPrimeMass (j + 1) - suzukiOldPrimeMass j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [suzukiOldPrimeMass_succ]
        ring
      _ = _ := Finset.sum_range_sub suzukiOldPrimeMass count
  rw [he]
  linarith [suzukiOldPrimeMass_pos 0]

/-- The complete absolute mass-log work admits every positive multiple of the actual old mass, with one finite prefix remainder. -/
theorem exists_suzukiMassLogWork_absolute_mass_remainder {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ count : ℕ,
      (∑ j ∈ Finset.range count, |suzukiFirstTailMassLogWork j|) ≤ e * suzukiOldPrimeMass count + C := by
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp log_ratio_abs_tendsto_zero (e / 2) (by linarith)
  let C := ∑ j ∈ Finset.range A, |suzukiFirstTailMassLogWork j|
  refine ⟨C, Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), fun count ↦ ?_⟩
  have hterm (j : ℕ) : |suzukiFirstTailMassLogWork j| ≤
      e * suzukiPrimeWeight (j + 1) + if j < A then |suzukiFirstTailMassLogWork j| else 0 := by
    by_cases hj : j < A
    · rw [if_pos hj]
      have hn := mul_nonneg he.le (suzukiPrimeWeight_nonnegative (j + 1))
      linarith
    · rw [if_neg hj, add_zero, suzukiFirstTailMassLogWork_eq_neg_two_mul_log_ratio, abs_mul,
        abs_mul, abs_of_nonneg (suzukiPrimeWeight_nonnegative _)]
      norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have h := hA j (le_of_not_gt hj)
      rw [Real.dist_eq, sub_zero, abs_abs] at h
      have hs : 2 * |Real.log (suzukiFirstTailCorrectedMassRatio j)| ≤ e := by linarith
      have hm := mul_le_mul_of_nonneg_right hs (suzukiPrimeWeight_nonnegative (j + 1))
      nlinarith
  have hhead : (∑ j ∈ Finset.range count, if j < A then |suzukiFirstTailMassLogWork j| else 0) ≤ C := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j _ _
      exact abs_nonneg _
  calc
    _ ≤ ∑ j ∈ Finset.range count,
        (e * suzukiPrimeWeight (j + 1) + if j < A then |suzukiFirstTailMassLogWork j| else 0) :=
      Finset.sum_le_sum (fun j _ ↦ hterm j)
    _ = e * (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1)) +
        ∑ j ∈ Finset.range count, if j < A then |suzukiFirstTailMassLogWork j| else 0 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (sum_next_weights_le_old_mass count) he.le) hhead

/-- The complete absolute mass-log work is `o(sqrt N)`, using cancellation in the actual arithmetic mass rather than a formal normalization premise. -/
theorem suzukiMassLogWork_absolute_sum_div_sqrt_tendsto_zero :
    Tendsto (fun count : ℕ ↦ (∑ j ∈ Finset.range count, |suzukiFirstTailMassLogWork j|) /
      Real.sqrt (count + 2 : ℕ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := exists_suzukiMassLogWork_absolute_mass_remainder (by linarith : 0 < eps / 24)
  have hc : Tendsto (fun count : ℕ ↦ C / Real.sqrt (count + 2 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 2))
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hc (eps / 2) (by linarith)
  refine ⟨A, fun count hcount ↦ ?_⟩
  have hs : 0 < Real.sqrt (count + 2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hm := mul_le_mul_of_nonneg_left (suzukiOldPrimeMass_le_twelve_sqrt count)
    (show 0 ≤ eps / 24 by linarith)
  have hsum : (∑ j ∈ Finset.range count, |suzukiFirstTailMassLogWork j|) ≤
      eps / 2 * Real.sqrt (count + 2 : ℕ) + C := by linarith [hbound count]
  have hsmall := hA count hcount
  rw [Real.dist_eq, sub_zero] at hsmall ⊢
  rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) hs.le)]
  calc
    _ ≤ (eps / 2 * Real.sqrt (count + 2 : ℕ) + C) / Real.sqrt (count + 2 : ℕ) :=
      div_le_div_of_nonneg_right hsum hs.le
    _ = eps / 2 + C / Real.sqrt (count + 2 : ℕ) := by field_simp
    _ < eps := by have := le_abs_self (C / Real.sqrt (count + 2 : ℕ)); linarith

/-- The summable Lerch correction transfers the new sub-square-root estimate to the complete absolute work of the original canonical-center chain. -/
theorem suzukiSignedWork_absolute_sum_div_sqrt_tendsto_zero :
    Tendsto (fun count : ℕ ↦ (∑ j ∈ Finset.range count, |suzukiFirstTailTransportLinearWork j|) /
      Real.sqrt (count + 2 : ℕ)) atTop (𝓝 0) := by
  have he := summable_suzukiFirstTailMassLogWorkError.hasSum.tendsto_sum_nat.div_atTop
    (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 2))
  have hmajor := suzukiMassLogWork_absolute_sum_div_sqrt_tendsto_zero.add he
  norm_num only [Function.comp_def, add_zero] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun _ ↦ div_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (Real.sqrt_nonneg _)
  · exact Eventually.of_forall fun count ↦ by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      rw [suzukiFirstTailTransportLinearWork_eq_massLog_add_error]
      simpa only [abs_of_nonneg (suzukiFirstTailMassLogWorkError_bounds j).1] using
        abs_add_le (suzukiFirstTailMassLogWork j) (suzukiFirstTailMassLogWorkError j)

/-- The unchanged cumulative signed work is `o(sqrt N)`. No logarithmic floor or off-critical zero exclusion follows from this weaker rate. -/
theorem suzukiSignedWork_sum_div_sqrt_tendsto_zero :
    Tendsto (fun count : ℕ ↦ (∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) /
      Real.sqrt (count + 2 : ℕ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' ?_ ?_ suzukiSignedWork_absolute_sum_div_sqrt_tendsto_zero
  · exact Eventually.of_forall (fun _ ↦ norm_nonneg _)
  · exact Eventually.of_forall fun count ↦ by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.sqrt_nonneg _)

/-- The original canonical gap is also `o(sqrt N)` after the unchanged summable transport costs are included. -/
theorem suzukiCanonicalGap_div_sqrt_tendsto_zero :
    Tendsto (fun count : ℕ ↦ suzukiFirstTailCanonicalGap count / Real.sqrt (count + 2 : ℕ))
      atTop (𝓝 0) := by
  have hcost := suzukiFirstTailCanonicalGap_sub_linearWork_tendsto.div_atTop
    (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 2))
  have hbase : Tendsto (fun count : ℕ ↦ suzukiFirstTailCanonicalGap 0 / Real.sqrt (count + 2 : ℕ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (endpoint_tendsto_atTop 2))
  have h := (hcost.add hbase).add suzukiSignedWork_sum_div_sqrt_tendsto_zero
  norm_num only [Function.comp_def, add_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun count ↦ by dsimp only; ring

end

end RiemannGaussian
