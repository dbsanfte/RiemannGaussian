import RiemannGaussian.EtaGammaQuadraticGcd

/-!
# The concrete eighth/fifth gamma quadratic

All actual nontrivial zeros retain the original source on the proposed
near-square schedule, with both short copies and the entire omitted
cofactor accounted for. This supplies no independent signed upper bound.
-/

open Complex Filter MeasureTheory Set RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic RiemannGaussian.EtaGammaGcd
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaQuadratic

noncomputable section

/-- The omitted square tends to zero on the explicit eighth/fifth schedule at every actual zero. -/
theorem smoothError_eighth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ smoothError rho ((u : ℝ) ^ 8) (u ^ 5)) atTop (𝓝 0) := by
  have hx : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ 2 / 4) atTop atTop := by
    have hp := (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [div_eq_mul_inv, Function.comp_def] using hp.atTop_mul_const (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)
  have hlim := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).comp hx).mul_const
    (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 12)
  have hb : ∀ᶠ u : ℕ in atTop,
      ‖smoothError rho ((u : ℝ) ^ 8) (u ^ 5)‖ ≤
        ((u : ℝ) ^ 2 / 4) ^ 12 * Real.exp (-((u : ℝ) ^ 2 / 4)) *
          (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 12) := by
    filter_upwards [eventually_ge_atTop 2] with u hu
    have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
    have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
    have hU : 2 * (u : ℝ) ^ 8 ≤ ((u ^ 5 : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith [mul_nonneg (sq_nonneg ((u : ℝ) ^ 4)) (show 0 ≤ (u : ℝ) ^ 2 - 2 by nlinarith)]
    apply (norm_smoothError_le rho (pow_pos huR 8) hU).trans_eq
    have he : -(((u ^ 5 : ℕ) : ℝ) ^ 2) / (4 * (u : ℝ) ^ 8) = -((u : ℝ) ^ 2 / 4) := by
      push_cast
      field_simp
    rw [he]
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hb
    (by simpa only [zero_mul, Function.comp_def] using hlim)

/-- The complete fifth-power short family has a negative exponent at every actual zero. -/
theorem norm_short_eighth_fifth_le (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 5)) ((u : ℝ) ^ 8)‖ ≤
      gammaMoebiusConstant rho * (u : ℝ) ^ (-4 - 5 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  apply (norm_gammaMoebiusSelected_le rho (pow_pos huR 8)
    (S := Finset.Icc 1 (u ^ 5)) (D := u ^ 5) (fun _ h ↦ h)).trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le, ← pow_mul, ← Real.rpow_natCast (u : ℝ) (8 * 3),
    div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub huR]
  congr 2
  norm_num
  ring

/-- Both short copies in the smooth quadratic identity tend to zero on the explicit schedule. -/
theorem short_eighth_fifth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 5)) ((u : ℝ) ^ 8))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (-4 - 5 * rho.1.re)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (show 0 < 4 + 5 * rho.1.re by
      linarith [NontrivialZetaZero.zero_lt_re rho])).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext u
    simp only [Function.comp_def]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun u hu ↦ norm_short_eighth_fifth_le rho hu)
    (by simpa only [mul_zero] using hp.const_mul (gammaMoebiusConstant rho))

/-- The unchanged two-endpoint smoothed source tends to the original source. -/
theorem source_eighth_tendsto_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ gammaMoebiusSource rho ((u : ℝ) ^ 8)) atTop
      (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hinv : Tendsto (fun u : ℕ ↦ (u : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := ((hinv.pow 8).pow 3).const_mul
    (‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / 6)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop (1 : ℕ)).mono fun u hu ↦ norm_gammaMoebiusSource_sub_le rho
      (pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 8))
  simpa only [div_eq_mul_inv, mul_inv, inv_pow, mul_assoc,
    zero_pow (by decide : 8 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero] using hb

/-- The full smooth quadratic retains the original source at every actual nontrivial zero; no independent upper estimate is asserted. -/
theorem smoothQuadratic_eighth_tendsto_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ smoothQuadratic rho ((u : ℝ) ^ 8) (u ^ 5)) atTop
      (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have ht := (((source_eighth_tendsto_source rho).sub (short_eighth_fifth_tendsto_zero rho)).sub
    (short_eighth_fifth_tendsto_zero rho)).sub (smoothError_eighth_tendsto_zero rho)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  have hA : 0 < (u : ℝ) ^ 8 := pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 8
  rw [source_eq_short_add_quadratic_add_error rho hA (u ^ 5)]
  ring

/-- The exact source comparison on the proposed near-square schedule pays both short sums, the full omitted cofactor, and the physical endpoints. -/
theorem norm_smoothQuadratic_eighth_sub_source_le (rho : NontrivialZetaZero)
    {u : ℕ} (hu : 2 ≤ u) :
    ‖smoothQuadratic rho ((u : ℝ) ^ 8) (u ^ 5) - pairedEtaCompletedMoebiusSource rho‖ ≤
      2 * gammaMoebiusConstant rho * (u : ℝ) ^ (-4 - 5 * rho.1.re) +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 24 * Real.exp (-(u : ℝ) ^ 2 / 4) +
          ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) /
            (6 * (u : ℝ) ^ 24) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 1 ≤ u by omega)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hA : 0 < (u : ℝ) ^ 8 := pow_pos huR 8
  have hU : 2 * (u : ℝ) ^ 8 ≤ ((u ^ 5 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [mul_nonneg (pow_nonneg huR.le 8) (show 0 ≤ (u : ℝ) ^ 2 - 2 by nlinarith)]
  have he : smoothQuadratic rho ((u : ℝ) ^ 8) (u ^ 5) - pairedEtaCompletedMoebiusSource rho =
      -(gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 5)) ((u : ℝ) ^ 8) +
        gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 5)) ((u : ℝ) ^ 8) +
          smoothError rho ((u : ℝ) ^ 8) (u ^ 5)) +
            (gammaMoebiusSource rho ((u : ℝ) ^ 8) - pairedEtaCompletedMoebiusSource rho) := by
    rw [source_eq_short_add_quadratic_add_error rho hA]
    ring
  have herr : ‖smoothError rho ((u : ℝ) ^ 8) (u ^ 5)‖ ≤
      1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 24 * Real.exp (-(u : ℝ) ^ 2 / 4) := by
    apply (norm_smoothError_le rho hA hU).trans_eq
    have hx : -(((u ^ 5 : ℕ) : ℝ) ^ 2) / (4 * (u : ℝ) ^ 8) = -(u : ℝ) ^ 2 / 4 := by
      push_cast
      field_simp
    rw [hx, ← pow_mul]
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add _ herr
    have h := norm_short_eighth_fifth_le rho (show 1 ≤ u by omega)
    exact (norm_add_le _ _).trans (by linarith)
  · simpa only [← pow_mul] using norm_gammaMoebiusSource_sub_le rho hA

/-- After the independently controlled large-gcd part is removed, the exact surviving core still tends to the nonzero source. -/
theorem smallGcd_eighth_fifth_tendsto_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ smallGcd rho ((u : ℝ) ^ 8) (u ^ 5) (2 * u ^ 4)) atTop
      (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have ht := (smoothQuadratic_eighth_tendsto_source rho).sub
    (largeGcd_eighth_fifth_tendsto_zero rho hrho)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  rw [smoothQuadratic_eq_small_add_large rho (pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 8)]
  ring

end

end RiemannGaussian.EtaGammaQuadratic
