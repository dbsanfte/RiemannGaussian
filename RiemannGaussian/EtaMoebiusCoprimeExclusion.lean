import RiemannGaussian.EtaMoebiusCoprimeGrowth

/-!
# Removing a growing set of product rows and all their mixed terms

The actual high product prefix is restricted to products coprime to the
growing odd modulus. The removed complex family has vanishing mean square
on the explicit original cubic scales, and its entire mixed correlation
with the original family vanishes. The surviving energy keeps every
remaining product pair and still converges to the original source square.
An independent bound below that source is not supplied by this exclusion.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The complex family removed by coprimality is exactly the literal prefix of excluded products. -/
theorem pairedEtaCompletedMoebiusLarge_sub_coprime_eq_excluded
    (rho : NontrivialZetaZero) (P D M : ℕ) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D -
      pairedEtaCompletedMoebiusCoprimeAggregate rho P D M =
        pairedEtaXiCompletionFactor rho.1 *
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ ¬n.Coprime P),
            (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) := by
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix, pairedEtaCompletedMoebiusCoprimeAggregate]
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n ↦ n.Coprime P)
    (fun n ↦ (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1))
  rw [← hs]
  ring

/-- The whole removed family is the difference of the exact sieved and unsieved low divisor families, with their complex phases retained. -/
theorem pairedEtaCompletedMoebiusLarge_sub_coprime_eq_low_sub
    (rho : NontrivialZetaZero) {P : ℕ} (hodd : Odd P)
    {D M : ℕ} (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D -
      pairedEtaCompletedMoebiusCoprimeAggregate rho P D M =
        pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M -
          pairedEtaCompletedMoebiusPartialAggregate rho M D := by
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub rho hM hDM]
  have hs := pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd hM hDM
  rw [← hs]
  ring

/-- The mean square of the entire excluded complex product family on the unchanged cubic window. -/
def pairedEtaMoebiusCoprimeRemovedCubicEnergy (rho : NontrivialZetaZero) (P u : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (u ^ 3),
    ‖pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2) -
      pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2) / (u ^ 3 : ℕ)

/-- The full complex correlation between the original family and all simultaneously excluded products. -/
def pairedEtaMoebiusCoprimeMixedCubicCorrelation (rho : NontrivialZetaZero) (P u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 3),
    pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2) *
      starRingEnd ℂ (pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2) -
        pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 2) (u ^ 3 + t))) / (u ^ 3 : ℕ)

/-- The energy after simultaneous exclusion retains every ordered pair of surviving products. -/
def pairedEtaMoebiusCoprimeCubicEnergy (rho : NontrivialZetaZero) (P u : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (u ^ 3),
    ‖pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2) / (u ^ 3 : ℕ)

/-- Both whole low families control the removed mean square, including all intersections of prime-divisible products. -/
theorem pairedEtaMoebiusCoprimeRemovedCubicEnergy_le_low
    (rho : NontrivialZetaZero) {P u : ℕ} (hodd : Odd P) (hu : 2 ≤ u) :
    pairedEtaMoebiusCoprimeRemovedCubicEnergy rho P u ≤
      2 * pairedEtaMoebiusCoprimeLowCubicEnergy rho P u +
        2 * pairedEtaCompletedMoebiusOriginalMeanSquare rho (u ^ 3) (u ^ 3) (u ^ 2) := by
  have hu1 : 1 ≤ u := by omega
  have h23 : u ^ 2 ≤ u ^ 3 := by nlinarith [Nat.mul_le_mul_left (u ^ 2) hu1]
  have hM2 : 2 ≤ u ^ 3 := hu.trans (Nat.le_self_pow (by decide : 3 ≠ 0) u)
  have hpoint (t : ℕ) :
      ‖pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2) -
        pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2 ≤
          2 * ‖pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 2) (u ^ 3 + t)‖ ^ 2 +
            2 * ‖pairedEtaCompletedMoebiusPartialAggregate rho (u ^ 3 + t) (u ^ 2)‖ ^ 2 := by
    rw [pairedEtaCompletedMoebiusLarge_sub_coprime_eq_low_sub rho hodd
      (hM2.trans (Nat.le_add_right _ _)) (h23.trans (Nat.le_add_right _ _))]
    have hn := norm_sub_le (pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 2) (u ^ 3 + t))
      (pairedEtaCompletedMoebiusPartialAggregate rho (u ^ 3 + t) (u ^ 2))
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [sq_nonneg (‖pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (u ^ 2) (u ^ 3 + t)‖ -
      ‖pairedEtaCompletedMoebiusPartialAggregate rho (u ^ 3 + t) (u ^ 2)‖)]
  unfold pairedEtaMoebiusCoprimeRemovedCubicEnergy pairedEtaMoebiusCoprimeLowCubicEnergy
    pairedEtaCompletedMoebiusOriginalMeanSquare
  have hh := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.range (u ^ 3)) (fun t _ ↦ hpoint t))
    (Nat.cast_nonneg (u ^ 3) : (0 : ℝ) ≤ (u ^ 3 : ℕ))
  apply hh.trans_eq
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, add_div, mul_div_assoc, mul_div_assoc]

/-- The mean square of all products removed by the explicit growing odd sieve tends to zero. -/
theorem pairedEtaMoebiusCoprimeRemovedCubicEnergy_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeRemovedCubicEnergy rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop (𝓝 0) := by
  have hs := pairedEtaMoebiusCoprimeLowCubicEnergy_growing_tendsto_zero rho hrho
  have hl := (pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_tendsto_zero rho hrho).comp
    (pairedEtaCoprimeScale_tendsto_atTop rho)
  have hb := (hs.const_mul 2).add (hl.const_mul 2)
  simp only [mul_zero, add_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun v ↦ by
    unfold pairedEtaMoebiusCoprimeRemovedCubicEnergy; positivity))
    (((pairedEtaCoprimeScale_tendsto_atTop rho).eventually (eventually_ge_atTop 2)).mono fun v hv ↦
      pairedEtaMoebiusCoprimeRemovedCubicEnergy_le_low rho (pairedEtaOddSieveModulus_odd v) hv)
  convert hb using 1
  ext v
  rfl

private theorem norm_mean_mixed_sq_le (L : ℕ) (f g : ℕ → ℂ) :
    ‖(∑ t ∈ Finset.range L, f t * starRingEnd ℂ (g t)) / (L : ℂ)‖ ^ 2 ≤
      ((∑ t ∈ Finset.range L, ‖f t‖ ^ 2) / (L : ℝ)) *
        ((∑ t ∈ Finset.range L, ‖g t‖ ^ 2) / (L : ℝ)) := by
  have hn := norm_sum_le (Finset.range L) (fun t ↦ f t * starRingEnd ℂ (g t))
  simp only [norm_mul, norm_conj] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun t ↦ ‖f t‖) (fun t ↦ ‖g t‖)
  rw [norm_div, Complex.norm_natCast, div_pow]
  apply (div_le_div_of_nonneg_right (hs.trans hc) (sq_nonneg (L : ℝ))).trans_eq
  ring

/-- All mixed interactions with the original family are controlled together on the same physical window. -/
theorem norm_pairedEtaMoebiusCoprimeMixedCubicCorrelation_sq_le
    (rho : NontrivialZetaZero) (P u : ℕ) :
    ‖pairedEtaMoebiusCoprimeMixedCubicCorrelation rho P u‖ ^ 2 ≤
      pairedEtaCompletedMoebiusLargeMeanSquare rho (u ^ 3) (u ^ 3) (u ^ 2) *
        pairedEtaMoebiusCoprimeRemovedCubicEnergy rho P u :=
  norm_mean_mixed_sq_le (u ^ 3)
    (fun t ↦ pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2))
    (fun t ↦ pairedEtaCompletedMoebiusLargeAggregate rho (u ^ 3 + t) (u ^ 2) -
      pairedEtaCompletedMoebiusCoprimeAggregate rho P (u ^ 2) (u ^ 3 + t))

/-- The exact energy identity retains the entire complex interference of the removed family with the original high aggregate. -/
theorem pairedEtaMoebiusCoprimeCubicEnergy_eq_mixed
    (rho : NontrivialZetaZero) (P u : ℕ) :
    pairedEtaMoebiusCoprimeCubicEnergy rho P u =
      pairedEtaCompletedMoebiusLargeMeanSquare rho (u ^ 3) (u ^ 3) (u ^ 2) +
        pairedEtaMoebiusCoprimeRemovedCubicEnergy rho P u -
          2 * (pairedEtaMoebiusCoprimeMixedCubicCorrelation rho P u).re := by
  have hpoint (M D : ℕ) :
      ‖pairedEtaCompletedMoebiusCoprimeAggregate rho P D M‖ ^ 2 =
        ‖pairedEtaCompletedMoebiusLargeAggregate rho M D‖ ^ 2 +
          ‖pairedEtaCompletedMoebiusLargeAggregate rho M D - pairedEtaCompletedMoebiusCoprimeAggregate rho P D M‖ ^ 2 -
            2 * (pairedEtaCompletedMoebiusLargeAggregate rho M D *
              starRingEnd ℂ (pairedEtaCompletedMoebiusLargeAggregate rho M D -
                pairedEtaCompletedMoebiusCoprimeAggregate rho P D M)).re := by
    have he : pairedEtaCompletedMoebiusCoprimeAggregate rho P D M =
        pairedEtaCompletedMoebiusLargeAggregate rho M D -
          (pairedEtaCompletedMoebiusLargeAggregate rho M D - pairedEtaCompletedMoebiusCoprimeAggregate rho P D M) := by ring
    conv_lhs => rw [he]
    rw [Complex.sq_norm, Complex.normSq_sub]
    simp only [← Complex.sq_norm]
  simp only [pairedEtaMoebiusCoprimeCubicEnergy, hpoint,
    pairedEtaCompletedMoebiusLargeMeanSquare, pairedEtaMoebiusCoprimeRemovedCubicEnergy,
    pairedEtaMoebiusCoprimeMixedCubicCorrelation, Complex.div_natCast_re,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    add_div, sub_div, mul_div_assoc]
  rw [Complex.re_sum]

/-- The whole mixed correlation vanishes with the growing excluded family, including every interaction between that family and its complement. -/
theorem pairedEtaMoebiusCoprimeMixedCubicCorrelation_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeMixedCubicCorrelation rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop (𝓝 0) := by
  have hr := pairedEtaMoebiusCoprimeRemovedCubicEnergy_growing_tendsto_zero rho hrho
  have hh := (pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho).comp
    (pairedEtaCoprimeScale_tendsto_atTop rho)
  have hz : Tendsto (fun v ↦ ‖pairedEtaMoebiusCoprimeMixedCubicCorrelation rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ sq_nonneg _)
      (fun v ↦ norm_pairedEtaMoebiusCoprimeMixedCubicCorrelation_sq_le rho _ _)
    have hb := hh.mul hr
    simp only [mul_zero] at hb
    convert hb using 1
    ext v
    rfl
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hz.sqrt

/-- Deleting the rows and columns divisible by an increasing set of odd primes changes the original signed whole energy by a vanishing amount. -/
theorem pairedEtaMoebiusLargeMeanSquare_sub_growingCoprime_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho
      (pairedEtaCoprimeScale rho v ^ 3) (pairedEtaCoprimeScale rho v ^ 3) (pairedEtaCoprimeScale rho v ^ 2) -
        pairedEtaMoebiusCoprimeCubicEnergy rho (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v))
          atTop (𝓝 0) := by
  have hr := pairedEtaMoebiusCoprimeRemovedCubicEnergy_growing_tendsto_zero rho hrho
  have hm : Tendsto (fun v ↦ (pairedEtaMoebiusCoprimeMixedCubicCorrelation rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)).re) atTop (𝓝 0) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (pairedEtaMoebiusCoprimeMixedCubicCorrelation_growing_tendsto_zero rho hrho) using 1
    · ext v
      rfl
    · rfl
  have hz := (hm.const_mul 2).sub hr
  simp only [mul_zero, sub_zero] at hz
  convert hz using 1
  ext v
  rw [pairedEtaMoebiusCoprimeCubicEnergy_eq_mixed]
  ring

/-- The exact complement after growing simultaneous odd-prime exclusion still carries the nonzero source square; its independent sub-source upper bound remains the open arithmetic step. -/
theorem pairedEtaMoebiusCoprimeCubicEnergy_growing_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeCubicEnergy rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v)) atTop
        (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hh := (pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho).comp
    (pairedEtaCoprimeScale_tendsto_atTop rho)
  have hd := pairedEtaMoebiusLargeMeanSquare_sub_growingCoprime_tendsto_zero rho hrho
  have hz := hh.sub hd
  simp only [sub_zero] at hz
  convert hz using 1
  ext v
  simp only [Function.comp_apply]
  ring

end

end RiemannGaussian
