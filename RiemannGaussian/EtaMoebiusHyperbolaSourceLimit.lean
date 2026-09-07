import RiemannGaussian.EtaMoebiusHyperbolaLargeMeanSquare

/-!
# The source carried by the large-divisor half

The exact source split retains its signed cross term after averaging.
The proved small-half decay therefore makes the large-half mean square
converge to the strictly positive source square when `Re rho > 1/4`.
At a hypothetical right-half zero a separate vanishing operator estimate
would contradict this result. That new arithmetic estimate is not proved
here; quotient reindexing alone does not supply it.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The actual complex mean of the original small-divisor aggregate, before discarding its phase. -/
def pairedEtaCompletedMoebiusSmallAverage (rho : NontrivialZetaZero) (A L D : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L, pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D) / L

/-- The complex mean is bounded by the mean square on the same physical window, with both normalizations accounted for. -/
theorem pairedEtaCompletedMoebiusSmallAverage_norm_sq_le
    (rho : NontrivialZetaZero) (A D : ℕ) {L : ℕ} (hL : 0 < L) :
    ‖pairedEtaCompletedMoebiusSmallAverage rho A L D‖ ^ 2 ≤
      pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun _ : ℕ ↦ (1 : ℝ))
    (fun n ↦ ‖pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (norm_sum_le (Finset.range L) (fun n ↦ pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D)) 2
  rw [pairedEtaCompletedMoebiusSmallAverage, norm_div, Complex.norm_natCast, div_pow,
    pairedEtaCompletedMoebiusOriginalMeanSquare]
  apply (div_le_iff₀ (sq_pos_of_pos hLR)).mpr
  calc
    _ ≤ (L : ℝ) * ∑ n ∈ Finset.range L,
        ‖pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D‖ ^ 2 := hn.trans hc
    _ = _ := by field_simp

/-- Averaging the exact source split retains the full signed source/small-half cross term. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_source_expansion
    (rho : NontrivialZetaZero) {A L D : ℕ} (hA : 2 ≤ A) (hL : 0 < L) (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusLargeMeanSquare rho A L D =
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 +
        pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D -
        2 * (pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)).re := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have havg : (pairedEtaCompletedMoebiusSource rho *
      starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)).re =
        (∑ n ∈ Finset.range L, (pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D)).re) / L := by
    unfold pairedEtaCompletedMoebiusSmallAverage
    rw [map_div₀, map_sum, map_natCast, ← mul_div_assoc, Complex.div_natCast_re, Finset.mul_sum]
    congr 1
    exact map_sum Complex.reAddGroupHom _ _
  have hpoint (n : ℕ) : ‖pairedEtaCompletedMoebiusLargeAggregate rho (A + n) D‖ ^ 2 =
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 +
        ‖pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D‖ ^ 2 -
        2 * (pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D)).re := by
    rw [pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub rho (by omega) (by omega)]
    simp only [Complex.sq_norm, Complex.normSq_sub]
  rw [pairedEtaCompletedMoebiusLargeMeanSquare, havg, pairedEtaCompletedMoebiusOriginalMeanSquare]
  simp only [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- The actual large-half energy differs from the source square by at most its small-half mean square plus the explicitly controlled signed cross term. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_source_error_le
    (rho : NontrivialZetaZero) {A L D : ℕ} (hA : 2 ≤ A) (hL : 0 < L) (hDA : D ≤ A) :
    |pairedEtaCompletedMoebiusLargeMeanSquare rho A L D - ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2| ≤
      pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D +
        2 * ‖pairedEtaCompletedMoebiusSource rho‖ *
          Real.sqrt (pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D) := by
  have ha : ‖pairedEtaCompletedMoebiusSmallAverage rho A L D‖ ≤
      Real.sqrt (pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D) :=
    Real.le_sqrt_of_sq_le (pairedEtaCompletedMoebiusSmallAverage_norm_sq_le rho A D hL)
  have hc : |(pairedEtaCompletedMoebiusSource rho *
      starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)).re| ≤
        ‖pairedEtaCompletedMoebiusSource rho‖ *
          Real.sqrt (pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D) := by
    calc
      _ ≤ ‖pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)‖ := Complex.abs_re_le_norm _
      _ = ‖pairedEtaCompletedMoebiusSource rho‖ * ‖pairedEtaCompletedMoebiusSmallAverage rho A L D‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
  calc
    _ = |pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D -
        2 * (pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)).re| := by
      rw [pairedEtaCompletedMoebiusLargeMeanSquare_eq_source_expansion rho hA hL hDA]
      congr 1
      ring
    _ ≤ |pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D| +
        |2 * (pairedEtaCompletedMoebiusSource rho *
          starRingEnd ℂ (pairedEtaCompletedMoebiusSmallAverage rho A L D)).re| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (pairedEtaCompletedMoebiusOriginalMeanSquare_nonneg rho A L D), abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith

/-- On square windows the source concentration has the explicit rate supplied by the existing Fourier bound, with its square-root cross-term cost retained. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_square_source_error_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 2 ≤ D) :
    let U := pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * (1 + Real.log D) *
      (D : ℝ) ^ (1 - 4 * rho.1.re)
    |pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 2) (D ^ 2) D -
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2| ≤ U + 2 * ‖pairedEtaCompletedMoebiusSource rho‖ * Real.sqrt U := by
  dsimp only
  apply (pairedEtaCompletedMoebiusLargeMeanSquare_source_error_le rho (by nlinarith : 2 ≤ D ^ 2)
    (by positivity : 0 < D ^ 2) (Nat.le_self_pow (by decide : 2 ≠ 0) D)).trans
  have hu := pairedEtaCompletedMoebiusOriginalMeanSquare_square_le rho (by omega : 1 ≤ D)
  exact add_le_add hu (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu) (by positivity))

/-- The original small half tends to zero even as a complex average; its phase is retained until this downstream limit. -/
theorem pairedEtaCompletedMoebiusSmallAverage_square_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 4 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusSmallAverage rho (D ^ 2) (D ^ 2) D)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun D : ℕ ↦ ‖pairedEtaCompletedMoebiusSmallAverage rho (D ^ 2) (D ^ 2) D‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ sq_nonneg _))
      ((eventually_ge_atTop 1).mono fun D hD ↦
        pairedEtaCompletedMoebiusSmallAverage_norm_sq_le rho (D ^ 2) D (pow_pos hD 2))
      (pairedEtaCompletedMoebiusOriginalMeanSquare_square_tendsto_zero rho hrho)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

/-- The large half carries the positive source square in the limit whenever the real part exceeds one quarter; this is an exact consequence of the proved small-half decay. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_square_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 4 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 2) (D ^ 2) D)
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hl := pairedEtaCompletedMoebiusOriginalMeanSquare_square_tendsto_zero rho hrho
  have ha := pairedEtaCompletedMoebiusSmallAverage_square_tendsto_zero rho hrho
  have hc : Tendsto (fun D : ℕ ↦
      (pairedEtaCompletedMoebiusSource rho * starRingEnd ℂ
        (pairedEtaCompletedMoebiusSmallAverage rho (D ^ 2) (D ^ 2) D)).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero, mul_zero, Complex.zero_re] using
      (Complex.continuous_re.tendsto _).comp
        (((Complex.continuous_conj.tendsto _).comp ha).const_mul (pairedEtaCompletedMoebiusSource rho))
  have hz := ((tendsto_const_nhds (x := ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)).add hl).sub
    (hc.const_mul 2)
  simp only [add_zero, mul_zero, sub_zero] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 2] with D hD
  exact (pairedEtaCompletedMoebiusLargeMeanSquare_eq_source_expansion rho
    (by nlinarith : 2 ≤ D ^ 2) (by positivity : 0 < D ^ 2)
    (Nat.le_self_pow (by decide : 2 ≠ 0) D)).symm

/-- The same nonzero source limit holds on the precise dyadic schedule proposed for the hyperbola reductio. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_hyperbola_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 4 < rho.1.re) :
    Tendsto (fun k ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho
      (pairedEtaMoebiusHyperbolaScale k) (pairedEtaMoebiusHyperbolaScale k)
      (pairedEtaMoebiusHyperbolaCutoff k)) atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) :=
  (pairedEtaCompletedMoebiusLargeMeanSquare_square_tendsto_source rho hrho).comp
    pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop

/-- A fixed positive amount of large-half mean square survives eventually at any hypothetical right-half zero, identifying exactly what a separate decay estimate must contradict. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_hyperbola_pos_eventually
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    ∀ᶠ k : ℕ in atTop, ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 / 2 <
      pairedEtaCompletedMoebiusLargeMeanSquare rho
        (pairedEtaMoebiusHyperbolaScale k) (pairedEtaMoebiusHyperbolaScale k)
        (pairedEtaMoebiusHyperbolaCutoff k) := by
  have hp : 0 < ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (pairedEtaCompletedMoebiusSource_ne_zero rho)) 2
  exact (pairedEtaCompletedMoebiusLargeMeanSquare_hyperbola_tendsto_source rho (by linarith)).eventually
    (lt_mem_nhds (by linarith : ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 / 2 <
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2))

end

end RiemannGaussian
