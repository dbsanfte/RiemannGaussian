import RiemannGaussian.EtaMoebiusDyadicPhase

/-!
# Quantitative dyadic cancellation for the actual completed eta tails

The exact endpoint-normalized terms retain the original complex kernel with
both physical endpoint powers. The leading odd/even divisor interaction
cancels on a full arithmetic period. Explicit product errors then bound
the actual period average, retaining both divisor sizes and the starting
cutoff. These fixed-divisor estimates do not control a growing full matrix.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The interaction of the actual completed terms with their individual
complex odd-endpoint normalizations. -/
def pairedEtaCompletedMoebiusEndpointPair (rho : NontrivialZetaZero) (M d e : ℕ) : ℂ :=
  pairedEtaCompletedMoebiusEndpointPhase rho M d *
    starRingEnd ℂ (pairedEtaCompletedMoebiusEndpointPhase rho M e)

/-- Both literal complex endpoint powers remain attached to the original
pair kernel. This normalized pair does not redefine the original current. -/
theorem pairedEtaCompletedMoebiusEndpointPair_eq_physical_kernel
    (rho : NontrivialZetaZero) (M d e : ℕ) :
    pairedEtaCompletedMoebiusEndpointPair rho M d e =
      (((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 *
        starRingEnd ℂ (((e * pairedEtaUnpairedOddEndpoint (M / e) : ℕ) : ℂ) ^ rho.1)) *
          pairedEtaCompletedMoebiusPairKernel rho M d e := by
  simp only [pairedEtaCompletedMoebiusEndpointPair, pairedEtaCompletedMoebiusEndpointPhase,
    pairedEtaCompletedMoebiusPairKernel, map_mul]
  ring

/-- The actual pair error preserves both complex positions before taking
norms, using the existing product identity on the literal completed terms. -/
theorem pairedEtaCompletedMoebiusEndpointPair_sub_parity
    (rho : NontrivialZetaZero) (M d e : ℕ) :
    pairedEtaCompletedMoebiusEndpointPair rho M d e - pairedEtaCompletedMoebiusParityPair rho M d e =
      (pairedEtaCompletedMoebiusEndpointPhase rho M d - pairedEtaCompletedMoebiusParityPhase rho M d) *
          starRingEnd ℂ (pairedEtaCompletedMoebiusEndpointPhase rho M e) +
        pairedEtaCompletedMoebiusParityPhase rho M d *
          starRingEnd ℂ (pairedEtaCompletedMoebiusEndpointPhase rho M e -
            pairedEtaCompletedMoebiusParityPhase rho M e) :=
  etaCurrent_product_sub_euler _ _ _ _

/-- The explicit pair-error bound retains both divisor sizes and the
physical starting cutoff, including the product of the two errors. -/
def pairedEtaCompletedMoebiusPairPhaseError (rho : NontrivialZetaZero) (d e A : ℕ) : ℝ :=
  pairedEtaCompletedMoebiusPhaseErrorConstant rho * ‖pairedEtaXiCompletionFactor rho.1‖ *
      ((d : ℝ) + e) / A +
    4 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * d * e / (A : ℝ) ^ 2

/-- Every term of the explicit pair-error expression is nonnegative. -/
theorem pairedEtaCompletedMoebiusPairPhaseError_nonneg (rho : NontrivialZetaZero) (d e A : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusPairPhaseError rho d e A := by
  have h := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusPairPhaseError
  positivity

/-- The actual endpoint phase remains within its explicit completion
amplitude plus the genuine inverse-cutoff error. -/
theorem norm_pairedEtaCompletedMoebiusEndpointPhase_le
    (rho : NontrivialZetaZero) {M d : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) :
    ‖pairedEtaCompletedMoebiusEndpointPhase rho M d‖ ≤
      2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * d / M +
        ‖pairedEtaXiCompletionFactor rho.1‖ / 2 := by
  have h : ‖pairedEtaCompletedMoebiusEndpointPhase rho M d‖ ≤
      ‖pairedEtaCompletedMoebiusEndpointPhase rho M d - pairedEtaCompletedMoebiusParityPhase rho M d‖ +
        ‖pairedEtaCompletedMoebiusParityPhase rho M d‖ := by
    simpa only [add_comm] using norm_le_insert'
      (pairedEtaCompletedMoebiusEndpointPhase rho M d) (pairedEtaCompletedMoebiusParityPhase rho M d)
  exact h.trans (add_le_add
    (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM hd)
    (norm_pairedEtaCompletedMoebiusParityPhase_le rho M d))

/-- The exact completed pair differs from its leading arithmetic phase
by the explicit product-error estimate at every positive cutoff. -/
theorem norm_pairedEtaCompletedMoebiusEndpointPair_sub_parity_le
    (rho : NontrivialZetaZero) {M d e : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ‖pairedEtaCompletedMoebiusEndpointPair rho M d e - pairedEtaCompletedMoebiusParityPair rho M d e‖ ≤
      pairedEtaCompletedMoebiusPairPhaseError rho d e M := by
  have hH := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  apply (norm_etaCurrent_product_sub_euler_le _ _ _ _).trans
  calc
    _ ≤ (2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * d / M) *
          (2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * e / M +
            ‖pairedEtaXiCompletionFactor rho.1‖ / 2) +
        (‖pairedEtaXiCompletionFactor rho.1‖ / 2) *
          (2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * e / M) :=
      add_le_add
        (mul_le_mul (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM hd)
          (norm_pairedEtaCompletedMoebiusEndpointPhase_le rho hM he) (norm_nonneg _) (by positivity))
        (mul_le_mul (norm_pairedEtaCompletedMoebiusParityPhase_le rho M d)
          (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM he)
          (norm_nonneg _) (by positivity))
    _ = _ := by unfold pairedEtaCompletedMoebiusPairPhaseError; ring

/-- Increasing the starting cutoff decreases the explicit pair-error
bound while keeping both divisor sizes fixed. -/
theorem pairedEtaCompletedMoebiusPairPhaseError_antitone
    (rho : NontrivialZetaZero) (d e : ℕ) {A M : ℕ} (hA : 1 ≤ A) (hAM : A ≤ M) :
    pairedEtaCompletedMoebiusPairPhaseError rho d e M ≤ pairedEtaCompletedMoebiusPairPhaseError rho d e A := by
  have hH := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hAMR : (A : ℝ) ≤ M := by exact_mod_cast hAM
  unfold pairedEtaCompletedMoebiusPairPhaseError
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hAR hAMR
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hAR.le hAMR 2)

/-- The average of the actual complex endpoint pairs over one complete
arithmetic period, at its literal starting cutoff. -/
def pairedEtaCompletedMoebiusDyadicCorrelation (rho : NontrivialZetaZero) (A d k : ℕ) : ℂ :=
  (∑ r ∈ Finset.range (4 * d * k), pairedEtaCompletedMoebiusEndpointPair rho (A + r) d (2 * k)) /
    ((4 * d * k : ℕ) : ℂ)

/-- The actual completed odd/even divisor correlation has an explicit
inverse-cutoff bound. The arithmetic cancellation is proved before the
norm estimate, and neither divisor dependence nor the quadratic error is lost. -/
theorem norm_pairedEtaCompletedMoebiusDyadicCorrelation_le
    (rho : NontrivialZetaZero) {A d k : ℕ} (hA : 1 ≤ A) (hd : Odd d) (hk : 1 ≤ k) :
    ‖pairedEtaCompletedMoebiusDyadicCorrelation rho A d k‖ ≤
      pairedEtaCompletedMoebiusPairPhaseError rho d (2 * k) A := by
  have hdp : 1 ≤ d := by obtain ⟨n, rfl⟩ := hd; omega
  have hkp : 1 ≤ 2 * k := by omega
  have hP : (0 : ℝ) < (4 * d * k : ℕ) := by exact_mod_cast (show 0 < 4 * d * k by positivity)
  have hsum : ‖∑ r ∈ Finset.range (4 * d * k), pairedEtaCompletedMoebiusEndpointPair rho (A + r) d (2 * k)‖ ≤
      ((4 * d * k : ℕ) : ℝ) * pairedEtaCompletedMoebiusPairPhaseError rho d (2 * k) A := by
    rw [← sub_zero (∑ r ∈ Finset.range (4 * d * k), pairedEtaCompletedMoebiusEndpointPair rho (A + r) d (2 * k)),
      ← sum_pairedEtaCompletedMoebiusParityPair_period_eq_zero rho A hd hk, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _r ∈ Finset.range (4 * d * k), pairedEtaCompletedMoebiusPairPhaseError rho d (2 * k) A := by
        apply Finset.sum_le_sum
        intro r hr
        exact (norm_pairedEtaCompletedMoebiusEndpointPair_sub_parity_le rho (by omega) hdp hkp).trans
          (pairedEtaCompletedMoebiusPairPhaseError_antitone rho d (2 * k) hA (by omega))
      _ = _ := by simp
  rw [pairedEtaCompletedMoebiusDyadicCorrelation, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hP).2 (by simpa only [mul_comm] using hsum)

/-- For fixed divisors the proved error tends to zero, with both its
inverse-cutoff and inverse-square-cutoff terms retained. -/
theorem pairedEtaCompletedMoebiusPairPhaseError_tendsto_zero
    (rho : NontrivialZetaZero) (d e : ℕ) :
    Tendsto (pairedEtaCompletedMoebiusPairPhaseError rho d e) atTop (𝓝 0) := by
  have hi : Tendsto (fun A : ℕ ↦ (A : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 := hi.const_mul (pairedEtaCompletedMoebiusPhaseErrorConstant rho *
    ‖pairedEtaXiCompletionFactor rho.1‖ * ((d : ℝ) + e))
  have h2 := (hi.pow 2).const_mul (4 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * d * e)
  unfold pairedEtaCompletedMoebiusPairPhaseError
  simpa only [div_eq_mul_inv, inv_pow,
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h1.add h2

/-- The actual endpoint-normalized odd/even divisor correlation vanishes
after a full-period average, at every actual zero and for every fixed pair. -/
theorem pairedEtaCompletedMoebiusDyadicCorrelation_tendsto_zero
    (rho : NontrivialZetaZero) {d k : ℕ} (hd : Odd d) (hk : 1 ≤ k) :
    Tendsto (fun A ↦ pairedEtaCompletedMoebiusDyadicCorrelation rho A d k) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun _ hA ↦ norm_pairedEtaCompletedMoebiusDyadicCorrelation_le rho hA hd hk)
    (pairedEtaCompletedMoebiusPairPhaseError_tendsto_zero rho d (2 * k))

/-- The same full-period average for the repository's original signed
completed-pair orientation, with both reflected zero channels retained. -/
def pairedEtaSignedCompletedMoebiusDyadicCorrelation (rho : NontrivialZetaZero) (A d k : ℕ) : ℂ :=
  (∑ r ∈ Finset.range (4 * d * k), etaSignedCompletedPair
    (pairedEtaCompletedMoebiusEndpointPhase (NontrivialZetaZero.conjugatePartner rho) (A + r) d)
    (pairedEtaCompletedMoebiusEndpointPhase (NontrivialZetaZero.conjugatePartner rho) (A + r) (2 * k))
    (pairedEtaCompletedMoebiusEndpointPhase rho (A + r) d)
    (pairedEtaCompletedMoebiusEndpointPhase rho (A + r) (2 * k))) / ((4 * d * k : ℕ) : ℂ)

/-- The complete signed average is the partner correlation minus the
conjugate original correlation, with the exact finite normalization. -/
theorem pairedEtaSignedCompletedMoebiusDyadicCorrelation_eq_channels
    (rho : NontrivialZetaZero) (A d k : ℕ) :
    pairedEtaSignedCompletedMoebiusDyadicCorrelation rho A d k =
      pairedEtaCompletedMoebiusDyadicCorrelation (NontrivialZetaZero.conjugatePartner rho) A d k -
        starRingEnd ℂ (pairedEtaCompletedMoebiusDyadicCorrelation rho A d k) := by
  simp only [pairedEtaSignedCompletedMoebiusDyadicCorrelation, pairedEtaCompletedMoebiusDyadicCorrelation,
    pairedEtaCompletedMoebiusEndpointPair, etaSignedCompletedPair, Finset.sum_sub_distrib,
    map_div₀, map_sum, map_mul, map_natCast, starRingEnd_apply, star_star, sub_div]

/-- Both original completion channels satisfy a quantitative arithmetic
cancellation estimate, with each explicit divisor-dependent error included. -/
theorem norm_pairedEtaSignedCompletedMoebiusDyadicCorrelation_le
    (rho : NontrivialZetaZero) {A d k : ℕ} (hA : 1 ≤ A) (hd : Odd d) (hk : 1 ≤ k) :
    ‖pairedEtaSignedCompletedMoebiusDyadicCorrelation rho A d k‖ ≤
      pairedEtaCompletedMoebiusPairPhaseError (NontrivialZetaZero.conjugatePartner rho) d (2 * k) A +
        pairedEtaCompletedMoebiusPairPhaseError rho d (2 * k) A := by
  rw [pairedEtaSignedCompletedMoebiusDyadicCorrelation_eq_channels]
  apply (norm_sub_le _ _).trans
  rw [norm_conj]
  exact add_le_add
    (norm_pairedEtaCompletedMoebiusDyadicCorrelation_le (NontrivialZetaZero.conjugatePartner rho) hA hd hk)
    (norm_pairedEtaCompletedMoebiusDyadicCorrelation_le rho hA hd hk)

/-- The full signed completed correlation vanishes in this fixed-divisor
period average. No critical-line or multiplicity-one hypothesis is used. -/
theorem pairedEtaSignedCompletedMoebiusDyadicCorrelation_tendsto_zero
    (rho : NontrivialZetaZero) {d k : ℕ} (hd : Odd d) (hk : 1 ≤ k) :
    Tendsto (fun A ↦ pairedEtaSignedCompletedMoebiusDyadicCorrelation rho A d k) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hlim := (pairedEtaCompletedMoebiusPairPhaseError_tendsto_zero
    (NontrivialZetaZero.conjugatePartner rho) d (2 * k)).add
      (pairedEtaCompletedMoebiusPairPhaseError_tendsto_zero rho d (2 * k))
  simp only [add_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun _ hA ↦ norm_pairedEtaSignedCompletedMoebiusDyadicCorrelation_le rho hA hd hk)
    hlim

end

end RiemannGaussian
