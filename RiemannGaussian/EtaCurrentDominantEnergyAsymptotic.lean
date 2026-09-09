import RiemannGaussian.EtaCurrentRecessiveEnergy

/-!
# The literal Euler endpoint of the dominant reflected energy

The actual zeroth channel differs by an absolutely summable series from
its explicit completed Euler energy at the physical endpoint `2*N+5`.
For a zero left of one half, summing that energy exposes a strictly
positive leading power. Reflection transports it to the signed current
of a right-half zero, retaining actual multiplicity and completion.
These are conditional asymptotics at actual zeros, not zero exclusions.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate Interval

namespace RiemannGaussian

noncomputable section

/-- The literal positive Euler energy at the successor physical endpoint. -/
def pairedEtaCurrentEulerChannelEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaCurrentZeroEnergyCoefficient rho).re *
    (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * (2 * N + 5 : ℝ) ^ (-2 * rho.1.re)

/-- At order zero the zero coordinate cancels algebraically, while the
completion factor and full complex endpoint phase are retained. -/
theorem pairedEtaCurrentEulerMoment_zero (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentEulerMoment rho N 0 =
      -(pairedEtaXiCompletionFactor rho.1 / 2) *
        Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ)) := by
  unfold pairedEtaCurrentEulerMoment pairedEtaCurrentEulerMomentValue
  simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, one_mul]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- The squared Euler moment is exactly the completed horizontal power;
the common ordinate phase cancels in the genuine Hermitian product. -/
theorem norm_pairedEtaCurrentEulerMoment_zero_sq (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCurrentEulerMoment rho N 0‖ ^ 2 =
      (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * (2 * N + 5 : ℝ) ^ (-2 * rho.1.re) := by
  rw [pairedEtaCurrentEulerMoment_zero, norm_mul, norm_neg, norm_div, norm_ofNat, mul_pow,
    Complex.norm_exp]
  simp only [pow_two]
  rw [← Real.exp_add]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  have hx : (0 : ℝ) < 2 * N + 5 := by positivity
  rw [Real.rpow_def_of_pos hx]
  have hL : pairedEtaLogTailCutoff (N + 2) = Real.log (2 * N + 5 : ℝ) := by
    unfold pairedEtaLogTailCutoff
    push_cast
    congr 1
    ring
  rw [hL]
  congr 1
  · ring
  · congr 1
    ring

/-- The actual channel minus its literal Euler energy has the existing
summable pair-error majorant, with its positive multiplicity coefficient. -/
theorem abs_pairedEtaCurrentChannelEnergy_sub_euler_le (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCurrentChannelEnergy rho N - pairedEtaCurrentEulerChannelEnergy rho N| ≤
      (pairedEtaCurrentZeroEnergyCoefficient rho).re *
        (pairedEtaCurrentEulerPairErrorConstant rho 0 0 * pairedEtaCurrentMomentDecay rho N /
          (N + 1 : ℝ)) := by
  have h := norm_pairedEtaCurrent_product_sub_euler_le rho
    (analyticZetaZeroMultiplicity_positive rho) (analyticZetaZeroMultiplicity_positive rho) N
  rw [Complex.mul_conj', Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [norm_pairedEtaCurrentEulerMoment_zero_sq] at h
  simpa only [pairedEtaCurrentChannelEnergy, pairedEtaCurrentEulerChannelEnergy, mul_assoc,
    ← mul_sub, abs_mul, abs_of_pos (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho)] using
      mul_le_mul_of_nonneg_left h (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le

/-- The discrepancy from the explicit Euler channel is absolutely
summable throughout the open critical strip, for every actual multiplicity. -/
theorem summable_abs_pairedEtaCurrentChannelEnergy_sub_euler (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      |pairedEtaCurrentChannelEnergy rho N - pairedEtaCurrentEulerChannelEnergy rho N|) := by
  have hs : Summable (fun N : ℕ ↦ pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) := by
    simpa only [pow_zero, one_mul] using summable_pairedEtaCurrent_logPower_mul_decay_div rho 0
  have hm : Summable (fun N : ℕ ↦ (pairedEtaCurrentZeroEnergyCoefficient rho).re *
      (pairedEtaCurrentEulerPairErrorConstant rho 0 0 * pairedEtaCurrentMomentDecay rho N /
        (N + 1 : ℝ))) := by
    simpa only [mul_div_assoc] using
      (hs.mul_left (pairedEtaCurrentEulerPairErrorConstant rho 0 0)).mul_left
        (pairedEtaCurrentZeroEnergyCoefficient rho).re
  exact hm.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
    (abs_pairedEtaCurrentChannelEnergy_sub_euler_le rho)

private theorem shifted_rpow_sum_integral_bounds {r c : ℝ}
    (hr : -1 < r) (hr0 : r ≤ 0) (hc : 0 < c) (K : ℕ) :
    0 ≤ (∑ N ∈ Finset.range K, (c + N : ℝ) ^ r) -
        ((c + K : ℝ) ^ (r + 1) - c ^ (r + 1)) / (r + 1) ∧
      (∑ N ∈ Finset.range K, (c + N : ℝ) ^ r) -
        ((c + K : ℝ) ^ (r + 1) - c ^ (r + 1)) / (r + 1) ≤ c ^ r := by
  have hant : AntitoneOn (fun x : ℝ ↦ x ^ r) (Icc c (c + K)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (hc.trans_le ha.1) hab hr0
  have hlo := hant.integral_le_sum
  have hhi := hant.sum_le_integral
  rw [integral_rpow (Or.inl hr)] at hlo hhi
  have h := Finset.sum_range_succ' (fun N : ℕ ↦ (c + N : ℝ) ^ r) K
  rw [Finset.sum_range_succ] at h
  simp only [Nat.cast_zero, add_zero] at h
  have hn := Real.rpow_nonneg (show 0 ≤ c + K by positivity) r
  exact ⟨by linarith, by linarith⟩

private theorem tendsto_scaled_shifted_rpow_sum {r c : ℝ}
    (hr : -1 < r) (hr0 : r ≤ 0) (hc : 0 < c) :
    Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(r + 1)) *
      ∑ N ∈ Finset.range K, (c + N : ℝ) ^ r) atTop (𝓝 (1 / (r + 1))) := by
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(r + 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < r + 1)).comp hx
  have hratio : Tendsto (fun K : ℕ ↦ (c + K : ℝ) / (K + 1 : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c - 1)
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).add h
    convert h' using 1
    · ext K
      field_simp
      ring
    · simp
  have hp : Tendsto (fun K : ℕ ↦ ((c + K : ℝ) / (K + 1 : ℝ)) ^ (r + 1)) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hratio.rpow_const (Or.inl one_ne_zero)
  have hi : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(r + 1)) *
      (((c + K : ℝ) ^ (r + 1) - c ^ (r + 1)) / (r + 1))) atTop (𝓝 (1 / (r + 1))) := by
    have h := (hp.sub (hs.const_mul (c ^ (r + 1)))).div_const (r + 1)
    simp only [mul_zero, sub_zero] at h
    convert h using 1
    ext K
    rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity)]
    ring
  have he : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(r + 1)) *
      ((∑ N ∈ Finset.range K, (c + N : ℝ) ^ r) -
        ((c + K : ℝ) ^ (r + 1) - c ^ (r + 1)) / (r + 1))) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun K ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (shifted_rpow_sum_integral_bounds hr hr0 hc K).1)
      (fun K ↦ mul_le_mul_of_nonneg_left
        (shifted_rpow_sum_integral_bounds hr hr0 hc K).2 (Real.rpow_nonneg (by positivity) _))
    simpa only [zero_mul] using hs.mul_const (c ^ r)
  convert hi.add he using 1
  · ext K
    ring
  · simp

/-- The literal odd successor powers have their exact leading sum
constant. The harmless `K+1` normalization keeps every finite term defined
at a positive base, while preserving the large-cutoff coefficient. -/
theorem tendsto_scaled_odd_shifted_rpow_sum {tau : ℝ} (h0 : 0 < tau) (hhalf : tau < 1 / 2) :
    Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(1 - 2 * tau)) *
      ∑ N ∈ Finset.range K, (2 * N + 5 : ℝ) ^ (-2 * tau))
      atTop (𝓝 ((2 : ℝ) ^ (-2 * tau) / (1 - 2 * tau))) := by
  have h := (tendsto_scaled_shifted_rpow_sum
    (r := -2 * tau) (c := 5 / 2) (by linarith) (by linarith) (by norm_num)).const_mul
      ((2 : ℝ) ^ (-2 * tau))
  have hterm (N : ℕ) : (2 * N + 5 : ℝ) ^ (-2 * tau) =
      (2 : ℝ) ^ (-2 * tau) * (5 / 2 + N : ℝ) ^ (-2 * tau) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  simp only [show -2 * tau + 1 = 1 - 2 * tau by ring, mul_one_div] at h
  convert h using 1
  ext K
  simp only [hterm, ← Finset.mul_sum]
  ring

/-- After genuine absolute summability, the signed channel discrepancy
converges to its own complete series, retaining the finite offset. -/
theorem pairedEtaCurrentChannelEnergyPartialSum_sub_euler_tendsto (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ pairedEtaCurrentChannelEnergyPartialSum rho K -
      ∑ N ∈ Finset.range K, pairedEtaCurrentEulerChannelEnergy rho N) atTop
      (𝓝 (∑' N : ℕ, (pairedEtaCurrentChannelEnergy rho N - pairedEtaCurrentEulerChannelEnergy rho N))) := by
  have hs : Summable (fun N : ℕ ↦
      pairedEtaCurrentChannelEnergy rho N - pairedEtaCurrentEulerChannelEnergy rho N) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_abs_pairedEtaCurrentChannelEnergy_sub_euler rho
  simpa only [pairedEtaCurrentChannelEnergyPartialSum, Finset.sum_sub_distrib] using
    hs.hasSum.tendsto_sum_nat

/-- The positive left-half channel has the exact completed Euler
coefficient after division by its growing horizontal power. -/
theorem pairedEtaCurrentChannelEnergyPartialSum_scaled_tendsto_of_re_lt_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re < 1 / 2) :
    Tendsto (fun K : ℕ ↦ pairedEtaCurrentChannelEnergyPartialSum rho K /
      (K + 1 : ℝ) ^ (1 - 2 * rho.1.re)) atTop
      (𝓝 ((pairedEtaCurrentZeroEnergyCoefficient rho).re *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) *
          ((2 : ℝ) ^ (-2 * rho.1.re) / (1 - 2 * rho.1.re)))) := by
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) ^ (-(1 - 2 * rho.1.re))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * rho.1.re)).comp hx
  have he := hs.mul (pairedEtaCurrentChannelEnergyPartialSum_sub_euler_tendsto rho)
  simp only [zero_mul] at he
  have hm := (tendsto_scaled_odd_shifted_rpow_sum (NontrivialZetaZero.zero_lt_re rho) hrho).const_mul
    ((pairedEtaCurrentZeroEnergyCoefficient rho).re * (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4))
  convert hm.add he using 1
  · ext K
    simp only [pairedEtaCurrentEulerChannelEnergy, ← Finset.mul_sum,
      Real.rpow_neg (show (0 : ℝ) ≤ K + 1 by positivity)]
    ring
  · simp

/-- The explicit candidate leading coefficient of the reflected channel.
Strict positivity and its asymptotic meaning are asserted only right of
one half, where the actual displacement denominator is positive. -/
def pairedEtaCurrentDominantEnergyCoefficient (rho : NontrivialZetaZero) : ℝ :=
  (pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
    ‖pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1‖ ^ 2 *
      (2 : ℝ) ^ (-2 * (1 - rho.1.re)) / (4 * pairedEtaCurrentHorizontalDisplacement rho)

/-- Neither completion nor either multiplicity branch can annul the
dominant Euler coefficient of an actual right-half zero. -/
theorem pairedEtaCurrentDominantEnergyCoefficient_pos (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) : 0 < pairedEtaCurrentDominantEnergyCoefficient rho := by
  have hC := pairedEtaCurrentZeroEnergyCoefficient_re_pos (NontrivialZetaZero.conjugatePartner rho)
  have hchi := pairedEtaXiCompletionFactor_ne_zero
    (NontrivialZetaZero.zero_lt_re (NontrivialZetaZero.conjugatePartner rho))
    (NontrivialZetaZero.re_lt_one (NontrivialZetaZero.conjugatePartner rho))
  have hn : 0 < ‖pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1‖ :=
    norm_pos_iff.mpr hchi
  have he := pairedEtaCurrentHorizontalDisplacement_pos rho (ne_of_gt hrho)
  unfold pairedEtaCurrentDominantEnergyCoefficient
  positivity

/-- The full reflected channel has an exact positive leading coefficient,
using the genuine conjugate partner and the actual displacement exponent. -/
theorem pairedEtaCurrentPartnerEnergy_scaled_tendsto (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K /
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (pairedEtaCurrentDominantEnergyCoefficient rho)) := by
  have hp : (NontrivialZetaZero.conjugatePartner rho).1.re = 1 - rho.1.re := by
    simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re]
  have he : pairedEtaCurrentHorizontalDisplacement rho =
      1 - 2 * (NontrivialZetaZero.conjugatePartner rho).1.re := by
    rw [pairedEtaCurrentHorizontalDisplacement, abs_of_pos (by linarith : 0 < 2 * rho.1.re - 1), hp]
    ring
  have h := pairedEtaCurrentChannelEnergyPartialSum_scaled_tendsto_of_re_lt_half
    (NontrivialZetaZero.conjugatePartner rho) (by rw [hp]; linarith)
  rw [← he] at h
  convert h using 1
  unfold pairedEtaCurrentDominantEnergyCoefficient
  rw [hp]
  ring_nf

/-- The recessive channel's proved finite total disappears under the
growing normalization, leaving the same positive coefficient for the
complete signed normalized current. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_scaled_tendsto_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦ pairedEtaNormalizedReflectedEnergyPartialSum rho K /
      (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (pairedEtaCurrentDominantEnergyCoefficient rho)) := by
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hs := (tendsto_rpow_neg_atTop
    (pairedEtaCurrentHorizontalDisplacement_pos rho (ne_of_gt hrho))).comp hx
  have he := (pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_tendsto rho hrho).mul hs
  simp only [mul_zero] at he
  convert (pairedEtaCurrentPartnerEnergy_scaled_tendsto rho hrho).add he using 1
  · ext K
    simp only [Real.rpow_neg (show (0 : ℝ) ≤ K + 1 by positivity), Function.comp_apply]
    ring
  · simp

/-- The two independently proved absolutely summable transport errors
vanish after scaling. The unchanged weighted leading current therefore
has exactly four times the positive reflected endpoint coefficient. -/
theorem pairedEtaLeadingFluxSignedPartialSum_scaled_tendsto_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦ pairedEtaLeadingFluxSignedPartialSum rho K /
      (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (4 * pairedEtaCurrentDominantEnergyCoefficient rho)) := by
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hs := (tendsto_rpow_neg_atTop
    (pairedEtaCurrentHorizontalDisplacement_pos rho (ne_of_gt hrho))).comp hx
  have he := ((pairedEtaLeadingFluxSignedPartialSum_sub_fullInverse_tendsto rho).add
    (pairedEtaFullInverseEnergySignedPartialSum_sub_normalized_tendsto rho)).mul hs
  simp only [mul_zero] at he
  convert ((pairedEtaNormalizedReflectedEnergyPartialSum_scaled_tendsto_of_half_lt_re rho hrho).const_mul 4).add he using 1
  · ext K
    simp only [Real.rpow_neg (show (0 : ℝ) ≤ K + 1 by positivity), Function.comp_apply]
    ring
  · simp

private theorem tendsto_div_nat_rpow_of_add_one {f : ℕ → ℝ} {e A : ℝ}
    (h : Tendsto (fun K : ℕ ↦ f K / (K + 1 : ℝ) ^ e) atTop (𝓝 A)) :
    Tendsto (fun K : ℕ ↦ f K / (K : ℝ) ^ e) atTop (𝓝 A) := by
  have hr : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ) / (K : ℝ)) atTop (𝓝 1) := by
    have ht := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKN : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    field_simp
  have hp := hr.rpow_const (p := e) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hp
  have ht := h.mul hp
  simp only [mul_one] at ht
  convert ht using 1
  ext K
  rw [Real.div_rpow (by positivity) (Nat.cast_nonneg K)]
  have hq : (K + 1 : ℝ) ^ e ≠ 0 := (Real.rpow_pos_of_pos (by positivity) e).ne'
  rw [div_mul_div_cancel₀ hq]

/-- The partner asymptotic also holds with the literal `K^e` denominator;
the proof handles the initial zero cutoff separately from the limiting ratio. -/
theorem pairedEtaCurrentPartnerEnergy_natCutoff_scaled_tendsto
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K /
        (K : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (pairedEtaCurrentDominantEnergyCoefficient rho)) :=
  tendsto_div_nat_rpow_of_add_one (pairedEtaCurrentPartnerEnergy_scaled_tendsto rho hrho)

/-- The exact normalized signed current has the same explicit limit with
the literal cutoff normalization. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_natCutoff_scaled_tendsto_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦ pairedEtaNormalizedReflectedEnergyPartialSum rho K /
      (K : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (pairedEtaCurrentDominantEnergyCoefficient rho)) :=
  tendsto_div_nat_rpow_of_add_one
    (pairedEtaNormalizedReflectedEnergyPartialSum_scaled_tendsto_of_half_lt_re rho hrho)

/-- The unchanged original weighted current has the exact positive
`K^e` coefficient, with both finite transport corrections already justified. -/
theorem pairedEtaLeadingFluxSignedPartialSum_natCutoff_scaled_tendsto_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦ pairedEtaLeadingFluxSignedPartialSum rho K /
      (K : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho)
      atTop (𝓝 (4 * pairedEtaCurrentDominantEnergyCoefficient rho)) :=
  tendsto_div_nat_rpow_of_add_one
    (pairedEtaLeadingFluxSignedPartialSum_scaled_tendsto_of_half_lt_re rho hrho)

/-- Every coefficient strictly below the exact Euler coefficient is
eventually exceeded by the original signed current at a right-half zero.
This exposes the required independent contradiction rather than supplying it. -/
theorem pairedEtaLeadingFluxSignedPartialSum_gt_subdominant_eventually
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) {a : ℝ}
    (ha : a < 4 * pairedEtaCurrentDominantEnergyCoefficient rho) :
    ∀ᶠ K : ℕ in atTop, a * (K : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho <
      pairedEtaLeadingFluxSignedPartialSum rho K := by
  have ht := pairedEtaLeadingFluxSignedPartialSum_natCutoff_scaled_tendsto_of_half_lt_re rho hrho
  have h := ht.eventually (eventually_gt_nhds ha)
  filter_upwards [h, eventually_ge_atTop 1] with K hK hKpos
  have hx : (0 : ℝ) < K := by exact_mod_cast hKpos
  exact (lt_div_iff₀ (Real.rpow_pos_of_pos hx _)).mp hK

/-- A right-half zero prevents decay of the original current after its
source-power normalization: its proved limit is strictly positive. -/
theorem pairedEtaLeadingFluxSignedPartialSum_scaled_not_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ¬ Tendsto (fun K : ℕ ↦ pairedEtaLeadingFluxSignedPartialSum rho K /
      (K : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho) atTop (𝓝 0) := by
  intro h
  have he := tendsto_nhds_unique
    (pairedEtaLeadingFluxSignedPartialSum_natCutoff_scaled_tendsto_of_half_lt_re rho hrho) h
  have hp := pairedEtaCurrentDominantEnergyCoefficient_pos rho hrho
  linarith

end

end RiemannGaussian
