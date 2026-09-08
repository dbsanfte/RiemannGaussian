import RiemannGaussian.EtaCurrentOddWeightStepAsymptotic

/-!
# Quantitative removal of the recessive reflected-energy channel

At an actual zero strictly right of one half, the original channel's
zeroth-energy series converges. Its complete tail from `K ≥ 1` is at most
`C.re * Q² / (2*Re(rho)-1) * K^(1-2*Re(rho))`. The exact signed identities
retain this tail and the full reflected channel. Thus the original colour
can contribute only a finite total cancellation, with an explicit rate on
every late finite band. No upper saving for the reflected channel is proved.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate Interval

namespace RiemannGaussian

noncomputable section

/-- The full positive zeroth-energy channel, with its actual
multiplicity-selected coefficient and physical successor cutoff. -/
def pairedEtaCurrentChannelEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaCurrentZeroEnergyCoefficient rho).re *
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ^ 2

/-- Each actual channel energy is nonnegative. -/
theorem pairedEtaCurrentChannelEnergy_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentChannelEnergy rho N :=
  mul_nonneg (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le (sq_nonneg _)

/-- The actual squared moment retains twice its horizontal decay exponent. -/
theorem norm_pairedEtaFiniteCompletedMoment_sq_le_rpow (rho : NontrivialZetaZero)
    {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ ^ 2 ≤
      pairedEtaCurrentMomentConstant rho ^ 2 * (N + 1 : ℝ) ^ (-2 * rho.1.re) := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hD := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hdec : pairedEtaCurrentMomentDecay rho N ^ 2 ≤
      (N + 1 : ℝ) ^ (-2 * rho.1.re) := by
    unfold pairedEtaCurrentMomentDecay
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show -rho.1.re * (2 : ℝ) = -2 * rho.1.re by ring]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast (show N + 1 ≤ 2 * (N + 1) + 1 by omega))
      (by linarith [NontrivialZetaZero.zero_lt_re rho])
  calc
    _ ≤ (pairedEtaCurrentMomentConstant rho * pairedEtaCurrentMomentDecay rho N) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hQ hD)).mpr
        (norm_pairedEtaFiniteCompletedMoment_lower_le rho hk N)
    _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hdec (sq_nonneg _)

/-- The original completed channel has an explicit summable majorant
when its zero is right of the critical line. -/
theorem pairedEtaCurrentChannelEnergy_le_rpow (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentChannelEnergy rho N ≤
      (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 *
        (N + 1 : ℝ) ^ (-2 * rho.1.re) := by
  exact (mul_le_mul_of_nonneg_left
    (norm_pairedEtaFiniteCompletedMoment_sq_le_rpow rho (analyticZetaZeroMultiplicity_positive rho) N)
    (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le).trans_eq (by ring)

/-- Every lower-order completed moment is square summable at an actual
right-half zero; no finite cutoff is being held fixed. -/
theorem summable_norm_pairedEtaFiniteCompletedMoment_sq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho) :
    Summable (fun N : ℕ ↦ ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ ^ 2) := by
  have hs : Summable (fun N : ℕ ↦ (N + 1 : ℝ) ^ (-2 * rho.1.re)) := by
    convert (Real.summable_one_div_nat_add_rpow 1 (2 * rho.1.re)).2 (by linarith) using 1
    ext N
    rw [show -2 * rho.1.re = -(2 * rho.1.re) by ring, Real.rpow_neg (by positivity), one_div,
      abs_of_nonneg (by positivity)]
  exact (hs.mul_left (pairedEtaCurrentMomentConstant rho ^ 2)).of_nonneg_of_le
    (fun _ ↦ sq_nonneg _) (norm_pairedEtaFiniteCompletedMoment_sq_le_rpow rho hk)

/-- The original positive channel has a finite total energy on the right
half of the critical strip, including arbitrary actual multiplicity. -/
theorem summable_pairedEtaCurrentChannelEnergy (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) : Summable (pairedEtaCurrentChannelEnergy rho) :=
  (summable_norm_pairedEtaFiniteCompletedMoment_sq rho hrho
    (analyticZetaZeroMultiplicity_positive rho)).mul_left _

private theorem shifted_power_sum_le {r : ℝ} (hr : r < -1) {K : ℕ} (hK : 1 ≤ K) (L : ℕ) :
    (∑ n ∈ Finset.range L, (K + n + 1 : ℝ) ^ r) ≤ (K : ℝ) ^ (r + 1) / (-r - 1) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hant : AntitoneOn (fun x : ℝ ↦ x ^ r) (Icc (K : ℝ) (K + L : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (hKR.trans_le ha.1) hab (by linarith)
  have hi : (∑ n ∈ Finset.range L, (K + n + 1 : ℝ) ^ r) ≤
      ∫ x : ℝ in (K : ℝ)..(K + L : ℝ), x ^ r := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hant.sum_le_integral
  have hzero : (0 : ℝ) ∉ [[(K : ℝ), (K + L : ℝ)]] := by
    rw [uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg L) : (K : ℝ) ≤ K + L)]
    exact fun h ↦ (not_le_of_gt hKR) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)] at hi
  apply hi.trans
  have hd : 0 < -r - 1 := by linarith
  rw [show ((K + L : ℝ) ^ (r + 1) - (K : ℝ) ^ (r + 1)) / (r + 1) =
      ((K : ℝ) ^ (r + 1) - (K + L : ℝ) ^ (r + 1)) / (-r - 1) by
        rw [show -r - 1 = -(r + 1) by ring, div_neg, ← neg_div, neg_sub] ]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hd.le

/-- A finite late band of the actual right-hand channel has a bound
independent of its length and decaying in its starting cutoff. -/
theorem sum_pairedEtaCurrentChannelEnergy_band_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {K : ℕ} (hK : 1 ≤ K) (L : ℕ) :
    (∑ n ∈ Finset.range L, pairedEtaCurrentChannelEnergy rho (K + n)) ≤
      (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
        (2 * rho.1.re - 1) * (K : ℝ) ^ (1 - 2 * rho.1.re) := by
  have hC : 0 ≤ (pairedEtaCurrentZeroEnergyCoefficient rho).re *
      pairedEtaCurrentMomentConstant rho ^ 2 :=
    mul_nonneg (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le (sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ Finset.range L,
        (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 *
          (K + n + 1 : ℝ) ^ (-2 * rho.1.re) :=
      Finset.sum_le_sum (fun n _ ↦ by simpa only [Nat.cast_add] using
        pairedEtaCurrentChannelEnergy_le_rpow rho (K + n))
    _ = ((pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2) *
        ∑ n ∈ Finset.range L, (K + n + 1 : ℝ) ^ (-2 * rho.1.re) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (shifted_power_sum_le (by linarith : -2 * rho.1.re < -1) hK L) hC
      apply h.trans_eq
      rw [show -2 * rho.1.re + 1 = 1 - 2 * rho.1.re by ring,
        show -(-2 * rho.1.re) - 1 = 2 * rho.1.re - 1 by ring]
      ring

/-- The complete actual right-channel tail has the same explicit power
bound as every finite band. Convergence is established before taking the limit. -/
theorem tsum_pairedEtaCurrentChannelEnergy_tail_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {K : ℕ} (hK : 1 ≤ K) :
    (∑' n : ℕ, pairedEtaCurrentChannelEnergy rho (K + n)) ≤
      (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
        (2 * rho.1.re - 1) * (K : ℝ) ^ (1 - 2 * rho.1.re) := by
  have hs : Summable (fun n : ℕ ↦ pairedEtaCurrentChannelEnergy rho (K + n)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff K).2 (summable_pairedEtaCurrentChannelEnergy rho hrho)
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat
    (Eventually.of_forall (sum_pairedEtaCurrentChannelEnergy_band_le rho hrho hK))

/-- One complete positive-channel partial sum, kept separately so that
the signed comparison can retain both colours exactly. -/
def pairedEtaCurrentChannelEnergyPartialSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.range K, pairedEtaCurrentChannelEnergy rho N

/-- The normalized current is the exact difference of its two full
positive channel sums, with no diagonal or interaction removed. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_eq_channels (rho : NontrivialZetaZero) (K : ℕ) :
    pairedEtaNormalizedReflectedEnergyPartialSum rho K =
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
        pairedEtaCurrentChannelEnergyPartialSum rho K := by
  simp only [pairedEtaNormalizedReflectedEnergyPartialSum, pairedEtaCurrentReflectedEnergy,
    pairedEtaCurrentChannelEnergyPartialSum, pairedEtaCurrentChannelEnergy, Finset.sum_sub_distrib]

/-- Exact removal of the finite right-channel total leaves its genuine
positive tail, rather than discarding it from the signed current. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_eq_tail
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (K : ℕ) :
    pairedEtaNormalizedReflectedEnergyPartialSum rho K -
      (pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
        ∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N) =
      ∑' n : ℕ, pairedEtaCurrentChannelEnergy rho (K + n) := by
  have h := (summable_pairedEtaCurrentChannelEnergy rho hrho).sum_add_tsum_nat_add K
  rw [pairedEtaNormalizedReflectedEnergyPartialSum_eq_channels]
  simp only [pairedEtaCurrentChannelEnergyPartialSum, Nat.add_comm] at *
  linarith

/-- The full signed current and the surviving reflected energy, after
its finite offset, differ by a nonnegative explicitly decaying quantity. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_bounds
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) {K : ℕ} (hK : 1 ≤ K) :
    0 ≤ pairedEtaNormalizedReflectedEnergyPartialSum rho K -
        (pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
          ∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N) ∧
      pairedEtaNormalizedReflectedEnergyPartialSum rho K -
        (pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
          ∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N) ≤
        (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
          (2 * rho.1.re - 1) * (K : ℝ) ^ (1 - 2 * rho.1.re) := by
  rw [pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_eq_tail rho hrho]
  exact ⟨tsum_nonneg (fun _ ↦ pairedEtaCurrentChannelEnergy_nonneg rho _),
    tsum_pairedEtaCurrentChannelEnergy_tail_le rho hrho hK⟩

/-- The finite total of the recessive channel is itself bounded by its
literal first energy and an explicit integral-comparison constant. -/
theorem tsum_pairedEtaCurrentChannelEnergy_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    (∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N) ≤
      pairedEtaCurrentChannelEnergy rho 0 +
        (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
          (2 * rho.1.re - 1) := by
  have h := (summable_pairedEtaCurrentChannelEnergy rho hrho).sum_add_tsum_nat_add 1
  have ht := tsum_pairedEtaCurrentChannelEnergy_tail_le rho hrho (K := 1) (by rfl)
  simp only [Finset.sum_range_one, Nat.cast_one, Real.one_rpow, mul_one, Nat.add_comm] at h ht
  linarith

/-- The difference between a reflected positive-energy band and the
signed band is exactly the original colour on that same finite band. -/
theorem pairedEtaNormalizedReflectedEnergy_band_sub_eq (rho : NontrivialZetaZero) (K L : ℕ) :
    pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) (K + L) -
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
      (pairedEtaNormalizedReflectedEnergyPartialSum rho (K + L) -
        pairedEtaNormalizedReflectedEnergyPartialSum rho K) =
      ∑ n ∈ Finset.range L, pairedEtaCurrentChannelEnergy rho (K + n) := by
  simp only [pairedEtaNormalizedReflectedEnergyPartialSum_eq_channels,
    pairedEtaCurrentChannelEnergyPartialSum, Finset.sum_range_add]
  ring

/-- Removing the entire recessive colour costs a nonnegative decaying
allowance on every late finite band, uniformly in the band's length. -/
theorem pairedEtaNormalizedReflectedEnergy_band_sub_bounds
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) {K : ℕ} (hK : 1 ≤ K) (L : ℕ) :
    0 ≤ pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) (K + L) -
        pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
        (pairedEtaNormalizedReflectedEnergyPartialSum rho (K + L) -
          pairedEtaNormalizedReflectedEnergyPartialSum rho K) ∧
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) (K + L) -
        pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
        (pairedEtaNormalizedReflectedEnergyPartialSum rho (K + L) -
          pairedEtaNormalizedReflectedEnergyPartialSum rho K) ≤
        (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
          (2 * rho.1.re - 1) * (K : ℝ) ^ (1 - 2 * rho.1.re) := by
  rw [pairedEtaNormalizedReflectedEnergy_band_sub_eq]
  exact ⟨Finset.sum_nonneg (fun _ _ ↦ pairedEtaCurrentChannelEnergy_nonneg rho _),
    sum_pairedEtaCurrentChannelEnergy_band_le rho hrho hK L⟩

/-- The signed difference from the full reflected energy converges to
the negative of the genuine finite original-channel total. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_tendsto
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun K : ℕ ↦ pairedEtaNormalizedReflectedEnergyPartialSum rho K -
      pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K)
      atTop (𝓝 (-(∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N))) := by
  simpa only [pairedEtaNormalizedReflectedEnergyPartialSum_eq_channels,
    sub_sub_cancel_left, pairedEtaCurrentChannelEnergyPartialSum] using
      (summable_pairedEtaCurrentChannelEnergy rho hrho).hasSum.tendsto_sum_nat.neg

/-- The unchanged weighted leading current inherits the same comparison
with the surviving positive reflected sum, paying both upstream transport
budgets and the explicit recessive tail. -/
theorem pairedEtaLeadingFluxSignedPartialSum_reflected_error_le
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) {K : ℕ} (hK : 1 ≤ K) :
    |pairedEtaLeadingFluxSignedPartialSum rho K -
      4 * (pairedEtaCurrentChannelEnergyPartialSum (NontrivialZetaZero.conjugatePartner rho) K -
        ∑' N : ℕ, pairedEtaCurrentChannelEnergy rho N)| ≤
      (∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) +
        (∑' N : ℕ, pairedEtaCurrentStepNormalizationErrorEnvelope rho N) +
        4 * ((pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 /
          (2 * rho.1.re - 1) * (K : ℝ) ^ (1 - 2 * rho.1.re)) := by
  have hb := pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_bounds rho hrho hK
  apply (abs_sub_le _ (4 * pairedEtaNormalizedReflectedEnergyPartialSum rho K) _).trans
  apply add_le_add (pairedEtaLeadingFluxSignedPartialSum_normalized_error_le rho K)
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_left hb.2 (by norm_num)

end

end RiemannGaussian
