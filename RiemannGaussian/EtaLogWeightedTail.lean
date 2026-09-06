import RiemannGaussian.EtaLogFinitePart
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The retained complex eta tail and its endpoint test

A slow Lipschitz test can be frozen at the actual logarithmic cutoff
with a first-moment exponential error. The scalar Wallis evaluation remains
available without discarding the complex value of that endpoint test.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual complex weighted tail beyond an arithmetic cutoff. -/
def pairedEtaWeightedMismatchTail (r R : ℝ) (F : ℝ → ℂ) (M : ℕ) : ℂ :=
  ∫ t in Ioi (Real.log (M : ℝ)),
    (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)

/-- The first exponential moment about a nonnegative lower endpoint is
genuinely integrable. -/
theorem integrableOn_etaExponentialFirstMoment {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ ↦ (t - a) * Real.exp (-t)) (Ioi a) := by
  have hi0 : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow (s := 1) (p := 1) (by norm_num) (by norm_num))
  have hi := hi0.mono_set (Ioi_subset_Ioi ha)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi a) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) a
  apply (hi.sub (he.const_mul a)).congr_fun _ measurableSet_Ioi
  intro t _
  change t * Real.exp (-t) - a * Real.exp (-t) = (t - a) * Real.exp (-t)
  ring

/-- The first exponential moment at its lower endpoint has exact mass
`exp(-a)`, so freezing the slow tail costs one reciprocal cutoff. -/
theorem integral_etaExponentialFirstMoment {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioi a, (t - a) * Real.exp (-t)) = Real.exp (-a) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ -(t - a + 1) * Real.exp (-t))
      ((t - a) * Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).sub_const a).add_const 1).neg.mul
      ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg) using 1 <;>
      first | rfl | (simp only [id_eq, Pi.neg_apply, Function.comp_apply]; ring)
  have hte : Tendsto (fun t : ℝ ↦ t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have ht : Tendsto (fun t : ℝ ↦ -(t - a + 1) * Real.exp (-t)) atTop (𝓝 0) := by
    convert (hte.add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - a))).neg using 1 <;>
      first | (funext t; ring) | simp
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ ↦ hd t)
    (integrableOn_etaExponentialFirstMoment ha) ht]
  simp

/-- The actual complex tail retains genuine integrability for bounded
measurable tests. -/
theorem integrableOn_pairedEtaWeightedMismatchTailKernel {F : ℝ → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (r R : ℝ) (M : ℕ) :
    IntegrableOn (fun t ↦ (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R))
      (Ioi (Real.log (M : ℝ))) := integrableOn_pairedEtaWeightedMismatchKernel hF hB r R _

/-- Freezing a slow complex test at the actual tail cutoff has an error
bounded by `K/(R*M)`, independent of the displacement. -/
theorem pairedEtaWeightedMismatchTail_freeze_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (r : ℝ) :
    ‖pairedEtaWeightedMismatchTail r R F M -
      pairedEtaMismatchTail (1 / 2) r M • F (Real.log (M : ℝ) / R)‖ ≤ (K : ℝ) / (R * M) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlog := Real.log_nonneg hM1
  have hi := integrableOn_pairedEtaWeightedMismatchTailKernel hF.continuous.measurable hB r R M
  have hs : IntegrableOn (fun t : ℝ ↦ pairedEtaLogShiftMismatch r t * Real.exp (-t))
      (Ioi (Real.log (M : ℝ))) := by
    simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul] using
      integrableOn_pairedEtaMismatchKernel (sigma := 1 / 2) (by norm_num) r (Real.log (M : ℝ))
  unfold pairedEtaWeightedMismatchTail pairedEtaMismatchTail
  simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul]
  rw [← integral_smul_const, ← integral_sub hi (hs.smul_const _)]
  calc
    _ ≤ ∫ t in Ioi (Real.log (M : ℝ)), ((K : ℝ) / R) * ((t - Real.log M) * Real.exp (-t)) := by
      apply norm_integral_le_of_norm_le ((integrableOn_etaExponentialFirstMoment hlog).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hdiff : 0 ≤ t - Real.log (M : ℝ) := by linarith [ht.out]
      have hLip : ‖F (t / R) - F (Real.log (M : ℝ) / R)‖ ≤
          (K : ℝ) * ((t - Real.log M) / R) := by
        simpa only [dist_eq_norm, Real.norm_eq_abs, ← sub_div,
          abs_of_nonneg (div_nonneg hdiff hR.le)] using hF.dist_le_mul (t / R) (Real.log M / R)
      rw [← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le)]
      calc
        _ ≤ (pairedEtaLogShiftMismatch r t * Real.exp (-t)) *
            ((K : ℝ) * ((t - Real.log M) / R)) :=
          mul_le_mul_of_nonneg_left hLip
            (mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le)
        _ ≤ Real.exp (-t) * ((K : ℝ) * ((t - Real.log M) / R)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t))
            (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, integral_etaExponentialFirstMoment hlog,
        Real.exp_neg, Real.exp_log hMpos]
      ring

/-- The normalized complex tail has the scalar Wallis coefficient times
the original endpoint test, with both sources of error explicit. -/
theorem pairedEtaWeightedMismatchTail_scaled_wallis_error_le {r : ℝ} (hr : 0 < r)
    (hepsilon1 : Real.exp r - 1 ≤ 1) {M : ℕ} (hM : 1 ≤ M)
    (hcutoff : (Real.exp r - 1) * M ≤ 1) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M -
      (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * M)) •
        F (Real.log (M : ℝ) / R)‖ ≤
      (K : ℝ) / ((Real.exp r - 1) * R * M) +
        B * (4 * (Real.exp r - 1) / ((Real.exp r - 1) * M) +
          (Real.exp r - 1) / ((Real.exp r - 1) * M) ^ 2) := by
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  have hmain := pairedEtaMismatchTail_half_wallis_error_le hr hepsilon1 hM hcutoff
  have hfreeze := pairedEtaWeightedMismatchTail_freeze_error_le hM hR hF hB r
  calc
    _ ≤ ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M -
          (pairedEtaMismatchTail (1 / 2) r M / (Real.exp r - 1)) • F (Real.log (M : ℝ) / R)‖ +
        ‖(pairedEtaMismatchTail (1 / 2) r M / (Real.exp r - 1)) • F (Real.log (M : ℝ) / R) -
          (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * M)) •
            F (Real.log (M : ℝ) / R)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K : ℝ) / ((Real.exp r - 1) * R * M) +
        B * (4 * (Real.exp r - 1) / ((Real.exp r - 1) * M) +
          (Real.exp r - 1) / ((Real.exp r - 1) * M) ^ 2) := by
      apply add_le_add
      · have hid : (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M -
            (pairedEtaMismatchTail (1 / 2) r M / (Real.exp r - 1)) • F (Real.log (M : ℝ) / R) =
          (Real.exp r - 1)⁻¹ • (pairedEtaWeightedMismatchTail r R F M -
            pairedEtaMismatchTail (1 / 2) r M • F (Real.log (M : ℝ) / R)) := by
          rw [smul_sub, smul_smul, div_eq_mul_inv, mul_comm (Real.exp r - 1)⁻¹]
        rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
        calc
          _ ≤ (Real.exp r - 1)⁻¹ * ((K : ℝ) / (R * M)) :=
            mul_le_mul_of_nonneg_left hfreeze (inv_nonneg.mpr he.le)
          _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul hmain (hB _) (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

/-- At the actual displacement cutoff the complex weighted tail has a
uniform endpoint error `4K/R + 32(exp(r)-1)B`. -/
theorem pairedEtaWeightedMismatchTail_cutoff_error_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F (pairedEtaShiftBoundaryCutoff r) -
      (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r)) •
        F (Real.log (pairedEtaShiftBoundaryCutoff r : ℝ) / R)‖ ≤
      4 * (K : ℝ) / R + 32 * (Real.exp r - 1) * B := by
  obtain ⟨he1, haL, haU⟩ := pairedEtaShiftBoundaryCutoff_rescaled_bounds hr hrsmall
  obtain ⟨hM, _, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  apply (pairedEtaWeightedMismatchTail_scaled_wallis_error_le hr he1 (by omega) haU hR hF hB).trans
  have hfirst : (K : ℝ) / ((Real.exp r - 1) * R * pairedEtaShiftBoundaryCutoff r) ≤ 4 * (K : ℝ) / R := by
    calc
      _ = ((K : ℝ) / R) / ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ((K : ℝ) / R) / (1 / 4) := div_le_div_of_nonneg_left (by positivity) (by norm_num) haL
      _ = _ := by ring
  have haL2 : (1 / 16 : ℝ) ≤ ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ^ 2 := by nlinarith
  have hsecond : 4 * (Real.exp r - 1) / ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) +
      (Real.exp r - 1) / ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ^ 2 ≤ 32 * (Real.exp r - 1) := by
    calc
      _ ≤ 4 * (Real.exp r - 1) / (1 / 4) + (Real.exp r - 1) / (1 / 16) :=
        add_le_add (div_le_div_of_nonneg_left (by positivity) (by norm_num) haL)
          (div_le_div_of_nonneg_left he.le (by norm_num) haL2)
      _ = _ := by ring
  exact (add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hB0)).trans_eq (by ring)

end

end RiemannGaussian
