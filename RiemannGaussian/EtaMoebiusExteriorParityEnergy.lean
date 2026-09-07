import RiemannGaussian.EtaMoebiusExteriorParity
import RiemannGaussian.EtaMoebiusExteriorArithmetic
import RiemannGaussian.EtaLogEndpointControl

/-!
# Exact full exterior energy in parity coordinates

The two changes of variables in the endgame steer are proved for the
original grid carrier, using its exact right-closed parity representation.
The full parity integral is genuinely integrable away from zero. No near
shell is replaced by a complete-period covariance or by a norm envelope.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The exact parity sum is measurable on the full real physical axis. -/
theorem measurable_pairedEtaMoebiusGridParitySum (d M : ℕ) (w : ℕ → ℝ) :
    Measurable (pairedEtaMoebiusGridParitySum d M w) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (measurable_const.sub
    (measurable_const.mul (measurable_etaUnitIntervalColour.comp (measurable_const.mul measurable_id))))

/-- The complete weighted parity square is integrable above every positive physical endpoint, with a finite coefficient bound as the dominator. -/
theorem integrableOn_pairedEtaMoebiusGridParitySum_sq_div (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z : ℝ ↦ pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2) (Ioi a) := by
  have hi : IntegrableOn (fun z : ℝ ↦ 1 / z ^ 2) (Ioi a) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.rpow_neg (ha.trans hz).le, Real.rpow_two, one_div]
  have hb := hi.mul_bdd ((measurable_pairedEtaMoebiusGridParitySum d M w).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_pairedEtaMoebiusGridParitySum_le d M hw z) 2
      simpa only [sq_abs] using h)
  apply hb.congr
  exact Eventually.of_forall fun z ↦ by ring

/-- Exponentiation transports the complete original exterior square to the ordinary physical coordinate with its exact inverse-square weight. -/
theorem integral_pairedEtaMoebiusGrid_sq_eq_physical (d M : ℕ) (w : ℕ → ℝ) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) =
      ∫ x : ℝ in Ioi 2, ‖pairedEtaMoebiusTrialGridCombination d M w (Real.log x)‖ ^ 2 / x ^ 2 := by
  have hc := integral_comp_exp_Ioi
    (fun x : ℝ ↦ ‖pairedEtaMoebiusTrialGridCombination d M w (Real.log x)‖ ^ 2 / x ^ 2) (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hc
  rw [← hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [smul_eq_mul, Real.log_exp, Real.exp_neg]
  field_simp

/-- The entire actual exterior residual is exactly the finite signed parity-wave integral proposed in the endgame steer, with both changes of variables and all endpoints checked. -/
theorem integral_pairedEtaMoebiusGrid_exterior_eq_parity {d M : ℕ} (hd : 0 < d)
    (hMd : M ≤ d) (w : ℕ → ℝ) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) =
      (1 / (4 * (d : ℝ))) * ∫ z : ℝ in Ioi (2 / (d : ℝ)),
        pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [integral_pairedEtaMoebiusGrid_sq_eq_physical]
  have hc := integral_comp_mul_left_Ioi'
    (fun x : ℝ ↦ ‖pairedEtaMoebiusTrialGridCombination d M w (Real.log x)‖ ^ 2 / x ^ 2)
    (2 / (d : ℝ)) hdp
  rw [smul_eq_mul, mul_div_cancel₀ _ hdp.ne'] at hc
  rw [← hc]
  have he : (∫ z : ℝ in Ioi (2 / (d : ℝ)),
      ‖pairedEtaMoebiusTrialGridCombination d M w (Real.log ((d : ℝ) * z))‖ ^ 2 / ((d : ℝ) * z) ^ 2) =
      (1 / (4 * (d : ℝ) ^ 2)) * ∫ z : ℝ in Ioi (2 / (d : ℝ)),
        pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hzp : 0 < z := (div_pos (by norm_num) hdp).trans hz
    dsimp only
    rw [pairedEtaMoebiusTrialGridCombination_eq_paritySum hd hMd w hzp,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  field_simp

/-- The complete far parity tail has the exact inverse-square integral bound, independently of any periodic covariance approximation. -/
theorem integral_Ioi_pairedEtaMoebiusGridParitySum_sq_div_le (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) {a : ℝ} (ha : 0 < a) :
    (∫ z : ℝ in Ioi a, pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2) ≤
      4 * (M : ℝ) ^ 2 / a := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  calc
    _ ≤ ∫ z : ℝ in Ioi a, 4 * (M : ℝ) ^ 2 * z ^ (-2 : ℝ) := by
      apply integral_mono_ae (integrableOn_pairedEtaMoebiusGridParitySum_sq_div d M hw ha) (hi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.rpow_neg (ha.trans hz).le, Real.rpow_two, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ (sq_nonneg z)
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_pairedEtaMoebiusGridParitySum_le d M hw z) 2
      norm_num [sq_abs, mul_pow] at h ⊢
      exact h
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- The original parity interval that still needs a signed covariance estimate after the genuinely far exterior is removed. -/
def pairedEtaMoebiusNearParityEnergy (d M : ℕ) (w : ℕ → ℝ) : ℝ :=
  (1 / (4 * (d : ℝ))) * ∫ z : ℝ in Ioc (2 / (d : ℝ)) 2,
    pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2

/-- The actual exterior energy is its unchanged near parity interval plus the entire far parity tail. -/
theorem integral_pairedEtaMoebiusGrid_exterior_eq_near_add_far {d M : ℕ} (hd : 0 < d)
    (hMd : M ≤ d) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) =
      pairedEtaMoebiusNearParityEnergy d M w + (1 / (4 * (d : ℝ))) *
        ∫ z : ℝ in Ioi 2, pairedEtaMoebiusGridParitySum d M w z ^ 2 / z ^ 2 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : 2 / (d : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hdp).mpr
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hi := integrableOn_pairedEtaMoebiusGridParitySum_sq_div d M hw
    (div_pos (by norm_num : (0 : ℝ) < 2) hdp)
  have he := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hle))
  rw [intervalIntegral.integral_of_le hle] at he
  rw [integral_pairedEtaMoebiusGrid_exterior_eq_parity hd hMd w, ← he, mul_add]
  rfl

/-- All of the genuine far exterior is charged by `M²/(2d)`; the remaining near parity energy retains every Möbius and parity sign. -/
theorem integral_pairedEtaMoebiusGrid_exterior_le_near_add_allowance {d M : ℕ} (hd : 0 < d)
    (hMd : M ≤ d) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) ≤
      pairedEtaMoebiusNearParityEnergy d M w + (M : ℝ) ^ 2 / (2 * d) := by
  rw [integral_pairedEtaMoebiusGrid_exterior_eq_near_add_far hd hMd hw]
  apply add_le_add le_rfl
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have h := mul_le_mul_of_nonneg_left
    (integral_Ioi_pairedEtaMoebiusGridParitySum_sq_div_le d M hw (by norm_num : (0 : ℝ) < 2))
    (by positivity : 0 ≤ 1 / (4 * (d : ℝ)))
  exact h.trans_eq (by field_simp)

end

end RiemannGaussian
