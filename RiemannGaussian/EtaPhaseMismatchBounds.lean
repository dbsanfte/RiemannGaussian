import RiemannGaussian.EtaLogWeightedBoundary

/-!
# Measurability and tail estimates for complex eta displacement

The complete complex phase remains the primary carrier. These norm bounds
control its arithmetic tails and provide integrable majorants for later
Gaussian limits, independently of the real phase.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complex phase displacement is bounded by the uncoloured arithmetic
displacement, without replacing its definition by that bound. -/
theorem norm_pairedEtaPhaseMismatch_le (sigma r : ℝ) (phi : ℝ → ℝ) :
    ‖pairedEtaPhaseMismatch sigma phi r‖ ≤ pairedEtaMismatch sigma r := by
  calc
    _ ≤ ∫ t in Ioi 0,
        ‖(pairedEtaLogShiftMismatch r t : ℂ) * pairedEtaShiftPhaseKernel sigma phi r t‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t ↦ by
        dsimp only
        rw [norm_mul, norm_pairedEtaShiftPhaseKernel, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg r t)]

/-- A measurable phase gives a measurable complex displacement as a
function of the displacement parameter. -/
theorem measurable_pairedEtaPhaseMismatch {phi : ℝ → ℝ} (hphi : Measurable phi)
    (sigma : ℝ) : Measurable (pairedEtaPhaseMismatch sigma phi) := by
  have hp : Measurable (fun p : ℝ × ℝ ↦
      Complex.exp ((((phi (p.2 + p.1) - phi p.2) : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.measurable.comp
      (((hphi.comp (measurable_snd.add measurable_fst)).sub
        (hphi.comp measurable_snd)).complex_ofReal.mul_const Complex.I)
  have hm : Measurable (fun p : ℝ × ℝ ↦
      (pairedEtaLogShiftMismatch p.1 p.2 : ℂ) * pairedEtaShiftPhaseKernel sigma phi p.1 p.2) :=
    measurable_pairedEtaLogShiftMismatch.complex_ofReal.mul
      (((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable.complex_ofReal).mul hp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- Phase-uniform complex tail control at an arbitrary real time cutoff. -/
theorem norm_pairedEtaPhaseMismatch_time_tail_le {sigma : ℝ} (hsigma : 0 < sigma)
    (phi : ℝ → ℝ) (r a : ℝ) :
    ‖∫ t in Ioi a, (pairedEtaLogShiftMismatch r t : ℂ) *
      pairedEtaShiftPhaseKernel sigma phi r t‖ ≤ Real.exp (-(2 * sigma) * a) / (2 * sigma) := by
  calc
    _ ≤ ∫ t in Ioi a, Real.exp (-(2 * sigma) * t) := by
      apply norm_integral_le_of_norm_le
        (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) a)
      exact Eventually.of_forall fun t ↦ by
        rw [norm_mul, norm_pairedEtaShiftPhaseKernel, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg r t)]
        exact mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t)
    _ = _ := by rw [integral_exp_mul_Ioi (by linarith)]; ring

/-- An arbitrary bounded complex test has a critical arithmetic time tail
bounded by its supremum times the exact exponential tail mass. -/
theorem norm_pairedEtaWeightedMismatch_time_tail_le {F : ℝ → ℂ} {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (r R a : ℝ) :
    ‖∫ t in Ioi a, (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)‖ ≤
      B * Real.exp (-a) := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi a) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) a
  calc
    _ ≤ ∫ t in Ioi a, B * Real.exp (-t) := by
      apply norm_integral_le_of_norm_le (he.const_mul B)
      exact Eventually.of_forall fun t ↦ by
        have hm := pairedEtaLogShiftMismatch_nonneg r t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm (Real.exp_pos _).le)]
        calc
          _ ≤ (pairedEtaLogShiftMismatch r t * Real.exp (-t)) * B :=
            mul_le_mul_of_nonneg_left (hB _) (mul_nonneg hm (Real.exp_pos _).le)
          _ ≤ Real.exp (-t) * B := mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t)) hB0
          _ = _ := mul_comm _ _
    _ = _ := by
      rw [integral_const_mul]
      have hi := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) a
      simpa only [neg_one_mul, div_neg, div_one, neg_neg] using congrArg (B * ·) hi

/-- The critical exponential mass on every positive finite time interval
is at most one. -/
theorem integral_exp_neg_Ioc_le_one {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioc 0 a, Real.exp (-t)) ≤ 1 := by
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  have hi := intervalIntegral.integral_Ioi_sub_Ioi he ha
  rw [intervalIntegral.integral_of_le ha] at hi
  rw [← hi]
  have h0 := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  have h1 := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) a
  simp only [neg_one_mul, div_neg, div_one, neg_neg, neg_zero, Real.exp_zero] at h0 h1
  rw [h0, h1]
  linarith [Real.exp_pos (-a)]

end

end RiemannGaussian
