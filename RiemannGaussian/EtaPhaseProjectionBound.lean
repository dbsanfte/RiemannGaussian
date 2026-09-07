import RiemannGaussian.EtaPhaseProjectionKernel

/-!
# A direct eta phase bound on the right-half zero coordinate

The actual zero annihilates one exponential in the retained complex
projection. Cauchy--Schwarz on the literal eta support bounds the remaining
boundary value by the ratio `(1-beta)/beta`. Every square integral and
support restriction is discharged by the explicit projection calculation.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The exact boundary eta Laplace value at the selected ordinate. -/
def pairedEtaPhaseBoundaryValue (y : ℝ) : ℂ :=
  pairedEtaLaplacePartition (1 + (y : ℂ) * Complex.I)

/-- The complex projection keeps the common ordinate and both decay exponents. -/
def pairedEtaPhaseProjectionKernel (beta y t : ℝ) : ℂ :=
  Complex.exp (-(1 + (y : ℂ) * Complex.I) * t) -
    (etaPhaseProjectionCoefficient beta : ℂ) * Complex.exp (-((beta : ℂ) + (y : ℂ) * Complex.I) * t)

/-- The full complex kernel factors into its unchanged phase and the real projection residual. -/
theorem pairedEtaPhaseProjectionKernel_eq_phase (beta y t : ℝ) :
    pairedEtaPhaseProjectionKernel beta y t =
      Complex.exp (-((y : ℂ) * Complex.I) * t) *
        (Real.exp (-(1 / 2) * t) : ℂ) * (etaPhaseProjectionResidual beta t : ℂ) := by
  unfold pairedEtaPhaseProjectionKernel etaPhaseProjectionResidual
  push_cast
  have h1 : Complex.exp (-((y : ℂ) * Complex.I) * t) *
      Complex.exp (-(1 / 2) * (t : ℂ)) * Complex.exp (-(1 / 2) * (t : ℂ)) =
        Complex.exp (-(1 + (y : ℂ) * Complex.I) * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-((y : ℂ) * Complex.I) * t) *
      Complex.exp (-(1 / 2) * (t : ℂ)) * Complex.exp (-((beta : ℂ) - 1 / 2) * t) =
        Complex.exp (-((beta : ℂ) + (y : ℂ) * Complex.I) * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (-((y : ℂ) * Complex.I) * t) *
        Complex.exp (-(1 / 2) * (t : ℂ)) * Complex.exp (-(1 / 2) * (t : ℂ)) -
        (etaPhaseProjectionCoefficient beta : ℂ) *
          (Complex.exp (-((y : ℂ) * Complex.I) * t) *
            Complex.exp (-(1 / 2) * (t : ℂ)) * Complex.exp (-((beta : ℂ) - 1 / 2) * t)) := by rw [h1, h2]
    _ = _ := by ring

/-- Taking the norm only after phase factorization gives the exact real product used by Cauchy--Schwarz. -/
theorem norm_pairedEtaPhaseProjectionKernel (beta y t : ℝ) :
    ‖pairedEtaPhaseProjectionKernel beta y t‖ =
      ‖Real.exp (-(1 / 2) * t)‖ * ‖etaPhaseProjectionResidual beta t‖ := by
  rw [pairedEtaPhaseProjectionKernel_eq_phase, norm_mul, norm_mul, Complex.norm_exp]
  norm_num [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.norm_real]

/-- Both complex projection terms are integrable on the actual infinite eta support. -/
theorem integrable_pairedEtaPhaseProjectionKernel {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    Integrable (pairedEtaPhaseProjectionKernel beta y) pairedEtaLogMeasure := by
  have h1 := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := 1 + (y : ℂ) * Complex.I) (by norm_num)
  have h2 := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (beta : ℂ) + (y : ℂ) * Complex.I) (by simpa using hb)
  exact h1.sub (h2.const_mul _)

/-- Integrating preserves the exact complex boundary value and its zero-dependent correction. -/
theorem integral_pairedEtaPhaseProjectionKernel {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    (∫ t : ℝ, pairedEtaPhaseProjectionKernel beta y t ∂pairedEtaLogMeasure) =
      pairedEtaPhaseBoundaryValue y - (etaPhaseProjectionCoefficient beta : ℂ) *
        pairedEtaLaplacePartition ((beta : ℂ) + (y : ℂ) * Complex.I) := by
  have h1 := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := 1 + (y : ℂ) * Complex.I) (by norm_num)
  have h2 := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (beta : ℂ) + (y : ℂ) * Complex.I) (by simpa using hb)
  unfold pairedEtaPhaseProjectionKernel
  have hc : Integrable (fun t : ℝ ↦ (etaPhaseProjectionCoefficient beta : ℂ) *
      Complex.exp (-((beta : ℂ) + (y : ℂ) * Complex.I) * t)) pairedEtaLogMeasure := h2.const_mul _
  rw [integral_sub h1 hc, integral_const_mul,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num),
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by simpa using hb)]
  rfl

/-- The critical base has at most unit square mass on the actual support. -/
theorem integral_etaPhaseProjectionBase_sq_le_one :
    (∫ t : ℝ, Real.exp (-(1 / 2) * t) ^ 2 ∂pairedEtaLogMeasure) ≤ 1 := by
  have he : (fun t : ℝ ↦ Real.exp (-(1 / 2) * t) ^ 2) = fun t ↦ Real.exp (-t) := by
    funext t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have h := integral_mono_measure pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
    (Eventually.of_forall (fun t : ℝ ↦ (Real.exp_pos (-t)).le)) hi
  apply h.trans_eq
  simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0

/-- The original complex projection has the exact boundary-ratio norm budget on the whole actual eta measure. -/
theorem norm_integral_pairedEtaPhaseProjectionKernel_le {beta : ℝ}
    (hb : 1 / 2 < beta) (hb1 : beta < 1) (y : ℝ) :
    ‖∫ t : ℝ, pairedEtaPhaseProjectionKernel beta y t ∂pairedEtaLogMeasure‖ ≤ (1 - beta) / beta := by
  have hf : MemLp (fun t : ℝ ↦ Real.exp (-(1 / 2) * t)) (ENNReal.ofReal (2 : ℝ)) pairedEtaLogMeasure := by
    simpa using memLp_etaPhaseProjectionBase
  have hg : MemLp (etaPhaseProjectionResidual beta) (ENNReal.ofReal (2 : ℝ)) pairedEtaLogMeasure := by
    simpa using memLp_etaPhaseProjectionResidual hb
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : (1 : ℝ) < 2), (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)⟩)
    hf hg
  have hcs : (∫ t : ℝ, ‖Real.exp (-(1 / 2) * t)‖ * ‖etaPhaseProjectionResidual beta t‖ ∂pairedEtaLogMeasure) ≤
      Real.sqrt (∫ t : ℝ, Real.exp (-(1 / 2) * t) ^ 2 ∂pairedEtaLogMeasure) *
        Real.sqrt (∫ t : ℝ, etaPhaseProjectionResidual beta t ^ 2 ∂pairedEtaLogMeasure) := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow] using hholder
  have hbase : Real.sqrt (∫ t : ℝ, Real.exp (-(1 / 2) * t) ^ 2 ∂pairedEtaLogMeasure) ≤ 1 :=
    Real.sqrt_le_one.mpr integral_etaPhaseProjectionBase_sq_le_one
  have hres : Real.sqrt (∫ t : ℝ, etaPhaseProjectionResidual beta t ^ 2 ∂pairedEtaLogMeasure) ≤
      (1 - beta) / beta := by
    apply (Real.sqrt_le_sqrt (integral_etaPhaseProjectionResidual_sq_le hb)).trans_eq
    exact Real.sqrt_sq (by positivity [show 0 < beta by linarith])
  calc
    _ ≤ ∫ t : ℝ, ‖pairedEtaPhaseProjectionKernel beta y t‖ ∂pairedEtaLogMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖Real.exp (-(1 / 2) * t)‖ * ‖etaPhaseProjectionResidual beta t‖ ∂pairedEtaLogMeasure := by
      simp_rw [norm_pairedEtaPhaseProjectionKernel]
    _ ≤ _ := (hcs.trans (mul_le_mul hbase hres (Real.sqrt_nonneg _) (by norm_num))).trans_eq (one_mul _)

/-- Every actual right-half zero bounds the boundary eta value at its own ordinate by its horizontal boundary-distance ratio. -/
theorem norm_pairedEtaPhaseBoundaryValue_le_zero_ratio (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ‖pairedEtaPhaseBoundaryValue rho.1.im‖ ≤ (1 - rho.1.re) / rho.1.re := by
  have h := norm_integral_pairedEtaPhaseProjectionKernel_le hrho (NontrivialZetaZero.re_lt_one rho) rho.1.im
  rw [integral_pairedEtaPhaseProjectionKernel (NontrivialZetaZero.zero_lt_re rho),
    Complex.re_add_im, pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho, mul_zero, sub_zero] at h
  exact h

end

end RiemannGaussian
