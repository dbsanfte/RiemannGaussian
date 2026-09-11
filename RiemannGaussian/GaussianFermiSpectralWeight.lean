/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPairDecay
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exact positive spectral weight of the centered Fermi signal

Centering the Gaussian Fermi pair at `a/2` gives a real nonnegative Fourier
transform. The original derivative estimate makes that transform
integrable. Fourier inversion identifies its exact normalization and
retains its characteristic function for transporting the Gaussian explicit
formula to the Fermi product.
-/

namespace RiemannGaussian.GaussianFermiSpectralWeight

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology FourierTransform
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiDerivativeBounds
open GaussianFermiPairDecay

/-- The centered original time signal. -/
def signal (a b t : ℝ) : ℝ := damped a b (a / 2) t

/-- Its full complex angular-frequency transform, retained before taking
its real part. -/
def kernel (a b y : ℝ) : ℂ := oscillatory (signal a b) y

/-- The normalized real spectral weight. -/
def density (a b y : ℝ) : ℝ := (kernel a b y).re / Real.pi

/-- Centering does not change the literal endpoint value. -/
theorem signal_zero (a b : ℝ) : signal a b 0 = 1 / 2 := by
  norm_num [signal, damped, EtaGammaSmoothing.fermi]

/-- The exact centered signal is continuous. -/
theorem continuous_signal (a b : ℝ) : Continuous (signal a b) := by
  have hf := EtaGammaSmoothing.continuous_fermi
  unfold signal damped
  fun_prop

/-- All integrability hypotheses follow from the existing actual-signal
derivative bound at the center of the reflection strip. -/
theorem integrable_signal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Integrable (signal a b) := by
  exact (integrable_damped_orders ha hb (δ := 0) le_rfl (by simpa using hb.le)
    (x := a / 2) (by linarith) (by linarith)).1

/-- The retained Fourier kernel is exactly the centered analytic pair. -/
theorem kernel_eq_pair {b : ℝ} (hb : 0 < b) (a y : ℝ) :
    kernel a b y =
      transform a (window b) ((a / 2 : ℝ) + (y : ℂ) * I) +
      transform a (window b) ((a : ℂ) - ((a / 2 : ℝ) + (y : ℂ) * I)) := by
  rw [pair_eq_oscillatory hb]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

/-- The centered analytic partners are conjugates, so the full complex
kernel is real without discarding an imaginary channel. -/
theorem kernel_im {b : ℝ} (hb : 0 < b) (a y : ℝ) : (kernel a b y).im = 0 := by
  rw [kernel_eq_pair hb]
  have he : (a : ℂ) - ((a / 2 : ℝ) + (y : ℂ) * I) =
      starRingEnd ℂ ((a / 2 : ℝ) + (y : ℂ) * I) := by
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
    apply Complex.ext <;> norm_num [htwo]
    ring
  rw [he, transform_conj]
  simp

/-- The spectral kernel is nonnegative at every frequency by the proved
reflection-strip positivity theorem. -/
theorem density_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    0 ≤ density a b y := by
  have hp := reflected_pair_re_nonneg ha hb
    (z := ((a / 2 : ℝ) + (y : ℂ) * I)) (by simp; linarith) (by simp; linarith)
  rw [physical_pair_re_eq, ← kernel_eq_pair hb] at hp
  exact div_nonneg hp Real.pi_pos.le

/-- Continuity of the entire paired transform gives continuity of the
original Fourier kernel. -/
theorem continuous_kernel {b : ℝ} (hb : 0 < b) (a : ℝ) : Continuous (kernel a b) := by
  have ht : Continuous (transform a (window b)) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_gaussian_transform hb a z).continuousAt
  have hc : Continuous (fun y : ℝ =>
      transform a (window b) ((a / 2 : ℝ) + (y : ℂ) * I) +
      transform a (window b) ((a : ℂ) - ((a / 2 : ℝ) + (y : ℂ) * I))) := by fun_prop
  exact hc.congr fun y => (kernel_eq_pair hb a y).symm

/-- One finite constant bounds the exact kernel by the integrable
inverse-square majorant, including zero frequency. -/
theorem exists_kernel_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖kernel a b y‖ ≤ C / (1 + y ^ 2) := by
  let M := ∫ t : ℝ, |signal a b t|
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hC := integralCost_pos hb a 0
  refine ⟨M + integralCost a b 0, by positivity, ?_⟩
  intro y
  have h0 : ‖kernel a b y‖ ≤ M := norm_oscillatory_le (integrable_signal ha hb) y
  have h2 := im_sq_mul_norm_pair_le ha hb (δ := 0) le_rfl (by simpa using hb.le)
    (z := ((a / 2 : ℝ) + (y : ℂ) * I)) (by simp; linarith) (by simp; linarith)
  rw [← kernel_eq_pair hb] at h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at h2
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

/-- The genuine complex spectral weight is absolutely integrable. -/
theorem integrable_kernel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Integrable (kernel a b) := by
  obtain ⟨C, hC, hbound⟩ := exists_kernel_bound ha hb
  apply (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_kernel hb a).aestronglyMeasurable
  exact Eventually.of_forall fun y => by simpa only [div_eq_mul_inv] using hbound y

/-- The real averaging weight is absolutely integrable. -/
theorem integrable_density {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Integrable (density a b) := (integrable_kernel ha hb).re.div_const Real.pi

/-- The real density retains the same inverse-square spectral control. -/
theorem exists_density_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, |density a b y| ≤ C / (1 + y ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_kernel_bound ha hb
  refine ⟨C / Real.pi, by positivity, ?_⟩
  intro y
  unfold density
  rw [abs_div, abs_of_pos Real.pi_pos]
  calc
    _ ≤ ‖kernel a b y‖ / Real.pi := by gcongr; exact Complex.abs_re_le_norm _
    _ ≤ (C / (1 + y ^ 2)) / Real.pi := by gcongr; exact hbound y
    _ = _ := by ring

/-- The real averaging density is continuous. -/
theorem continuous_density {b : ℝ} (hb : 0 < b) (a : ℝ) : Continuous (density a b) :=
  (Complex.continuous_re.comp (continuous_kernel hb a)).div_const Real.pi

/-- The normalized real weight exactly reconstructs the complex kernel. -/
theorem ofReal_density {b : ℝ} (hb : 0 < b) (a y : ℝ) :
    ((Real.pi * density a b y : ℝ) : ℂ) = kernel a b y := by
  have he : ((kernel a b y).re : ℂ) = kernel a b y := by
    apply Complex.ext <;> simp [kernel_im hb]
  rw [density, mul_div_cancel₀ _ Real.pi_ne_zero]
  exact he

/-- The angular-frequency kernel agrees with Mathlib's Fourier transform
after the exact `2*pi` change of frequency. -/
theorem fourier_signal_eq_kernel (a b y : ℝ) :
    𝓕 (fun t : ℝ => (signal a b t : ℂ)) (y / (2 * Real.pi)) = kernel a b y := by
  rw [Real.fourier_eq']
  unfold kernel oscillatory
  apply integral_congr_ae
  filter_upwards with t
  simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul]
  rw [smul_eq_mul, mul_comm]
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Absolute integrability in Mathlib's cyclic-frequency convention. -/
theorem integrable_fourier_signal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Integrable (𝓕 (fun t : ℝ => (signal a b t : ℂ))) := by
  have hs := (integrable_kernel ha hb).comp_mul_left'
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  apply hs.congr
  filter_upwards with y
  have hf := fourier_signal_eq_kernel a b (2 * Real.pi * y)
  convert hf.symm using 1
  field_simp [Real.pi_ne_zero]

/-- Exact angular-frequency Fourier inversion, with the endpoint and
normalization retained. Both original integrability hypotheses are proved. -/
theorem integral_kernel_mul_cexp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (t : ℝ) :
    (∫ y : ℝ, kernel a b y * Complex.exp (I * (y : ℂ) * (t : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) * (signal a b t : ℂ) := by
  have hinv := (integrable_signal ha hb).ofReal.fourierInv_fourier_eq
    (v := t) (integrable_fourier_signal ha hb)
    ((Complex.continuous_ofReal.comp (continuous_signal a b)).continuousAt)
  rw [Real.fourierInv_eq'] at hinv
  let G : ℝ → ℂ := fun y => kernel a b y * Complex.exp (I * (y : ℂ) * (t : ℂ))
  have hinvG : (∫ u : ℝ, G (2 * Real.pi * u)) = (signal a b t : ℂ) := by
    rw [← hinv]
    apply integral_congr_ae
    filter_upwards with u
    have hf : 𝓕 (fun x : ℝ => (signal a b x : ℂ)) u =
        kernel a b (2 * Real.pi * u) := by
      convert fourier_signal_eq_kernel a b (2 * Real.pi * u) using 1
      field_simp [Real.pi_ne_zero]
    dsimp only [G]
    rw [hf, smul_eq_mul]
    conv_rhs => rw [mul_comm]
    congr 1
    congr 1
    simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul]
    push_cast
    ring
  have hs : (∫ u : ℝ, G (2 * Real.pi * u)) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ y : ℝ, G y) := by
    calc
      _ = |(2 * Real.pi)⁻¹| • (∫ y : ℝ, G y) := Measure.integral_comp_mul_left G _
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
        rfl
  change (∫ y : ℝ, G y) = _
  calc
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ y : ℝ, G y)) := by
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = ((2 * Real.pi : ℝ) : ℂ) * (∫ u : ℝ, G (2 * Real.pi * u)) := by rw [hs]
    _ = _ := by rw [hinvG]

/-- The exact characteristic function of the normalized spectral weight
is twice the original centered Fermi signal. -/
theorem integral_density_mul_cexp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (t : ℝ) :
    (∫ y : ℝ, (density a b y : ℂ) * Complex.exp (I * (y : ℂ) * (t : ℂ))) =
      2 * (signal a b t : ℂ) := by
  have hk := integral_kernel_mul_cexp ha hb t
  have he : (∫ y : ℝ, kernel a b y * Complex.exp (I * (y : ℂ) * (t : ℂ))) =
      (Real.pi : ℂ) *
        (∫ y : ℝ, (density a b y : ℂ) * Complex.exp (I * (y : ℂ) * (t : ℂ))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [← ofReal_density hb a y, Complex.ofReal_mul]
    ring
  rw [he] at hk
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    _ = _ := hk
    _ = _ := by push_cast; ring

/-- The averaging weight has exactly unit mass; combined with
`density_nonneg`, it is a genuine probability density. -/
theorem integral_density {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (∫ y : ℝ, density a b y) = 1 := by
  have h := integral_density_mul_cexp ha hb 0
  norm_num [signal_zero] at h
  have hi : Integrable (fun y : ℝ => (density a b y : ℂ)) :=
    (integrable_density ha hb).ofReal
  have hr : (∫ y : ℝ, (density a b y : ℂ).re) =
      (∫ y : ℝ, (density a b y : ℂ)).re := integral_re hi
  calc
    _ = (∫ y : ℝ, (density a b y : ℂ)).re := by
      simpa only [Complex.ofReal_re] using hr
    _ = 1 := by rw [h]; rfl

end
end RiemannGaussian.GaussianFermiSpectralWeight
