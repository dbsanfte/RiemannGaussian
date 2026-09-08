import RiemannGaussian.EtaMoebiusSelectedFamily
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# Positive gamma kernel and cubic eta cancellation

The exact third derivative of the Fermi kernel has a global exponential
envelope. A positive gamma survival transform cancels the first two
Taylor corrections. Its full signed remainder has a cubic bound. The
physical density is nonnegative, integrable, and has total mass one.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

/-- The real Fermi kernel used in the Mellin representation of the eta function. -/
def fermi (t : ℝ) : ℝ := (1 + Real.exp t)⁻¹

/-- The exact first derivative written as a polynomial in the Fermi value. -/
def fermiOne (t : ℝ) : ℝ := fermi t * (fermi t - 1)

/-- The exact second derivative written as a polynomial in the Fermi value. -/
def fermiTwo (t : ℝ) : ℝ := fermi t * (fermi t - 1) * (2 * fermi t - 1)

/-- The exact third derivative written as a polynomial in the Fermi value. -/
def fermiThree (t : ℝ) : ℝ := fermi t * (fermi t - 1) * (6 * (fermi t) ^ 2 - 6 * fermi t + 1)

/-- The Fermi value is strictly between zero and one at every real input. -/
theorem fermi_bounds (t : ℝ) : 0 < fermi t ∧ fermi t < 1 := by
  have he := Real.exp_pos t
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact inv_lt_one_of_one_lt₀ (by linarith)

/-- The Fermi kernel is bounded by the corresponding exponential on the entire real line. -/
theorem fermi_le_exp_neg (t : ℝ) : fermi t ≤ Real.exp (-t) := by
  rw [fermi, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos t)
    (by linarith : Real.exp t ≤ 1 + Real.exp t)

/-- The first Fermi derivative has no exceptional denominator. -/
theorem hasDerivAt_fermi (t : ℝ) : HasDerivAt fermi (fermiOne t) t := by
  have hne : 1 + Real.exp t ≠ 0 := by positivity
  convert! ((Real.hasDerivAt_exp t).const_add 1).inv hne using 1
  dsimp only [fermiOne, fermi]
  field_simp
  ring

/-- Differentiating the polynomial first derivative gives the exact second derivative. -/
theorem hasDerivAt_fermiOne (t : ℝ) : HasDerivAt fermiOne (fermiTwo t) t := by
  convert! (hasDerivAt_fermi t).mul ((hasDerivAt_fermi t).sub_const 1) using 1
  dsimp only [fermiOne, fermiTwo]
  ring

/-- Differentiating the polynomial second derivative gives the exact third derivative. -/
theorem hasDerivAt_fermiTwo (t : ℝ) : HasDerivAt fermiTwo (fermiThree t) t := by
  convert! ((hasDerivAt_fermi t).mul ((hasDerivAt_fermi t).sub_const 1)).mul
    (((hasDerivAt_fermi t).const_mul 2).sub_const 1) using 1
  dsimp only [fermiOne, fermiTwo, fermiThree, Pi.mul_apply, Pi.sub_apply]
  ring

/-- The real Fermi kernel is continuous everywhere. -/
theorem continuous_fermi : Continuous fermi :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_fermi t).continuousAt

/-- The third Fermi derivative is continuous everywhere. -/
theorem continuous_fermiThree : Continuous fermiThree := by
  unfold fermiThree
  exact (continuous_fermi.mul (continuous_fermi.sub continuous_const)).mul
    (((continuous_const.mul (continuous_fermi.pow 2)).sub
      (continuous_const.mul continuous_fermi)).add continuous_const)

/-- The exact third derivative has the global envelope `exp(-t)`. -/
theorem abs_fermiThree_le (t : ℝ) : |fermiThree t| ≤ Real.exp (-t) := by
  obtain ⟨hf0, hf1⟩ := fermi_bounds t
  have hp : |6 * (fermi t) ^ 2 - 6 * fermi t + 1| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (2 * fermi t - 1)]
    · nlinarith [mul_nonneg hf0.le (sub_nonneg.mpr hf1.le)]
  rw [fermiThree, abs_mul, abs_mul, abs_of_pos hf0,
    abs_of_neg (sub_neg.mpr hf1)]
  calc
    _ ≤ fermi t * -(fermi t - 1) * 1 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hf0.le (by linarith))
    _ ≤ fermi t := by nlinarith [sq_nonneg (fermi t)]
    _ ≤ _ := fermi_le_exp_neg t

/-- The positive gamma survival transform cancels the first two Taylor corrections. -/
def gammaTransform (t x : ℝ) : ℝ :=
  fermi (t + x) - x * fermiOne (t + x) + x ^ 2 / 2 * fermiTwo (t + x)

/-- Differentiation exposes the cubic remainder through one exact second-order factor. -/
theorem hasDerivAt_gammaTransform (t x : ℝ) :
    HasDerivAt (gammaTransform t) (x ^ 2 / 2 * fermiThree (t + x)) x := by
  have hshift := (hasDerivAt_id x).const_add t
  have h0 := (hasDerivAt_fermi (t + x)).comp x hshift
  have h1 := (hasDerivAt_fermiOne (t + x)).comp x hshift
  have h2 := (hasDerivAt_fermiTwo (t + x)).comp x hshift
  convert! (h0.sub ((hasDerivAt_id x).mul h1)).add
    ((((hasDerivAt_id x).pow 2).div_const 2).mul h2) using 1
  dsimp only [id_eq, Function.comp_def, Pi.pow_apply]
  ring

/-- The full signed kernel correction equals its genuine derivative integral. -/
theorem gammaTransform_sub_eq_integral (t x : ℝ) :
    gammaTransform t x - fermi t =
      ∫ v in (0 : ℝ)..x, v ^ 2 / 2 * fermiThree (t + v) := by
  have hc : Continuous (fun v : ℝ ↦ v ^ 2 / 2 * fermiThree (t + v)) := by
    exact ((continuous_id.pow 2).div_const 2).mul
      (continuous_fermiThree.comp (continuous_const.add continuous_id))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ ↦ hasDerivAt_gammaTransform t v) (hc.intervalIntegrable 0 x)]
  simp [gammaTransform]

/-- The complete Taylor-cancelling kernel has a uniform cubic error with its original exponential weight. -/
theorem abs_gammaTransform_sub_le (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    |gammaTransform t x - fermi t| ≤ x ^ 3 / 6 * Real.exp (-t) := by
  rw [gammaTransform_sub_eq_integral, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ v in (0 : ℝ)..x, v ^ 2 / 2 * Real.exp (-t) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hx
      · exact Eventually.of_forall fun v hv ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ v ^ 2 / 2)]
          apply mul_le_mul_of_nonneg_left ((abs_fermiThree_le (t + v)).trans ?_) (by positivity)
          apply Real.exp_le_exp.mpr
          linarith [hv.1]
      · exact (((continuous_id.pow 2).div_const 2).mul_const (Real.exp (-t))).intervalIntegrable 0 x
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
        integral_pow]
      norm_num
      ring

/-- The normalized positive gamma density on the physical half-line. -/
def gammaDensity (t : ℝ) : ℝ := t ^ 2 * Real.exp (-t) / 2

/-- The positive gamma density has a literal closed survival function. -/
def gammaSurvival (t : ℝ) : ℝ := Real.exp (-t) * (1 + t + t ^ 2 / 2)

/-- The physical gamma density is nonnegative. -/
theorem gammaDensity_nonneg (t : ℝ) : 0 ≤ gammaDensity t := by
  unfold gammaDensity
  positivity

/-- The survival derivative is exactly the negative physical density. -/
theorem hasDerivAt_gammaSurvival (t : ℝ) : HasDerivAt gammaSurvival (-gammaDensity t) t := by
  convert! (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg).mul
    (((hasDerivAt_id t).const_add 1).add (((hasDerivAt_id t).pow 2).div_const 2))) using 1
  dsimp only [gammaDensity, id_eq, Function.comp_def, Pi.pow_apply, Pi.add_apply]
  ring

/-- The positive gamma density is genuinely integrable on the physical half-line. -/
theorem integrableOn_gammaDensity : IntegrableOn gammaDensity (Ioi 0) := by
  have hi := (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3)).div_const 2
  change IntegrableOn (fun t : ℝ ↦ t ^ 2 * Real.exp (-t) / 2) (Ioi 0)
  norm_num only [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast] at hi
  simpa only [IntegrableOn, Real.rpow_two, mul_comm] using hi

/-- The gamma averaging kernel has exactly unit total mass. -/
theorem integral_gammaDensity : (∫ t in Ioi (0 : ℝ), gammaDensity t) = 1 := by
  change (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-t) / 2) = 1
  rw [integral_div]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1)
  norm_num [Real.rpow_natCast, Real.Gamma_add_one, Real.Gamma_one] at h
  rw [h]
  norm_num

end

end RiemannGaussian.EtaGammaSmoothing
