/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianPolynomialTransport
import RiemannGaussian.ZetaPrimeKernelLaplace
import RiemannGaussian.AnalyticDoublePoleMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exact selected simple-pole moment under Gaussian smoothing

The factorial Laplace representation retains the entire complex vertical
phase. Its Gaussian average is a positive gamma-weighted damping integral.
This identifies the scale at which growing pole moments survive smoothing,
before the analytic remainder of the actual cleared prime response is
estimated. It is not an independent signed bound for that prime response.
-/

namespace RiemannGaussian.GaussianSimplePoleHeat
noncomputable section
open Complex Filter MeasureTheory Set Topology
open GaussianPolynomialTransport

/-- The factorial Laplace monomial with its full complex damping. -/
def laplace (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-z * t)

/-- Vertical damping changes only the phase of a factorial Laplace atom. -/
theorem norm_laplace (n : ℕ) (z : ℂ) (t : ℝ) :
    ‖laplace n z t‖ = ‖laplace n (z.re : ℂ) t‖ := by
  simp only [laplace, norm_mul, Complex.norm_exp]
  congr 2
  simp

/-- Every complex factorial Laplace monomial is integrable on the
positive half-line at positive real damping. -/
theorem integrableOn_laplace (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (laplace n z) (Ioi 0) := by
  apply (integrableOn_factorial_monomial_exp n hz).norm.mono' (by unfold laplace; fun_prop)
  filter_upwards with t
  exact (norm_laplace n z t).le

/-- The full factorial Laplace atom vanishes at the upper endpoint,
including its complex phase. -/
theorem tendsto_laplace (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (laplace n z) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) z.re hz).div_const
    (n.factorial : ℝ)
  simp only [Real.rpow_natCast, zero_div] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [laplace, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, Complex.norm_natCast, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact le_of_eq (by ring)

/-- A derivative of the next factorial Laplace monomial retains both
adjacent orders and the full complex damping. -/
theorem hasDerivAt_laplace_succ (n : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (laplace (n + 1) z) (laplace n z t - z * laplace (n + 1) z t) t := by
  have hid := (hasDerivAt_id t).ofReal_comp
  have h := ((hid.pow (n + 1)).div_const ((n + 1).factorial : ℂ)).mul
    ((hid.const_mul (-z)).cexp)
  apply h.congr_deriv
  dsimp only [laplace, id_eq, Pi.pow_apply]
  simp only [Nat.add_sub_cancel, Complex.ofReal_one, mul_one, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- Exact complex Laplace evaluation for every factorial order. The
boundary limit and integration by parts are discharged before division. -/
theorem integral_laplace (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, laplace n z t) = z⁻¹ ^ (n + 1) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  induction n with
  | zero =>
    simpa [laplace] using integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
  | succ n ih =>
    have hi := (integrableOn_laplace n hz).sub ((integrableOn_laplace (n + 1) hz).const_mul z)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun t _ ↦ hasDerivAt_laplace_succ n z t) hi (tendsto_laplace (n + 1) hz)
    rw [integral_sub (integrableOn_laplace n hz) ((integrableOn_laplace (n + 1) hz).const_mul z),
      integral_const_mul, ih] at h
    simp only [laplace, Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero n), zero_div, zero_mul,
      sub_zero] at h
    apply (mul_left_cancel₀ hz0)
    rw [pow_succ, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ hz0, one_mul]
    exact (sub_eq_zero.mp h).symm

/-- The positive gamma density at the actual pole distance. Its total
mass and second moment are evaluated below, with the factorial retained. -/
def gammaWeight (n : ℕ) (u t : ℝ) : ℝ :=
  u ^ (n + 1) * (t ^ n / (n.factorial : ℝ)) * Real.exp (-u * t)

/-- The real gamma weight is the normalized original complex Laplace
monomial on the real axis. -/
theorem ofReal_gammaWeight (n : ℕ) (u t : ℝ) :
    (gammaWeight n u t : ℂ) = (u : ℂ) ^ (n + 1) * laplace n (u : ℂ) t := by
  simp only [gammaWeight, laplace, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_exp, Complex.ofReal_neg, mul_assoc]

/-- The complete gamma density is integrable at every positive pole distance. -/
theorem integrableOn_gammaWeight (n : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (gammaWeight n u) (Ioi 0) volume := by
  change Integrable (fun t ↦ gammaWeight n u t) (volume.restrict (Ioi 0))
  have hi := ((integrableOn_laplace n (z := (u : ℂ)) (by simpa using hu)).const_mul
    ((u : ℂ) ^ (n + 1))).re
  simpa only [← ofReal_gammaWeight, RCLike.re_to_complex, Complex.ofReal_re] using hi

/-- Every positive-half-line gamma weight is nonnegative. -/
theorem gammaWeight_nonneg (n : ℕ) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    0 ≤ gammaWeight n u t := by unfold gammaWeight; positivity

/-- The normalized gamma density has exact unit mass. -/
theorem integral_gammaWeight (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, gammaWeight n u t) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_one, ← integral_complex_ofReal]
  simp_rw [ofReal_gammaWeight]
  rw [integral_const_mul, integral_laplace n (by simpa using hu), ← mul_pow,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu.ne'), one_pow]

/-- The exact second moment coefficient governing Gaussian attenuation. -/
def secondMoment (n : ℕ) (u : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) / u ^ 2

/-- Multiplication by the physical squared variable keeps exactly two
additional factorial orders and the pole-distance normalization. -/
theorem gammaWeight_mul_sq (n : ℕ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    gammaWeight n u t * t ^ 2 = secondMoment n u * gammaWeight (n + 2) u t := by
  simp only [gammaWeight, secondMoment, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

/-- The entire squared-variable gamma moment is genuinely integrable. -/
theorem integrableOn_gammaWeight_mul_sq (n : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t ↦ gammaWeight n u t * t ^ 2) (Ioi 0) := by
  simp_rw [gammaWeight_mul_sq n hu]
  exact (integrableOn_gammaWeight (n + 2) hu).const_mul _

/-- The exact quadratic moment, with no loss in its growing-order factor. -/
theorem integral_gammaWeight_mul_sq (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, gammaWeight n u t * t ^ 2) = secondMoment n u := by
  simp_rw [gammaWeight_mul_sq n hu]
  rw [integral_const_mul, integral_gammaWeight (n + 2) hu, mul_one]

/-- The exact damping of the selected pole after its vertical Gaussian
average, expressed as one positive integral rather than a phasewise bound. -/
def attenuation (n : ℕ) (u B : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, gammaWeight n u t * Real.exp (-B * t ^ 2)

/-- Gaussian damping preserves gamma integrability for every nonnegative width. -/
theorem integrableOn_dampedGamma (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 ≤ B) :
    IntegrableOn (fun t ↦ gammaWeight n u t * Real.exp (-B * t ^ 2)) (Ioi 0) := by
  apply (integrableOn_gammaWeight n hu).mono' (by unfold gammaWeight; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (gammaWeight_nonneg n hu.le ht.le) (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right (gammaWeight_nonneg n hu.le ht.le)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))

/-- Positivity is obtained after the exact phase-coupled integral, not by
asserting positivity of each complex pole value. -/
theorem attenuation_nonneg (n : ℕ) {u B : ℝ} (hu : 0 ≤ u) : 0 ≤ attenuation n u B := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (gammaWeight_nonneg n hu ht.le) (Real.exp_pos _).le

/-- The complete averaged pole is at most its original unit source. -/
theorem attenuation_le_one (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 ≤ B) :
    attenuation n u B ≤ 1 := by
  rw [← integral_gammaWeight n hu]
  apply integral_mono_ae (integrableOn_dampedGamma n hu hB) (integrableOn_gammaWeight n hu)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_of_le_one_right (gammaWeight_nonneg n hu.le ht.le)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))

/-- The exact exponential tangent bounds the loss of the whole pole
source by B times its evaluated second gamma moment. -/
theorem one_sub_secondMoment_le_attenuation (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 ≤ B) :
    1 - B * secondMoment n u ≤ attenuation n u B := by
  have hi := (integrableOn_gammaWeight n hu).sub
    ((integrableOn_gammaWeight_mul_sq n hu).const_mul B)
  have h := integral_mono_ae hi (integrableOn_dampedGamma n hu hB) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (B * t ^ 2))
      (gammaWeight_nonneg n hu.le ht.le)
    change gammaWeight n u t - B * (gammaWeight n u t * t ^ 2) ≤ _
    calc
      _ = gammaWeight n u t * (1 - B * t ^ 2) := by ring
      _ ≤ _ := by simpa only [neg_mul] using he)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrableOn_gammaWeight n hu) ((integrableOn_gammaWeight_mul_sq n hu).const_mul B),
    integral_const_mul, integral_gammaWeight n hu, integral_gammaWeight_mul_sq n hu] at h
  exact h

private def joint (n : ℕ) (u B : ℝ) (p : ℝ × ℝ) : ℂ :=
  (Real.exp (-(1 / (4 * B)) * p.1 ^ 2) : ℂ) * laplace n (u : ℂ) p.2 *
    Complex.exp (I * (p.1 : ℂ) * (p.2 : ℂ))

private theorem integrable_joint (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    Integrable (joint n u B) (volume.prod (volume.restrict (Ioi 0))) := by
  have hg := integrable_real_pow_gaussian hB 0
  simp only [pow_zero, one_mul] at hg
  have hp := hg.norm.mul_prod (integrableOn_laplace n (z := (u : ℂ)) (by simpa using hu)).norm
  apply hp.mono' (by unfold joint laplace; fun_prop)
  filter_upwards with p
  simp [joint, Complex.norm_exp, pow_two, Complex.mul_re]

private theorem laplace_shift (n : ℕ) (u y t : ℝ) :
    laplace n ((u : ℂ) - I * y) t =
      laplace n (u : ℂ) t * Complex.exp (I * (y : ℂ) * (t : ℂ)) := by
  unfold laplace
  rw [show -((u : ℂ) - I * y) * t = -(u : ℂ) * t + I * y * t by ring, Complex.exp_add]
  ring

private theorem integral_joint_time (n : ℕ) {u : ℝ} (hu : 0 < u) (B y : ℝ) :
    (∫ t : ℝ in Ioi 0, joint n u B (y, t)) =
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * (((u : ℂ) - I * y)⁻¹) ^ (n + 1) := by
  have he (t : ℝ) : joint n u B (y, t) =
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * laplace n ((u : ℂ) - I * y) t := by
    rw [laplace_shift]
    unfold joint
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_laplace n (by simpa using hu)]

private theorem integral_joint_frequency (n : ℕ) (u : ℝ) {B : ℝ} (hB : 0 < B) (t : ℝ) :
    (∫ y : ℝ, joint n u B (y, t)) =
      (mass B : ℂ) * (laplace n (u : ℂ) t * (Real.exp (-B * t ^ 2) : ℂ)) := by
  have he (y : ℝ) : joint n u B (y, t) = laplace n (u : ℂ) t * atom B t y := by
    rw [atom_eq_gaussian_phase]
    unfold joint
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_atom hB]
  ring

/-- The actual vertical average of every selected simple-pole moment is
integrable. This follows from the complete phase-retaining product integral. -/
theorem integrable_poleMoment (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    Integrable (fun y : ℝ ↦ (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      (((u : ℂ) - I * y)⁻¹) ^ (n + 1)) := by
  have h := (integrable_joint n hu hB).integral_prod_left
  simpa only [integral_joint_time n hu] using h

/-- The exact normalized Gaussian average of the pole source. The full
complex phase is present before its integral is evaluated. -/
def poleHeat (n : ℕ) (u B : ℝ) : ℂ :=
  (u : ℂ) ^ (n + 1) / (mass B : ℂ) *
    ∫ y : ℝ, (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      (((u : ℂ) - I * y)⁻¹) ^ (n + 1)

/-- The entire complex pole average equals the positive gamma damping
integral exactly. Product integrability pays for the full interchange. -/
theorem poleHeat_eq_attenuation (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    poleHeat n u B = (attenuation n u B : ℂ) := by
  have hi := integral_integral_swap (f := fun y t ↦ joint n u B (y, t)) (integrable_joint n hu hB)
  simp only [integral_joint_time n hu, integral_joint_frequency n u hB] at hi
  rw [integral_const_mul] at hi
  rw [poleHeat, hi]
  have hm : (mass B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mass_pos hB).ne'
  rw [← mul_assoc, div_mul_cancel₀ _ hm, ← integral_const_mul]
  rw [attenuation, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.ofReal_mul, ofReal_gammaWeight]
  ring

/-- Centering the exponential tangent at the exact second moment gives
a strictly positive lower bound at every finite width and order. -/
theorem exp_neg_secondMoment_le_attenuation (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 ≤ B) :
    Real.exp (-B * secondMoment n u) ≤ attenuation n u B := by
  let e := Real.exp (-B * secondMoment n u)
  have hi := ((integrableOn_gammaWeight n hu).const_mul (e * (1 + B * secondMoment n u))).sub
    ((integrableOn_gammaWeight_mul_sq n hu).const_mul (e * B))
  have h := integral_mono_ae hi (integrableOn_dampedGamma n hu hB) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change e * (1 + B * secondMoment n u) * gammaWeight n u t -
      e * B * (gammaWeight n u t * t ^ 2) ≤ _
    have hex := Real.add_one_le_exp (B * (secondMoment n u - t ^ 2))
    have hg := gammaWeight_nonneg n hu.le ht.le
    calc
      _ = gammaWeight n u t * (e * (B * (secondMoment n u - t ^ 2) + 1)) := by ring
      _ ≤ gammaWeight n u t * (e * Real.exp (B * (secondMoment n u - t ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hex (Real.exp_pos _).le) hg
      _ = gammaWeight n u t * Real.exp (-B * t ^ 2) := by
        dsimp only [e]
        rw [← Real.exp_add]
        congr 2
        ring)
  simp only [Pi.sub_apply] at h
  rw [integral_sub ((integrableOn_gammaWeight n hu).const_mul (e * (1 + B * secondMoment n u)))
      ((integrableOn_gammaWeight_mul_sq n hu).const_mul (e * B)),
    integral_const_mul, integral_const_mul, integral_gammaWeight n hu,
    integral_gammaWeight_mul_sq n hu] at h
  convert! h using 1
  dsimp [e]
  ring

/-- The selected Gaussian pole factor is real: all imaginary phases
cancel in its complete average. -/
theorem poleHeat_im (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    (poleHeat n u B).im = 0 := by rw [poleHeat_eq_attenuation n hu hB]; rfl

/-- The full real pole factor has a positive explicit lower bound at
every positive width, with its growing-order dependence retained. -/
theorem poleHeat_re_bounds (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    Real.exp (-B * secondMoment n u) ≤ (poleHeat n u B).re ∧ (poleHeat n u B).re ≤ 1 := by
  rw [poleHeat_eq_attenuation n hu hB, Complex.ofReal_re]
  exact ⟨exp_neg_secondMoment_le_attenuation n hu hB.le, attenuation_le_one n hu hB.le⟩

/-- A quantitative bound for the loss of the exact complex source,
uniform in both moment order and Gaussian width. -/
theorem norm_poleHeat_sub_one_le (n : ℕ) {u B : ℝ} (hu : 0 < u) (hB : 0 < B) :
    ‖poleHeat n u B - 1‖ ≤ B * secondMoment n u := by
  rw [poleHeat_eq_attenuation n hu hB, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (attenuation_le_one n hu hB.le))]
  linarith [one_sub_secondMoment_le_attenuation n hu hB.le]

/-- The mathematically defined quadratic width schedule is normalized by
the actual pole distance and both adjacent factorial orders. -/
def quadraticWidth (c u : ℝ) (n : ℕ) : ℝ :=
  c * u ^ 2 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))

/-- Every positive relative width gives a genuine positive Gaussian. -/
theorem quadraticWidth_pos {c u : ℝ} (hc : 0 < c) (hu : 0 < u) (n : ℕ) :
    0 < quadraticWidth c u n := by unfold quadraticWidth; positivity

/-- The quadratic schedule keeps the full source-loss budget exactly
equal to its relative width at every moment order. -/
theorem quadraticWidth_mul_secondMoment (c : ℝ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    quadraticWidth c u n * secondMoment n u = c := by
  unfold quadraticWidth secondMoment
  field_simp

/-- Every positive relative width retains at least exp(-c) of the pole
source uniformly over all orders; it is unnecessary to send c to zero
merely to retain a nonzero source. -/
theorem poleHeat_quadraticWidth_bounds {c u : ℝ} (hc : 0 < c) (hu : 0 < u) (n : ℕ) :
    Real.exp (-c) ≤ (poleHeat n u (quadraticWidth c u n)).re ∧
      (poleHeat n u (quadraticWidth c u n)).re ≤ 1 := by
  have h := poleHeat_re_bounds n hu (quadraticWidth_pos hc hu n)
  simpa only [neg_mul, quadraticWidth_mul_secondMoment c hu] using h

/-- An explicit all-order source-error budget on the same quadratic
width family, retaining the entire complex pole average. -/
theorem norm_poleHeat_quadraticWidth_sub_one_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) (n : ℕ) :
    ‖poleHeat n u (quadraticWidth c u n) - 1‖ ≤ c := by
  have h := norm_poleHeat_sub_one_le n hu (quadraticWidth_pos hc hu n)
  simpa only [quadraticWidth_mul_secondMoment c hu] using h

/-- Every vanishing relative-width family preserves the complete unit
source while the factorial order grows, with the preceding quantitative
error budget and no unevaluated diagonal choice. -/
theorem tendsto_poleHeat_quadraticWidth {u : ℝ} (hu : 0 < u) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) (hlim : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n ↦ poleHeat n u (quadraticWidth (c n) u n)) atTop (𝓝 1) := by
  have h := squeeze_zero_norm (fun n ↦ norm_poleHeat_quadraticWidth_sub_one_le (hc n) hu n) hlim
  simpa only [sub_add_cancel, zero_add] using h.add_const (1 : ℂ)

/-- The original signed factorial derivative of a simple principal part,
at any vertically shifted Euler center, is exactly the pole kernel used
above. The complex residue is retained as a multiplier. -/
theorem signedTaylorMoment_principalPart (n : ℕ) (a L : ℂ) (u y : ℝ) :
    signedTaylorMoment n (fun z ↦ L / (z - a)) (a + u - I * y) =
      L * (((u : ℂ) - I * y)⁻¹) ^ (n + 1) := by
  simp_rw [div_eq_mul_inv]
  rw [signedTaylorMoment_const_mul, signedTaylorMoment_inv_sub]
  congr 3
  ring

end
end RiemannGaussian.GaussianSimplePoleHeat
