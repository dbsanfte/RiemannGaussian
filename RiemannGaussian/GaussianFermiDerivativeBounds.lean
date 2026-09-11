/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiZeroPair

/-!
# Uniform derivative bounds for the reflected Gaussian Fermi signal

The Fermi factor is retained in both derivative bounds. Its exponential
control on the negative time half-line is essential: discarding it would
introduce an exponential loss in the inverse Gaussian scale. On a strip
enlarged by `delta`, with `delta^2 <= b`, the actual signal and its first
two derivatives have a common Gaussian majorant.
-/

namespace RiemannGaussian.GaussianFermiDerivativeBounds

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open EtaGammaSmoothing FermiLaplaceReflection GaussianFermiZeroPair

/-- The real amplitude of the full coupled transform at abscissa `x`. -/
def damped (a b x t : ℝ) : ℝ := Real.exp (-b * t ^ 2 - x * t) * fermi (-a * t)

/-- The exact first time derivative, with its Fermi factor retained. -/
def dampedOne (a b x t : ℝ) : ℝ :=
  Real.exp (-b * t ^ 2 - x * t) *
    ((-2 * b * t - x) * fermi (-a * t) - a * fermiOne (-a * t))

/-- The exact second time derivative, before any absolute-value bound. -/
def dampedTwo (a b x t : ℝ) : ℝ :=
  Real.exp (-b * t ^ 2 - x * t) *
    (((-2 * b * t - x) ^ 2 - 2 * b) * fermi (-a * t) -
      2 * a * (-2 * b * t - x) * fermiOne (-a * t) + a ^ 2 * fermiTwo (-a * t))

/-- The amplitude is the original Fermi window with its real Laplace factor. -/
theorem damped_eq_weight (a b x t : ℝ) :
    damped a b x t = weight a (window b) t * Real.exp (-x * t) := by
  rw [damped, sub_eq_add_neg, Real.exp_add, weight, window, neg_mul x t]
  ring

/-- The retained first Fermi derivative is bounded by the Fermi value. -/
theorem abs_fermiOne_le_fermi (t : ℝ) : |fermiOne t| ≤ fermi t := by
  obtain ⟨hp, hu⟩ := fermi_bounds t
  rw [fermiOne, abs_mul, abs_of_pos hp, abs_of_nonpos (by linarith : fermi t - 1 ≤ 0)]
  nlinarith

/-- The second Fermi derivative has the same exponential envelope. -/
theorem abs_fermiTwo_le_fermi (t : ℝ) : |fermiTwo t| ≤ fermi t := by
  obtain ⟨hp, hu⟩ := fermi_bounds t
  have hfactor : |2 * fermi t - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  change |fermiOne t * (2 * fermi t - 1)| ≤ _
  rw [abs_mul]
  exact (mul_le_mul (abs_fermiOne_le_fermi t) hfactor (abs_nonneg _) hp.le).trans_eq
    (mul_one _)

private theorem hasDerivAt_exponent (b x t : ℝ) :
    HasDerivAt (fun u : ℝ => -b * u ^ 2 - x * u) (-2 * b * t - x) t := by
  apply ((((hasDerivAt_id t).pow 2).const_mul (-b)).sub
    ((hasDerivAt_id t).const_mul x)).congr_deriv
  dsimp
  ring

/-- Differentiation preserves the complete signed first derivative. -/
theorem hasDerivAt_damped (a b x t : ℝ) :
    HasDerivAt (damped a b x) (dampedOne a b x t) t := by
  have he := (hasDerivAt_exponent b x t).exp
  have hf := (hasDerivAt_fermi (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
  apply (he.mul hf).congr_deriv
  dsimp only [dampedOne, Function.comp_apply]
  ring

/-- The complete second derivative is computed without dropping reflection
or endpoint terms. -/
theorem hasDerivAt_dampedOne (a b x t : ℝ) :
    HasDerivAt (dampedOne a b x) (dampedTwo a b x t) t := by
  have he := (hasDerivAt_exponent b x t).exp
  have hlin := ((hasDerivAt_id t).const_mul (-2 * b)).sub_const x
  have hf := (hasDerivAt_fermi (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
  have hf' := (hasDerivAt_fermiOne (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
  apply (he.mul ((hlin.mul hf).sub (hf'.const_mul a))).congr_deriv
  dsimp only [dampedTwo, Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply]
  ring

/-- The actual full-line signal is strictly positive before oscillation. -/
theorem damped_pos (a b x t : ℝ) : 0 < damped a b x t :=
  mul_pos (Real.exp_pos _) (fermi_bounds _).1

/-- Reflection controls both time directions with only the amount by which
the abscissa leaves the positive strip. -/
theorem damped_le_exp_abs {a b x δ : ℝ} (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) (t : ℝ) :
    damped a b x t ≤ Real.exp (-b * t ^ 2 + δ * |t|) := by
  by_cases ht : 0 ≤ t
  · calc
      _ ≤ Real.exp (-b * t ^ 2 - x * t) * 1 :=
        mul_le_mul_of_nonneg_left (fermi_bounds _).2.le (Real.exp_pos _).le
      _ ≤ _ := by
        rw [mul_one]
        apply Real.exp_le_exp.mpr
        rw [abs_of_nonneg ht]
        nlinarith
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hf : fermi (-a * t) ≤ Real.exp (a * t) := by
      simpa only [neg_mul, neg_neg] using fermi_le_exp_neg (-a * t)
    calc
      _ ≤ Real.exp (-b * t ^ 2 - x * t) * Real.exp (a * t) :=
        mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
      _ = Real.exp (-b * t ^ 2 - x * t + a * t) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [abs_of_nonpos ht']
        nlinarith

/-- The real abscissa remains uniformly bounded on the enlarged strip. -/
theorem abs_abscissa_le {a x δ : ℝ} (ha : 0 ≤ a)
    (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) : |x| ≤ a + δ := by
  rw [abs_le]
  exact ⟨by linarith, hxa⟩

/-- A strip extension no greater than the Gaussian scale costs only
`exp(1/2)`, uniformly on the full real time line. -/
theorem damped_le_gaussian {a b x δ : ℝ} (hb : 0 < b) (hδb : δ ^ 2 ≤ b)
    (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) (t : ℝ) :
    damped a b x t ≤ Real.exp (1 / 2) * Real.exp (-(b / 2) * t ^ 2) := by
  apply (damped_le_exp_abs hx0 hxa t).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := sq_nonneg (b * |t| - δ)
  rw [sub_sq, mul_pow, sq_abs] at hs
  have he : b * (-b * t ^ 2 + δ * |t|) ≤ b * (1 / 2 - b / 2 * t ^ 2) := by
    nlinarith
  have h := (mul_le_mul_iff_right₀ hb).mp he
  linarith

/-- The first derivative keeps the same Fermi exponential envelope. -/
theorem abs_dampedOne_le_coeff (a b x t : ℝ) :
    |dampedOne a b x t| ≤ (|-2 * b * t - x| + |a|) * damped a b x t := by
  have hp := (fermi_bounds (-a * t)).1
  have hinner : |(-2 * b * t - x) * fermi (-a * t) - a * fermiOne (-a * t)| ≤
      (|-2 * b * t - x| + |a|) * fermi (-a * t) := by
    calc
      _ ≤ |(-2 * b * t - x) * fermi (-a * t)| + |a * fermiOne (-a * t)| :=
        abs_sub _ _
      _ = |-2 * b * t - x| * fermi (-a * t) + |a| * |fermiOne (-a * t)| := by
        rw [abs_mul, abs_mul, abs_of_pos hp]
      _ ≤ _ := by
        rw [add_mul]
        gcongr
        exact abs_fermiOne_le_fermi _
  rw [dampedOne, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le).trans_eq (by
    unfold damped
    ring)

/-- The second derivative also retains the Fermi envelope, including on
the negative half-line where it is essential for domination. -/
theorem abs_dampedTwo_le_coeff (a b x t : ℝ) :
    |dampedTwo a b x t| ≤ ((|-2 * b * t - x| + |a|) ^ 2 + 2 * |b|) *
      damped a b x t := by
  let T := -2 * b * t - x
  let q := fermi (-a * t)
  have hq : 0 < q := (fermi_bounds _).1
  have hbase : |T ^ 2 - 2 * b| ≤ T ^ 2 + 2 * |b| := by
    calc
      _ ≤ |T ^ 2| + |2 * b| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (sq_nonneg T), abs_mul]; norm_num
  have h0 : |(T ^ 2 - 2 * b) * q| ≤ (T ^ 2 + 2 * |b|) * q := by
    rw [abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_right hbase hq.le
  have h1 : |2 * a * T * fermiOne (-a * t)| ≤ 2 * |a| * |T| * q := by
    norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (abs_fermiOne_le_fermi _) (by positivity)
  have h2 : |a ^ 2 * fermiTwo (-a * t)| ≤ a ^ 2 * q := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    exact mul_le_mul_of_nonneg_left (abs_fermiTwo_le_fermi _) (sq_nonneg a)
  have hinner := (abs_add_le ((T ^ 2 - 2 * b) * q - 2 * a * T * fermiOne (-a * t))
    (a ^ 2 * fermiTwo (-a * t))).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add h0 h1)) h2)
  have he : (T ^ 2 + 2 * |b|) * q + 2 * |a| * |T| * q + a ^ 2 * q =
      ((|T| + |a|) ^ 2 + 2 * |b|) * q := by
    rw [add_sq, sq_abs, sq_abs]
    ring
  rw [he] at hinner
  rw [dampedTwo, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le).trans_eq (by
    dsimp only [T, q, damped]
    ring)

private theorem coefficient_le {a b x δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) (t : ℝ) :
    |-2 * b * t - x| + |a| ≤ 2 * b * |t| + 2 * a + δ := by
  have hlin : |-2 * b * t - x| ≤ 2 * b * |t| + |x| := by
    calc
      _ ≤ |-2 * b * t| + |x| := abs_sub _ _
      _ = _ := by norm_num [abs_mul, abs_of_nonneg hb]
  rw [abs_of_nonneg ha]
  linarith [abs_abscissa_le ha hx0 hxa]

/-- A concrete common envelope for the amplitude and its first two
derivatives on an enlarged reflection strip. -/
def envelope (a b δ t : ℝ) : ℝ :=
  Real.exp (1 / 2) * ((2 * b * |t| + 2 * a + δ) ^ 2 + 2 * b + 1) *
    Real.exp (-(b / 2) * t ^ 2)

/-- The same Gaussian envelope controls all three orders simultaneously. -/
theorem abs_damped_orders_le_envelope {a b x δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδb : δ ^ 2 ≤ b) (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) (t : ℝ) :
    |damped a b x t| ≤ envelope a b δ t ∧
      |dampedOne a b x t| ≤ envelope a b δ t ∧
        |dampedTwo a b x t| ≤ envelope a b δ t := by
  let M := 2 * b * |t| + 2 * a + δ
  let G := Real.exp (1 / 2) * Real.exp (-(b / 2) * t ^ 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have henv : envelope a b δ t = (M ^ 2 + 2 * b + 1) * G := by
    dsimp [envelope, M, G]
    ring
  have h0 : damped a b x t ≤ G := damped_le_gaussian hb hδb hx0 hxa t
  have hc : |-2 * b * t - x| + |a| ≤ M := coefficient_le ha hb.le hx0 hxa t
  have h1 : |dampedOne a b x t| ≤ M * G :=
    (abs_dampedOne_le_coeff a b x t).trans
      (mul_le_mul hc h0 (damped_pos _ _ _ _).le hM)
  have h2 : |dampedTwo a b x t| ≤ (M ^ 2 + 2 * b) * G := by
    apply (abs_dampedTwo_le_coeff a b x t).trans
    rw [abs_of_nonneg hb.le]
    apply mul_le_mul ?_ h0 (damped_pos _ _ _ _).le (by positivity)
    gcongr
  rw [henv, abs_of_pos (damped_pos _ _ _ _)]
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩
  · nlinarith [sq_nonneg M, mul_nonneg (sq_nonneg M) hG]
  · have hM1 : M ≤ M ^ 2 + 2 * b + 1 := by nlinarith [sq_nonneg (M - 1 / 2)]
    exact mul_le_mul_of_nonneg_right hM1 hG
  · exact mul_le_mul_of_nonneg_right (by linarith) hG

/-- A polynomial coefficient for a simpler Gaussian majorant. -/
def amplitudeCost (a b δ : ℝ) : ℝ :=
  Real.exp (1 / 2) * (34 * b + 2 * (2 * a + δ) ^ 2 + 1)

/-- The completely evaluated common integral bound. Its dependence on a
small Gaussian scale is polynomial, rather than exponential. -/
def integralCost (a b δ : ℝ) : ℝ := amplitudeCost a b δ * Real.sqrt (Real.pi / (b / 4))

/-- The explicit integral allowance is strictly positive at positive scale. -/
theorem integralCost_pos {b : ℝ} (hb : 0 < b) (a δ : ℝ) : 0 < integralCost a b δ := by
  unfold integralCost amplitudeCost
  positivity

/-- The polynomial Gaussian envelope is bounded by a wider Gaussian with
an explicit coefficient. -/
theorem envelope_le_simple {b : ℝ} (hb : 0 ≤ b) (a δ t : ℝ) :
    envelope a b δ t ≤ amplitudeCost a b δ * Real.exp (-(b / 4) * t ^ 2) := by
  let q := 2 * a + δ
  let v := (b / 4) * t ^ 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpoly : (2 * b * |t| + q) ^ 2 ≤ 8 * b ^ 2 * t ^ 2 + 2 * q ^ 2 := by
    have hs := sq_nonneg (2 * b * |t| - q)
    simp only [sub_sq, mul_pow, sq_abs] at hs
    have habs : (2 * b * |t|) ^ 2 = 4 * b ^ 2 * t ^ 2 := by
      simp only [mul_pow, sq_abs]
      ring
    nlinarith
  have he : Real.exp (-(b / 2) * t ^ 2) = Real.exp (-v) * Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [v]
    ring
  have hve : v * Real.exp (-v) ≤ 1 := by
    calc
      _ ≤ Real.exp v * Real.exp (-v) := by
        gcongr
        linarith [Real.add_one_le_exp v]
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hquad : 8 * b ^ 2 * t ^ 2 * Real.exp (-(b / 2) * t ^ 2) ≤
      32 * b * Real.exp (-v) := by
    calc
      _ = 32 * b * (v * Real.exp (-v)) * Real.exp (-v) := by
        rw [he]
        dsimp [v]
        ring
      _ ≤ 32 * b * 1 * Real.exp (-v) := by gcongr
      _ = _ := by ring
  have hexp : Real.exp (-(b / 2) * t ^ 2) ≤ Real.exp (-v) := by
    apply Real.exp_le_exp.mpr
    dsimp [v]
    nlinarith [sq_nonneg t]
  have hconstant := mul_le_mul_of_nonneg_left hexp
    (by positivity : 0 ≤ 2 * q ^ 2 + 2 * b + 1)
  have hbound : ((2 * b * |t| + q) ^ 2 + 2 * b + 1) *
      Real.exp (-(b / 2) * t ^ 2) ≤
      (34 * b + 2 * q ^ 2 + 1) * Real.exp (-v) := by
    calc
      _ ≤ (8 * b ^ 2 * t ^ 2 + 2 * q ^ 2 + 2 * b + 1) *
          Real.exp (-(b / 2) * t ^ 2) := by gcongr
      _ ≤ _ := by nlinarith
  have hout := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (1 / 2)).le
  simpa only [envelope, amplitudeCost, q, v, mul_assoc, add_assoc, neg_mul] using hout

/-- The three exact orders are continuous on the full real line. -/
theorem continuous_damped_orders (a b x : ℝ) :
    Continuous (damped a b x) ∧ Continuous (dampedOne a b x) ∧ Continuous (dampedTwo a b x) := by
  have hf : Continuous fermi := continuous_fermi
  have hf1 : Continuous fermiOne := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_fermiOne t).continuousAt
  have hf2 : Continuous fermiTwo := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_fermiTwo t).continuousAt
  refine ⟨continuous_iff_continuousAt.mpr fun t => (hasDerivAt_damped a b x t).continuousAt,
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_dampedOne a b x t).continuousAt, ?_⟩
  unfold dampedTwo
  fun_prop

/-- The simple Gaussian majorant is genuinely integrable. -/
theorem integrable_simple_majorant {b : ℝ} (hb : 0 < b) (a δ : ℝ) :
    Integrable (fun t : ℝ => amplitudeCost a b δ * Real.exp (-(b / 4) * t ^ 2)) :=
  (integrable_exp_neg_mul_sq (div_pos hb (by norm_num))).const_mul _

/-- The majorant integral has an exact closed form. -/
theorem integral_simple_majorant (a b δ : ℝ) :
    (∫ t : ℝ, amplitudeCost a b δ * Real.exp (-(b / 4) * t ^ 2)) = integralCost a b δ := by
  rw [integral_const_mul, integral_gaussian]
  rfl

/-- All three orders have genuine full-line integrability, with every
strip and scale hypothesis discharged by the common bound. -/
theorem integrable_damped_orders {a b x δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδb : δ ^ 2 ≤ b) (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) :
    Integrable (damped a b x) ∧ Integrable (dampedOne a b x) ∧ Integrable (dampedTwo a b x) := by
  have hcont := continuous_damped_orders a b x
  have hbound := abs_damped_orders_le_envelope ha hb hδ hδb hx0 hxa
  have hmajor := integrable_simple_majorant hb a δ
  refine ⟨hmajor.mono' hcont.1.aestronglyMeasurable ?_,
    hmajor.mono' hcont.2.1.aestronglyMeasurable ?_,
    hmajor.mono' hcont.2.2.aestronglyMeasurable ?_⟩
  · exact Eventually.of_forall fun t => (hbound t).1.trans (envelope_le_simple hb.le a δ t)
  · exact Eventually.of_forall fun t => (hbound t).2.1.trans (envelope_le_simple hb.le a δ t)
  · exact Eventually.of_forall fun t => (hbound t).2.2.trans (envelope_le_simple hb.le a δ t)

/-- The second derivative's absolute integral has an explicit uniform
bound throughout the enlarged strip. -/
theorem integral_abs_dampedTwo_le {a b x δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδb : δ ^ 2 ≤ b) (hx0 : -δ ≤ x) (hxa : x ≤ a + δ) :
    (∫ t : ℝ, |dampedTwo a b x t|) ≤ integralCost a b δ := by
  rw [← integral_simple_majorant a b δ]
  apply integral_mono (integrable_damped_orders ha hb hδ hδb hx0 hxa).2.2.abs
    (integrable_simple_majorant hb a δ)
  intro t
  exact (abs_damped_orders_le_envelope ha hb hδ hδb hx0 hxa t).2.2.trans
    (envelope_le_simple hb.le a δ t)

end
end RiemannGaussian.GaussianFermiDerivativeBounds
