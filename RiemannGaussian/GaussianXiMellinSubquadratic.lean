import RiemannGaussian.GaussianXiGrowth
import Mathlib.Analysis.MeanInequalities

/-!
# A subquadratic Mellin growth bound for spectral xi

The existing global xi-growth proof absorbs the Mellin power `x^u` into an
exponential theta tail with a quadratic cost in `u`.  That is sufficient for
Gaussian zero sums but not for inverse-square divisor summability.

Here Young's inequality with conjugate exponents `4/3` and `4` gives a
strictly subquadratic cost.  We prove an explicit `u^(4/3)`-type bound for the
upper-tail Mellin transform.  This is the first analytic step toward a Jensen
divisor count of exponent below two and hence finite Poisson/Blaschke mass.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Explicit Young-inequality cost for absorbing a nonnegative Mellin power
into half of an exponential tail. -/
def mellinFourThirdsCost (p u : ℝ) : ℝ :=
  (4 * u / (2 * p) ^ (1 / 4 : ℝ)) ^ (4 / 3 : ℝ) / (4 / 3)

/-- The exponents `4/3` and `4` are Hölder conjugates. -/
theorem holderConjugate_four_thirds_four :
    Real.HolderConjugate (4 / 3 : ℝ) 4 := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- The fourth-power term in the scaled Young inequality is exactly half of
the original exponential rate. -/
theorem scaled_fourth_rpow_div_four
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (((2 * p) ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) ^ (4 : ℝ)) / 4 =
      p * x / 2 := by
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg hx _)]
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul hx]
  norm_num
  ring

/-- Scaled Young inequality in the form needed for the Mellin integrand. -/
theorem four_mul_mul_rpow_quarter_le_mellinFourThirdsCost_add_half
    {p u x : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    4 * u * x ^ (1 / 4 : ℝ) ≤
      mellinFourThirdsCost p u + p * x / 2 := by
  let a : ℝ := 4 * u / (2 * p) ^ (1 / 4 : ℝ)
  let b : ℝ := (2 * p) ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hyoung :=
    Real.young_inequality_of_nonneg ha hb
      holderConjugate_four_thirds_four
  have hab : a * b = 4 * u * x ^ (1 / 4 : ℝ) := by
    dsimp [a, b]
    field_simp [ne_of_gt
      (Real.rpow_pos_of_pos (by positivity : 0 < 2 * p) _)]
  rw [hab] at hyoung
  dsimp [a, b] at hyoung
  rw [scaled_fourth_rpow_div_four hp hx] at hyoung
  simpa [mellinFourThirdsCost] using hyoung

/-- A nonnegative Mellin power is absorbed into half the exponential tail at
the explicit strictly subquadratic Young cost. -/
theorem rpow_mul_exp_neg_le_exp_fourThirdsCost_mul_exp_neg_half_of_nonneg
    {p x u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (mellinFourThirdsCost p u) *
        Real.exp (-(p / 2) * x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h :=
      Real.log_le_rpow_div hxpos.le
        (by norm_num : (0 : ℝ) < 1 / 4)
    calc
      Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * x ^ (1 / 4 : ℝ) := by ring
  have hulog : u * Real.log x ≤ 4 * u * x ^ (1 / 4 : ℝ) := by
    nlinarith
  have hyoung :=
    four_mul_mul_rpow_quarter_le_mellinFourThirdsCost_add_half
      hp hu hxpos.le
  have hexponent :
      u * Real.log x + (-p * x) ≤
        mellinFourThirdsCost p u + (-(p / 2) * x) := by
    nlinarith
  rw [Real.rpow_def_of_pos hxpos]
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hexponent)

/-- For an arbitrary real Mellin exponent, replacing it by its nonnegative
part only increases `x^u` on `[1, infinity)`. -/
theorem rpow_mul_exp_neg_le_exp_fourThirdsCost_posPart_mul_exp_neg_half
    {p x u : ℝ} (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (mellinFourThirdsCost p (max 0 u)) *
        Real.exp (-(p / 2) * x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have huMax : u ≤ max 0 u := le_max_right _ _
  have hpow : x ^ u ≤ x ^ max 0 u :=
    Real.rpow_le_rpow_of_exponent_le hx huMax
  calc
    x ^ u * Real.exp (-p * x) ≤
        x ^ max 0 u * Real.exp (-p * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ ≤ Real.exp (mellinFourThirdsCost p (max 0 u)) *
        Real.exp (-(p / 2) * x) :=
      rpow_mul_exp_neg_le_exp_fourThirdsCost_mul_exp_neg_half_of_nonneg
        hp (le_max_left _ _) hx

/-- Quantitative subquadratic bound for the entire upper-tail Mellin
transform.  Its exponent cost grows like the `4/3` power of the positive part
of `Re(s) - 1`, rather than quadratically. -/
theorem norm_mellin_riemannThetaUpper_le_fourThirds
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖mellin riemannThetaUpper s‖ ≤
      (2 * C / p) *
        Real.exp
          (mellinFourThirdsCost p (max 0 (s.re - 1))) := by
  let Q : ℝ := mellinFourThirdsCost p (max 0 (s.re - 1))
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hhalf : 0 < p / 2 := by positivity
  have hmajorant : IntegrableOn
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (Ioi 0) := by
    change Integrable
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (volume.restrict (Ioi 0))
    exact (exp_neg_integrableOn_Ioi 0 hhalf).const_mul
      (C * Real.exp Q)
  rw [mellin]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) • riemannThetaUpper x‖ ≤
        ∫ x : ℝ in Ioi 0,
          (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx0
      by_cases hx1 : x ≤ 1
      · rw [riemannThetaUpper_eq_zero hx1, smul_zero, norm_zero]
        positivity
      · have hx1' : 1 < x := lt_of_not_ge hx1
        rw [riemannThetaUpper_eq_tail hx1', norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
          Complex.one_re]
        calc
          x ^ (s.re - 1) * ‖riemannThetaTail x‖ ≤
              x ^ (s.re - 1) * (C * Real.exp (-p * x)) :=
            mul_le_mul_of_nonneg_left (hbound x hx1'.le)
              (Real.rpow_nonneg hx0.le _)
          _ = C * (x ^ (s.re - 1) * Real.exp (-p * x)) := by ring
          _ ≤ C *
              (Real.exp (mellinFourThirdsCost p (max 0 (s.re - 1))) *
                Real.exp (-(p / 2) * x)) :=
            mul_le_mul_of_nonneg_left
              (rpow_mul_exp_neg_le_exp_fourThirdsCost_posPart_mul_exp_neg_half
                hp hx1'.le) hC0
          _ = (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
            simp only [Q]
            ring
    _ = (C * Real.exp Q) * (2 / p) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(p / 2)) (by linarith) 0]
      simp
    _ = (2 * C / p) *
        Real.exp (mellinFourThirdsCost p (max 0 (s.re - 1))) := by
      simp only [Q]
      field_simp [hp.ne']

end

end RiemannGaussian
