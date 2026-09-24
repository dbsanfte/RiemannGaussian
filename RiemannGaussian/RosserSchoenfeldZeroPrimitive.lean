/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldLaplace
import RiemannGaussian.RosserSchoenfeldZeroMass

/-!
# The complete logarithmically smoothed zero sum

Every analytic multiplicity and both ordinate signs are retained in
`sum m_rho * (exp(rho*t)-1)/rho^2`. The classical complete reciprocal-square
bound supplies actual convergence and a quantitative majorant. Its
one-sided Laplace transform is the full xi logarithmic-derivative difference.
-/

namespace RiemannGaussian.RosserSchoenfeldZeroPrimitive
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open RosserSchoenfeldLaplace

/-- One unweighted zero primitive in logarithmic time. -/
def atom (z : ℂ) (t : ℝ) : ℂ := (Complex.exp (z*t)-1)/z^2

/-- The actual multiplicity-weighted zero primitive. -/
def term (ρ : NontrivialZetaZero) (t : ℝ) : ℂ :=
  (analyticZetaZeroMultiplicity ρ : ℂ)*atom ρ.1 t

/-- The complete zero primitive, with the subtraction at time zero retained. -/
def value (t : ℝ) : ℂ := ∑' ρ : NontrivialZetaZero, term ρ t

private lemma atom_rewrite (s z : ℂ) (t : ℝ) :
    Complex.exp (-s*t)*atom z t =
      (Complex.exp (-s*t)*Complex.exp (z*t)-Complex.exp (-s*t))/z^2 := by
  unfold atom
  ring

/-- Each primitive has an absolutely convergent damped integral. -/
theorem integrable_atom {s z : ℂ} (hs : 0 < s.re) (hz : z.re < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*atom z t) (Ioi 0) := by
  have h0 := integrable_exponential (s := s) (z := 0) (by simpa using hs)
  simp only [zero_mul, Complex.exp_zero, mul_one] at h0
  apply (((integrable_exponential hz).sub h0).div_const (z^2)).congr
  filter_upwards with t
  exact (atom_rewrite s z t).symm

/-- The exact transform of one primitive retains its original zero coordinate. -/
theorem transform_atom {s z : ℂ} (hs : 0 < s.re) (hz : z.re < s.re) (hz0 : z ≠ 0) :
    transform s (atom z) = 1/(s*z*(s-z)) := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hsz : s-z ≠ 0 := ne_zero_of_re_pos (by simpa using sub_pos.mpr hz)
  have h0 := integrable_exponential (s := s) (z := 0) (by simpa using hs)
  have he0 := transform_exponential (s := s) (z := 0) (by simpa using hs)
  simp only [zero_mul, Complex.exp_zero, mul_one] at h0
  simp only [transform, zero_mul, Complex.exp_zero, mul_one, sub_zero] at he0
  have he := transform_exponential hz
  unfold transform at he
  change (∫ t : ℝ in Ioi 0, Complex.exp (-s*t)*atom z t) = _
  simp only [atom_rewrite]
  rw [integral_div, integral_sub (integrable_exponential hz) h0]
  rw [he, he0]
  field_simp
  ring

/-- Pointwise quantitative domination by the reciprocal-square weight. -/
theorem norm_atom_le {z : ℂ} (hz : z.re ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖atom z t‖ ≤ (Real.exp t+1)/‖z‖^2 := by
  rw [atom, norm_div, norm_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := norm_sub_le (Complex.exp (z*t)) 1
  rw [Complex.norm_exp] at hh
  norm_num [Complex.mul_re] at hh
  have he : Real.exp (z.re*t) ≤ Real.exp t := by
    apply Real.exp_le_exp.mpr
    nlinarith
  linarith

/-- Original multiplicity is retained in the summable majorant. -/
theorem norm_term_le (ρ : NontrivialZetaZero) {t : ℝ} (ht : 0 ≤ t) :
    ‖term ρ t‖ ≤ (Real.exp t+1)*
      ((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2) := by
  rw [term, norm_mul, Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left (norm_atom_le (NontrivialZetaZero.re_lt_one ρ).le ht)
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ))
  convert hh using 1 <;> first | rfl | ring

/-- The complete complex zero primitive is absolutely summable. -/
theorem summable_norm_term {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun ρ : NontrivialZetaZero => ‖term ρ t‖) := by
  exact (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (Real.exp t+1)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun ρ => norm_term_le ρ ht)

/-- The complete zero primitive is summable as a complex series. -/
theorem summable_term {t : ℝ} (ht : 0 ≤ t) : Summable (fun ρ : NontrivialZetaZero => term ρ t) :=
  (summable_norm_term ht).of_norm

/-- A global evaluated bound for the complete primitive at every nonnegative time. -/
theorem norm_value_lt {t : ℝ} (ht : 0 ≤ t) :
    ‖value t‖ < (463/10000 : ℝ)*(Real.exp t+1) := by
  have hh := (summable_norm_term ht).tsum_le_tsum (fun ρ => norm_term_le ρ ht)
    (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (Real.exp t+1))
  rw [tsum_mul_left] at hh
  have hb := mul_lt_mul_of_pos_left RosserSchoenfeldZeroMass.norm_square_mass_lt
    (show 0 < Real.exp t+1 by positivity)
  exact ((norm_tsum_le_tsum_norm (summable_norm_term ht)).trans hh).trans_lt
    (by simpa [mul_comm] using hb)

/-- Locally uniform convergence preserves continuity at every positive time. -/
theorem continuousOn_value : ContinuousOn value (Ioi 0) := by
  intro t ht
  have hc : ContinuousOn value (Ioo 0 (t+1)) := by
    apply continuousOn_tsum (fun ρ => (show Continuous (term ρ) by unfold term atom; fun_prop).continuousOn)
      (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left (Real.exp (t+1)+1))
    intro ρ x hx
    apply (norm_term_le ρ hx.1.le).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    gcongr
    exact hx.2.le
  have hmem : Ioo (0 : ℝ) (t+1) ∈ 𝓝 t := Ioo_mem_nhds ht (by linarith)
  exact ((hc t ⟨ht, by linarith⟩).continuousAt hmem).continuousWithinAt

/-- The subtraction at time zero is exact term by term. -/
@[simp] theorem value_zero : value 0 = 0 := by simp [value, term, atom]

/-- Scalar integrable majorant on the genuine convergence half-plane. -/
private def damping (s : ℂ) (t : ℝ) : ℝ :=
  Real.exp ((1-s.re)*t)+Real.exp (-s.re*t)

private lemma damping_eq (s : ℂ) (t : ℝ) :
    Real.exp (-s.re*t)*(Real.exp t+1) = damping s t := by
  rw [mul_add, mul_one, ← Real.exp_add]
  unfold damping
  congr 2
  ring

private lemma integrable_damping {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (damping s) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (by linarith : 1-s.re < 0) 0).add
    (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0)

private lemma norm_damped_term (s : ℂ) (ρ : NontrivialZetaZero) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-s*t)*term ρ t‖ ≤ damping s t *
      ((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2) := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp (-s.re*t)*((Real.exp t+1)*
        ((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2)) :=
      mul_le_mul_of_nonneg_left (norm_term_le ρ ht) (Real.exp_nonneg _)
    _ = _ := by rw [← mul_assoc, damping_eq]

/-- Every original multiplicity-weighted damped term is integrable. -/
theorem integrable_term {s : ℂ} (hs : 1 < s.re) (ρ : NontrivialZetaZero) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*term ρ t) (Ioi 0) := by
  have hh := (integrable_atom (by linarith : 0 < s.re)
    ((NontrivialZetaZero.re_lt_one ρ).trans hs)).const_mul
      (analyticZetaZeroMultiplicity ρ : ℂ)
  apply hh.congr
  filter_upwards with t
  unfold term
  ring

/-- The full sum of absolute integrals is finite; no conditional exchange is used. -/
theorem summable_integral_norm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : NontrivialZetaZero =>
      ∫ t : ℝ in Ioi 0, ‖Complex.exp (-s*t)*term ρ t‖) := by
  apply (RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left
    (∫ t : ℝ in Ioi 0, damping s t)).of_nonneg_of_le
  · intro ρ
    exact integral_nonneg (fun _ => norm_nonneg _)
  · intro ρ
    have hh := integral_mono_ae (integrable_term hs ρ).norm
      ((integrable_damping hs).mul_const
        ((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_damped_term s ρ ht.le)
    simpa only [integral_mul_const] using hh

/-- The complete zero primitive has a genuinely integrable Laplace kernel. -/
theorem integrable_value {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*value t) (Ioi 0) := by
  apply ((integrable_damping hs).mul_const (463/10000 : ℝ)).mono'
  · exact ((show Continuous (fun t : ℝ => Complex.exp (-s*t)) by fun_prop).continuousOn.mul
      continuousOn_value).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (-s.re*t)*((463/10000 : ℝ)*(Real.exp t+1)) :=
        mul_le_mul_of_nonneg_left (norm_value_lt ht.le).le (Real.exp_nonneg _)
      _ = (Real.exp (-s.re*t)*(Real.exp t+1))*(463/10000) := by ring
      _ = _ := by rw [damping_eq]

private lemma integral_term {s : ℂ} (hs : 1 < s.re) (ρ : NontrivialZetaZero) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-s*t)*term ρ t) =
      zetaLogDerivDifferenceSummand s 0 ρ / s^2 := by
  have hρ : (ρ.1 : ℂ) ≠ 0 := ne_zero_of_re_pos (NontrivialZetaZero.zero_lt_re ρ)
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hd : s-ρ.1 ≠ 0 := ne_zero_of_re_pos (by
    have hh := NontrivialZetaZero.re_lt_one ρ
    simp only [Complex.sub_re]
    linarith)
  have he : (fun t : ℝ => Complex.exp (-s*t)*term ρ t) =
      (fun t : ℝ => (analyticZetaZeroMultiplicity ρ : ℂ)*
        (Complex.exp (-s*t)*atom ρ.1 t)) := by
    funext t
    unfold term
    ring
  rw [he, integral_const_mul]
  change (analyticZetaZeroMultiplicity ρ : ℂ)*transform s (atom ρ.1) = _
  rw [transform_atom (by linarith) ((NontrivialZetaZero.re_lt_one ρ).trans hs) hρ]
  unfold zetaLogDerivDifferenceSummand
  field_simp
  ring

/-- Exact transform of the complete actual zero primitive. The full xi
logarithmic derivative and its value at zero are retained. -/
theorem transform_value {s : ℂ} (hs : 1 < s.re) :
    transform s value = (logDeriv riemannXi s-logDeriv riemannXi 0)/s^2 := by
  have hxi : riemannXi s ≠ 0 := by
    intro hz
    let ρ : NontrivialZetaZero := ⟨s, (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz⟩
    have hh := NontrivialZetaZero.re_lt_one ρ
    change s.re < 1 at hh
    linarith
  have hh := integral_tsum_of_summable_integral_norm (integrable_term hs)
    (summable_integral_norm hs)
  have he : (fun t : ℝ => ∑' ρ : NontrivialZetaZero, Complex.exp (-s*t)*term ρ t) =
      (fun t : ℝ => Complex.exp (-s*t)*value t) := by
    funext t
    rw [tsum_mul_left]
    rfl
  rw [he] at hh
  rw [transform, ← hh]
  simp only [integral_term hs, tsum_div_const]
  rw [(hasSum_zetaLogDerivDifference hxi (by simp [riemannXi_zero])).tsum_eq]

end
end RiemannGaussian.RosserSchoenfeldZeroPrimitive
