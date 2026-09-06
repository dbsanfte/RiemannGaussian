import RiemannGaussian.EtaZetaPoleBounds
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Round

/-!
# Uniform pole-removed zeta bounds across dyadic resonances

Rectangles with horizontal edges at the negative dyadic phase cover the
entire half-to-three-halves strip. The eta factor is bounded away from zero
on each boundary. The maximum-modulus principle for the entire pole-removed
zeta function transports the actual eta support estimate through all the
interior dyadic zeros, including the removable zeta pole at one.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The imaginary period of the elementary dyadic eta factor. -/
def etaDyadicImaginaryPeriod : ℝ := 2 * Real.pi / Real.log 2

/-- The dyadic imaginary period is positive. -/
theorem etaDyadicImaginaryPeriod_pos : 0 < etaDyadicImaginaryPeriod :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num))

/-- A rational upper bound suffices for the later ordinate envelope. -/
theorem etaDyadicImaginaryPeriod_le_sixteen : etaDyadicImaginaryPeriod ≤ 16 := by
  unfold etaDyadicImaginaryPeriod
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  linarith [Real.pi_lt_four, Real.log_two_gt_d9]

/-- Every ordinate lies in a closed dyadic period centered at an integer
multiple of that period. -/
theorem exists_etaDyadicRectangle_center (y : ℝ) : ∃ n : ℤ,
    y ∈ Icc (etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2)
      (etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2) := by
  refine ⟨round (y / etaDyadicImaginaryPeriod), ?_⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_sub_round (y / etaDyadicImaginaryPeriod))
  have h1 : (round (y / etaDyadicImaginaryPeriod) : ℝ) - 1 / 2 ≤
      y / etaDyadicImaginaryPeriod := by linarith
  have h2 : y / etaDyadicImaginaryPeriod ≤
      (round (y / etaDyadicImaginaryPeriod) : ℝ) + 1 / 2 := by linarith
  have h1' := (le_div_iff₀ etaDyadicImaginaryPeriod_pos).mp h1
  have h2' := (div_le_iff₀ etaDyadicImaginaryPeriod_pos).mp h2
  constructor <;> nlinarith

/-- Both horizontal edges of the chosen rectangle have the negative
dyadic phase, with the integer phase winding retained. -/
theorem cos_log_two_mul_etaDyadicRectangle_boundary (n : ℤ) {y : ℝ}
    (hy : y = etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2 ∨
      y = etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2) :
    Real.cos (Real.log 2 * y) = -1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rcases hy with hy | hy
  · have he : Real.log 2 * y = (n : ℝ) * (2 * Real.pi) - Real.pi := by
      rw [hy, etaDyadicImaginaryPeriod]
      field_simp
    rw [he, Real.cos_int_mul_two_pi_sub_pi]
  · have he : Real.log 2 * y = (n : ℝ) * (2 * Real.pi) + Real.pi := by
      rw [hy, etaDyadicImaginaryPeriod]
      field_simp
    rw [he, Real.cos_int_mul_two_pi_add_pi]

/-- The eta support estimate gives one explicit bound on every safe
rectangle boundary, expressed relative to the ordinate being enclosed. -/
theorem norm_riemannZeta₁_le_etaRectangle_envelope {s : ℂ} {y : ℝ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 3 / 2)
    (him : |s.im - y| ≤ etaDyadicImaginaryPeriod)
    (hfactor : (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|y| + 20) ^ 2 := by
  have hspos : 0 < s.re := by linarith
  have himabs : |s.im| ≤ |y| + 16 := by
    have h := abs_add_le (s.im - y) y
    rw [sub_add_cancel] at h
    linarith [etaDyadicImaginaryPeriod_le_sixteen]
  have hreabs : |s.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, hshi⟩
  have hreone : |s.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : ‖s‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hn1 : ‖s - 1‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hprod : ‖s - 1‖ * ‖s‖ ≤ (|y| + 20) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn1 hn (norm_nonneg s) (by positivity : 0 ≤ |y| + 20)
  refine (norm_riemannZeta₁_le_of_etaFactor_lower hspos hfactor).trans ?_
  rw [div_le_iff₀ hspos]
  nlinarith [sq_nonneg (|y| + 20)]

/-- The original eta support controls pole-removed zeta uniformly on
the full closed half-to-three-halves strip, including all dyadic resonances. -/
theorem norm_riemannZeta₁_le_etaStrip {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 3 / 2) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|s.im| + 20) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_etaDyadicRectangle_center s.im
  let a := etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2
  let b := etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2
  have hab : a < b := by dsimp [a, b]; linarith [etaDyadicImaginaryPeriod_pos]
  have hsab : s.im ∈ Icc a b := hn
  have hnear {y : ℝ} (hy : y ∈ Icc a b) : |y - s.im| ≤ etaDyadicImaginaryPeriod := by
    have hlen : b - a = etaDyadicImaginaryPeriod := by dsimp [a, b]; ring
    exact abs_le.mpr ⟨by linarith [hy.1, hsab.2], by linarith [hy.2, hsab.1]⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (1 / 2 : ℝ) (3 / 2)).reProdIm (isBounded_Ioo a b))
    differentiable_riemannZeta₁.diffContOnCl
  · intro z hz
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3 / 2),
      frontier_Ioo (by norm_num : (1 / 2 : ℝ) < 3 / 2),
      closure_Ioo hab.ne, frontier_Ioo hab] at hz
    rcases hz with hz | hz
    · have hzab : z.im = a ∨ z.im = b := by simpa using hz.2
      have hzmem : z.im ∈ Icc a b := by
        rcases hzab with hzab | hzab
        · rw [hzab]; exact ⟨le_rfl, hab.le⟩
        · rw [hzab]; exact ⟨hab.le, le_rfl⟩
      apply norm_riemannZeta₁_le_etaRectangle_envelope hz.1.1 hz.1.2 (hnear hzmem)
      exact (by norm_num : (1 / 4 : ℝ) ≤ 1).trans
        (one_le_norm_etaFactor_of_cos_eq_neg_one (cos_log_two_mul_etaDyadicRectangle_boundary n hzab))
    · have hzre : z.re = 1 / 2 ∨ z.re = 3 / 2 := by simpa using hz.1
      have hzlo : 1 / 2 ≤ z.re := hzre.elim (fun h ↦ by rw [h]) (fun h ↦ by rw [h]; norm_num)
      have hzhi : z.re ≤ 3 / 2 := hzre.elim (fun h ↦ by rw [h]; norm_num) (fun h ↦ by rw [h])
      exact norm_riemannZeta₁_le_etaRectangle_envelope hzlo hzhi (hnear hz.2)
        (quarter_le_norm_etaFactor_of_re_boundary hzre)
  · rw [closure_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3 / 2), closure_Ioo hab.ne]
    exact ⟨⟨hslo, hshi⟩, hsab⟩

end

end RiemannGaussian
