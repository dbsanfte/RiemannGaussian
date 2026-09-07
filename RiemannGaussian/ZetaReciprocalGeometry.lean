import RiemannGaussian.ZetaSignedQuadraticComparison

/-!
# Zero avoidance for a quantitative reciprocal-zeta contour

The checked zero margin supplies an explicit strip just to the left of
one. Every complete local divisor point stays a positive distance from
that strip at absolute height at least two. The geometry is proved for
the actual pole-removed zeta function, with no zero-avoidance premise.
-/

open Complex MeromorphicOn Metric Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The horizontal allowance for the reciprocal contour inside the proved zero-free strip. -/
def zetaReciprocalStripWidth (y : ℝ) : ℝ := 1 / (500000 * localZetaLogHeight y)

/-- The reciprocal contour has strictly positive horizontal allowance. -/
theorem zetaReciprocalStripWidth_pos (y : ℝ) : 0 < zetaReciprocalStripWidth y := by
  have := two_lt_localZetaLogHeight y
  unfold zetaReciprocalStripWidth
  positivity

/-- The allowance fits inside the canonical inner geometry. -/
theorem zetaReciprocalStripWidth_le_eighth (y : ℝ) : zetaReciprocalStripWidth y ≤ 1 / 8 := by
  have h := two_lt_localZetaLogHeight y
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) (by linarith)

/-- Nearby ordinates have comparable actual logarithmic heights. -/
theorem localZetaLogHeight_le_two_mul_of_abs_sub_le_one {t y : ℝ} (h : |t - y| ≤ 1) :
    localZetaLogHeight t ≤ 2 * localZetaLogHeight y := by
  have ht : |t| ≤ |y| + 1 := by
    have ha := abs_add_le (t - y) y
    rw [sub_add_cancel] at ha
    linarith
  calc
    localZetaLogHeight t ≤ Real.log ((|y| + 22) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg y])
    _ = _ := by rw [Real.log_pow]; rfl

/-- A positive-real-part zero of pole-removed zeta is an actual nontrivial zero. -/
theorem isNontrivialZetaZero_of_poleRemoved_eq_zero {s : ℂ} (hs : 0 < s.re)
    (hz : riemannZeta₁ s = 0) : IsNontrivialZetaZero s := by
  have h1 : s ≠ 1 := by intro h; subst s; norm_num [riemannZeta₁_one] at hz
  rw [riemannZeta₁_eq_sub_one_mul h1] at hz
  refine ⟨(mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h1), ?_, h1⟩
  rintro ⟨n, rfl⟩
  norm_num at hs
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Every actual zero at a nearby ordinate leaves four times the contour allowance before the edge. -/
theorem four_mul_zetaReciprocalStripWidth_le_zero_gap (rho : NontrivialZetaZero)
    {y : ℝ} (hy : 1 ≤ |rho.1.im|) (hnear : |rho.1.im - y| ≤ 1) :
    4 * zetaReciprocalStripWidth y ≤ 1 - rho.1.re := by
  have hlog := localZetaLogHeight_le_two_mul_of_abs_sub_le_one hnear
  have hyL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hrL : 0 < localZetaLogHeight rho.1.im := by linarith [two_lt_localZetaLogHeight rho.1.im]
  have hmargin := (nontrivialZetaZero_mem_quadratic_reciprocal_log_strip rho hy).2
  have hcomp : 4 * zetaReciprocalStripWidth y ≤ 1 / (56458 * localZetaLogHeight rho.1.im) := by
    unfold zetaReciprocalStripWidth
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- The actual pole-removed function does not vanish in the shifted strip above absolute height one. -/
theorem riemannZeta₁_ne_zero_in_reciprocalStrip {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - zetaReciprocalStripWidth s.im ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := by linarith [zetaReciprocalStripWidth_le_eighth s.im]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hpos hz⟩
  have hgap := four_mul_zetaReciprocalStripWidth_le_zero_gap rho (y := s.im) hy (by simp [rho])
  change 4 * zetaReciprocalStripWidth s.im ≤ 1 - s.re at hgap
  linarith [zetaReciprocalStripWidth_pos s.im]

/-- Every complete local divisor point lies strictly beyond the reciprocal contour's horizontal buffer. -/
theorem localZetaDivisor_re_le_reciprocal_buffer (y : ℝ) (hy : 2 ≤ |y|) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0) :
    i.re ≤ -(1 / 2 : ℝ) - 4 * zetaReciprocalStripWidth y := by
  have himem := (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y))).supportWithinDomain hi
  have hin : ‖i‖ < 7 / 8 :=
    (show ‖i‖ < localZetaCanonicalRadius y by simpa only [mem_ball, dist_zero_right] using himem).trans
      (localZetaCanonicalRadius_spec y).2.1
  let s : ℂ := 3 / 2 + I * y + i
  have hsre : s.re = 3 / 2 + i.re := by simp [s]
  have hsim : s.im = y + i.im := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith [(abs_le.mp (Complex.abs_re_le_norm i)).1]
  have hsne : riemannZeta₁ s = 0 := localZetaPoleRemoved_eq_zero_of_divisor_ne_zero y hi
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hsne⟩
  have hnear : |rho.1.im - y| ≤ 1 := by
    change |s.im - y| ≤ 1
    rw [hsim, add_sub_cancel_left]
    linarith [Complex.abs_im_le_norm i]
  have hrh : 1 ≤ |rho.1.im| := by
    have ht := abs_add_le (y - rho.1.im) rho.1.im
    rw [sub_add_cancel, abs_sub_comm y rho.1.im] at ht
    linarith
  have hgap := four_mul_zetaReciprocalStripWidth_le_zero_gap rho hrh hnear
  change 4 * zetaReciprocalStripWidth y ≤ 1 - s.re at hgap
  rw [hsre] at hgap
  linarith

/-- The same positive distance separates every enclosed pole from every point of the shifted contour strip. -/
theorem three_mul_zetaReciprocalStripWidth_le_dist_localDivisor (y : ℝ) (hy : 2 ≤ |y|)
    {i z : ℂ} (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0)
    (hz : -(1 / 2 : ℝ) - zetaReciprocalStripWidth y ≤ z.re) :
    3 * zetaReciprocalStripWidth y ≤ ‖z - i‖ := by
  have hgap := localZetaDivisor_re_le_reciprocal_buffer y hy hi
  have hnorm := Complex.re_le_norm (z - i)
  simp only [Complex.sub_re] at hnorm
  linarith

end

end RiemannGaussian
