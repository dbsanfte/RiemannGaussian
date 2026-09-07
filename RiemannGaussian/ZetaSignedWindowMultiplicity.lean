import RiemannGaussian.ZetaSignedWindowPole

/-!
# An explicit simultaneous multiplicity bound near the strip edge

For absolute center height at least one, the rectangle of width and
ordinate half-width `1 / (6000 log (abs y + 22))` next to the right edge
contains at most one actual zero, counting full analytic multiplicity.
The proof uses every selected pole at the same evaluation point and
discharges membership in the common canonical disc.
-/

open Complex Metric Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The explicit common horizontal width and vertical half-width of the edge window. -/
def zetaSignedEdgeWindowWidth (y : ℝ) : ℝ := 1 / (6000 * localZetaLogHeight y)

/-- The edge window has strictly positive width at every real ordinate. -/
theorem zetaSignedEdgeWindowWidth_pos (y : ℝ) : 0 < zetaSignedEdgeWindowWidth y := by
  have := two_lt_localZetaLogHeight y
  unfold zetaSignedEdgeWindowWidth
  positivity

/-- The chosen window stays well inside the canonical geometry. -/
theorem zetaSignedEdgeWindowWidth_le_one_div_sixteen (y : ℝ) :
    zetaSignedEdgeWindowWidth y ≤ 1 / 16 := by
  have h := two_lt_localZetaLogHeight y
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 12000)
    (by linarith : (12000 : ℝ) ≤ 6000 * localZetaLogHeight y)).trans (by norm_num)

/-- The height-width product is exactly the constant used in the prime estimate. -/
theorem localZetaLogHeight_mul_signedEdgeWindowWidth (y : ℝ) :
    localZetaLogHeight y * zetaSignedEdgeWindowWidth y = 1 / 6000 := by
  have h : localZetaLogHeight y ≠ 0 := ne_of_gt (by linarith [two_lt_localZetaLogHeight y])
  unfold zetaSignedEdgeWindowWidth
  field_simp

/-- Actual zero membership retains both its horizontal coordinate and displacement from the common ordinate. -/
def InZetaSignedEdgeWindow (y : ℝ) (rho : NontrivialZetaZero) : Prop :=
  1 - zetaSignedEdgeWindowWidth y ≤ rho.1.re ∧ |rho.1.im - y| ≤ zetaSignedEdgeWindowWidth y

/-- An actual zero in the explicit window lies in the common canonical disc. -/
theorem InZetaSignedEdgeWindow.mem_canonicalBall {y : ℝ} {rho : NontrivialZetaZero}
    (h : InZetaSignedEdgeWindow y rho) :
    localZetaZeroTranslate y rho ∈ ball 0 (localZetaCanonicalRadius y) :=
  localZetaZeroTranslate_mem_canonicalBall y _ (zetaSignedEdgeWindowWidth_le_one_div_sixteen y) rho h.1 h.2

/-- A common Cauchy floor holds throughout the whole edge window at real shift four times its width. -/
theorem edgeWindow_cauchy_floor {D u v : ℝ} (hD : 0 < D)
    (hu : 4 * D ≤ u) (hu' : u ≤ 5 * D) (hv : |v| ≤ D) :
    5 / (26 * D) ≤ u / (u ^ 2 + v ^ 2) := by
  have huv : 0 < u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg v]
  have hv2 : v ^ 2 ≤ D ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg v) hv
    nlinarith [sq_abs v]
  have hprod := mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ 5 * u - D by linarith)
  rw [div_le_div_iff₀ (by positivity : 0 < 26 * D) huv]
  nlinarith

/-- All selected multiplicities contribute to the same local pole sum with one common positive floor. -/
theorem edgeWindow_multiplicity_cauchy_floor (y : ℝ) (S : Finset NontrivialZetaZero)
    (hS : ∀ rho ∈ S, InZetaSignedEdgeWindow y rho) :
    ((∑ rho ∈ S, analyticZetaZeroMultiplicity rho : ℕ) : ℝ) *
      (5 / (26 * zetaSignedEdgeWindowWidth y)) ≤
      (localZetaPoleSum y ((4 * zetaSignedEdgeWindowWidth y - 1 / 2 : ℝ) : ℂ)).re := by
  have hD := zetaSignedEdgeWindowWidth_pos y
  calc
    _ = ∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℝ) *
        (5 / (26 * zetaSignedEdgeWindowWidth y)) := by rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℝ) *
        ((4 * zetaSignedEdgeWindowWidth y + 1 - rho.1.re) /
          ((4 * zetaSignedEdgeWindowWidth y + 1 - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2)) := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact edgeWindow_cauchy_floor hD
        (by linarith [NontrivialZetaZero.re_lt_one rho])
        (by linarith [(hS rho hrho).1]) (by simpa only [abs_sub_comm] using (hS rho hrho).2)
    _ ≤ _ := sum_multiplicity_cauchy_le_localZetaPoleSum_re y S
      (fun rho hrho ↦ (hS rho hrho).mem_canonicalBall) (by positivity)

/-- Every finite set of actual zeros in the explicit near-edge rectangle has total analytic multiplicity at most one. -/
theorem sum_multiplicity_le_one_in_signedEdgeWindow (y : ℝ) (hy : 1 ≤ |y|)
    (S : Finset NontrivialZetaZero) (hS : ∀ rho ∈ S, InZetaSignedEdgeWindow y rho) :
    ∑ rho ∈ S, analyticZetaZeroMultiplicity rho ≤ 1 := by
  let D := zetaSignedEdgeWindowWidth y
  have hD : 0 < D := zetaSignedEdgeWindowWidth_pos y
  have hDsmall : D ≤ 1 / 16 := zetaSignedEdgeWindowWidth_le_one_div_sixteen y
  have hy0 : y ≠ 0 := by intro h; norm_num [h] at hy
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y]
  have hlow := edgeWindow_multiplicity_cauchy_floor y S hS
  have hup := four_mul_localZetaPoleSum_re_le_quadraticHeight hy0
    (by positivity : 0 < 4 * D) (by linarith : 4 * D ≤ 1 / 4)
  have hp : 17 * (4 * D) / (4 * y ^ 2) ≤ 17 * D := by
    rw [show 17 * (4 * D) / (4 * y ^ 2) = (17 * D) / y ^ 2 by ring]
    exact div_le_self (by positivity) hy2
  by_contra hn
  have hn2 : (2 : ℝ) ≤ ((∑ rho ∈ S, analyticZetaZeroMultiplicity rho : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ ∑ rho ∈ S, analyticZetaZeroMultiplicity rho by omega)
  have hnlow := mul_le_mul_of_nonneg_right hn2 (show 0 ≤ 5 / (26 * D) by positivity)
  have hbound : 4 * (2 * (5 / (26 * D))) ≤
      3 / (4 * D) + 4032 * localZetaLogHeight y + 17 * D := by
    change _ ≤ (localZetaPoleSum y ((4 * D - 1 / 2 : ℝ) : ℂ)).re at hlow
    linarith
  have hmul := mul_le_mul_of_nonneg_right hbound hD.le
  have hleft : 4 * (2 * (5 / (26 * D))) * D = 20 / 13 := by field_simp; ring
  have hright : (3 / (4 * D) + 4032 * localZetaLogHeight y + 17 * D) * D =
      3 / 4 + 4032 * (localZetaLogHeight y * D) + 17 * D ^ 2 := by field_simp
  rw [hleft, hright, localZetaLogHeight_mul_signedEdgeWindowWidth] at hmul
  have hD2 : D ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by nlinarith
  nlinarith

end

end RiemannGaussian
