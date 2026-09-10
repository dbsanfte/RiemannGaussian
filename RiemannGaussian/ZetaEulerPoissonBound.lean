/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinBudget
import RiemannGaussian.ZetaStechkinZeroFree

/-!
# A uniform Poisson bound through the Euler boundary

The actual reciprocal-logarithm zero-free strip controls the nearby zero
atoms. Far zero atoms decrease when shifted toward the Euler boundary.
Together with the complete positive xi mass this gives a logarithmic
bound uniform on the closed strip `1 <= sigma <= 3`, including `sigma=1`.

This bound is for the complete actual zero mass with multiplicities. It
supplies domination for boundary limits; it does not exclude further zeros.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- The height scale includes the entire four-unit comparison window. -/
def zetaEulerLogHeight (t : ℝ) : ℝ := Real.log (|t| + 26)

/-- The height scale is uniformly above three. -/
theorem three_lt_zetaEulerLogHeight (t : ℝ) : 3 < zetaEulerLogHeight t := by
  have h := three_lt_localZetaLogHeight t
  have hh := Real.log_le_log (by positivity : 0 < |t| + 22)
    (show |t| + 22 ≤ |t| + 26 by linarith)
  exact h.trans_le hh

private theorem atom_comparison {a h C : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hC : 1 ≤ C) (hsize : a + h ≤ C * a) (r : ℝ) :
    a / (a ^ 2 + r ^ 2) ≤ C * ((a + h) / ((a + h) ^ 2 + r ^ 2)) := by
  have hb : 0 < a + h := by linarith
  have hCa : a ≤ C * (a + h) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hsize (mul_nonneg ha.le hb.le)
  have h2 := mul_le_mul_of_nonneg_right hCa (sq_nonneg r)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [h1, h2]

private theorem atom_far {a h r : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hfar : a * (a + h) ≤ r ^ 2) :
    a / (a ^ 2 + r ^ 2) ≤ (a + h) / ((a + h) ^ 2 + r ^ 2) := by
  have hb : 0 < a + h := by linarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg hh (sub_nonneg.mpr hfar)]

/-- At each actual zero, the boundary Poisson atom is at most 65
times its value on the nearby Euler-product line. Nearby atoms use the
proved zero-free margin; far atoms use their exact signed geometry. -/
theorem zetaGlobalPoissonSummand_euler_shift_le (rho : NontrivialZetaZero)
    {σ t : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (ht : 5 ≤ |t|) :
    zetaGlobalPoissonSummand ((σ : ℂ) + I * t) rho ≤
      65 * zetaGlobalPoissonSummand
        (((σ + 1 / zetaEulerLogHeight t : ℝ) : ℂ) + I * t) rho := by
  let L := zetaEulerLogHeight t
  let x := 1 / L
  let a := σ - rho.1.re
  let r := t - rho.1.im
  have hL : 3 < L := three_lt_zetaEulerLogHeight t
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; apply (div_le_one (by linarith)).mpr; linarith
  have ha : 0 < a := by dsimp [a]; linarith [NontrivialZetaZero.re_lt_one rho]
  have ha3 : a ≤ 3 := by dsimp [a]; linarith [NontrivialZetaZero.zero_lt_re rho]
  have hbound : a / (a ^ 2 + r ^ 2) ≤ 65 * ((a + x) / ((a + x) ^ 2 + r ^ 2)) := by
    by_cases hnear : |r| ≤ 4
    · have htri : |t| ≤ |r| + |rho.1.im| := by
        simpa only [r, sub_add_cancel] using abs_add_le (t - rho.1.im) rho.1.im
      have hzero : 1 ≤ |rho.1.im| := by linarith
      have htri' : |rho.1.im| ≤ |r| + |t| := by
        have he : rho.1.im - t = -r := by dsimp [r]; ring
        have ht' := abs_add_le (rho.1.im - t) t
        rw [sub_add_cancel, he, abs_neg] at ht'
        exact ht'
      have hheight : localZetaLogHeight rho.1.im ≤ L := by
        apply Real.log_le_log (by positivity)
        linarith
      have hgap := zetaStechkin_margin_lt_one_sub_re rho hzero
      unfold zetaStechkinZeroMargin at hgap
      have hcomp : 1 / (64 * L) ≤ 1 / (64 * localZetaLogHeight rho.1.im) :=
        one_div_le_one_div_of_le (by nlinarith [three_lt_localZetaLogHeight rho.1.im])
          (by nlinarith)
      have hga : 1 / (64 * L) ≤ a := by dsimp [a]; linarith
      have hxsize : a + x ≤ 65 * a := by
        have hm := mul_le_mul_of_nonneg_left hga (by norm_num : (0 : ℝ) ≤ 64)
        have he : (64 : ℝ) * (1 / (64 * L)) = x := by dsimp [x]; field_simp
        rw [he] at hm
        linarith
      exact atom_comparison ha hx.le (by norm_num) hxsize r
    · have hr : 16 ≤ r ^ 2 := by nlinarith [sq_abs r]
      have hab : a * (a + x) ≤ r ^ 2 := by
        have hprod := mul_le_mul ha3 (show a + x ≤ 4 by linarith)
          (by linarith : 0 ≤ a + x) (by norm_num : (0 : ℝ) ≤ 3)
        nlinarith
      have hh := atom_far ha hx.le hab
      have hb : 0 ≤ (a + x) / ((a + x) ^ 2 + r ^ 2) := by positivity
      nlinarith
  have hm := mul_le_mul_of_nonneg_left hbound
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho) : (0 : ℝ) ≤ analyticZetaZeroMultiplicity rho)
  unfold zetaGlobalPoissonSummand
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero]
  dsimp only [a, r, x, L] at hm
  convert! hm using 1 <;> ring

/-- The complete real-axis prime sum has a pole bound with its global
logarithmic completion allowance. -/
theorem neg_logDeriv_riemannZeta_real_le_global {u : ℝ} (hu : 1 < u) :
    (-logDeriv riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + 1 + Real.log u := by
  have h := zeta_global_real_budget_le (s := (u : ℂ)) (by simpa using hu)
  have hz : 0 ≤ ∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand (u : ℂ) rho :=
    tsum_nonneg (zetaGlobalPoissonSummand_nonneg (by simpa using hu.le))
  have hp : (1 / ((u : ℂ) - 1) : ℂ).re = 1 / (u - 1) := by norm_cast
  simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, add_zero, hp] at h
  linarith

private theorem shifted_mass_le {σ t : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) :
    (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand
      (((σ + 1 / zetaEulerLogHeight t : ℝ) : ℂ) + I * t) rho) ≤ 5 * zetaEulerLogHeight t := by
  let L := zetaEulerLogHeight t
  let x := 1 / L
  let u := σ + x
  have hL : 3 < L := three_lt_zetaEulerLogHeight t
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; apply (div_le_one (by linarith)).mpr; linarith
  have hu : 1 < u := by dsimp [u]; linarith
  have hu4 : u ≤ 4 := by dsimp [u]; linarith
  have hinv : 1 / (u - 1) ≤ L := by
    calc
      _ ≤ 1 / x := one_div_le_one_div_of_le hx (by dsimp [u]; linarith)
      _ = L := by dsimp [x]; simp
  have hlogu : Real.log u ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < u)
    linarith
  have hreal := neg_logDeriv_riemannZeta_real_le_global hu
  have hD := norm_neg_logDeriv_riemannZeta_re_le_real_axis hu t
  rw [Real.norm_eq_abs] at hD
  have hDlower := (abs_le.mp hD).1
  have hheight : Real.log (u + |t|) ≤ L := by
    apply Real.log_le_log (by positivity)
    linarith
  have hpole : (u - 1) / ((u - 1) ^ 2 + t ^ 2) ≤ L := by
    calc
      _ ≤ (u - 1) / (u - 1) ^ 2 := div_le_div_of_nonneg_left (by linarith)
        (sq_pos_of_pos (by linarith)) (by nlinarith [sq_nonneg t])
      _ = 1 / (u - 1) := by field_simp
      _ ≤ L := hinv
  have h := zeta_global_vertical_budget_le (by linarith : 0 < u - 1) t
  rw [show 1 + (u - 1) = u by ring] at h
  change (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand ((u : ℂ) + I * t) rho) ≤ 5 * L
  linarith

/-- A logarithmic bound for the complete actual zero mass, uniform all
the way to `sigma=1`. The known zero-free strip is used only to control
the nearby atoms; no new zero-location assumption is made. -/
theorem tsum_zetaGlobalPoissonSummand_euler_le {σ t : ℝ}
    (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (ht : 5 ≤ |t|) :
    (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand ((σ : ℂ) + I * t) rho) ≤
      325 * zetaEulerLogHeight t := by
  have hL := three_lt_zetaEulerLogHeight t
  have hs := summable_zetaGlobalPoissonSummand (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have hx : 0 ≤ 1 / zetaEulerLogHeight t := by positivity
  have htSum := summable_zetaGlobalPoissonSummand
    (s := (((σ + 1 / zetaEulerLogHeight t : ℝ) : ℂ) + I * t))
    (by simpa using (show 1 ≤ σ + 1 / zetaEulerLogHeight t by linarith))
  have h := hs.tsum_le_tsum
    (fun rho => zetaGlobalPoissonSummand_euler_shift_le rho hσ hσ3 ht)
    (htSum.mul_left 65)
  rw [tsum_mul_left] at h
  have hb := shifted_mass_le (t := t) hσ hσ3
  nlinarith

end
end RiemannGaussian
