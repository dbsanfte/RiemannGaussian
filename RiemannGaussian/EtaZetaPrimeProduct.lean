import RiemannGaussian.EtaZetaStripDerivative
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# An independent prime-product constraint at actual zeta zeros

Mathlib's classical three-four-one Euler-product inequality is combined
with the quantitative eta support bounds. All value and derivative bounds
are discharged for the original zeta function. The resulting constraint
excludes a quantitatively specified neighborhood of the right strip edge;
it does not exclude all off-critical zeros.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The classical three-four-one prime-product inequality, specialized
from Mathlib to the original Riemann zeta function. -/
theorem one_le_riemannZeta_three_four_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  simpa only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
    norm_mul, norm_pow] using
    DirichletCharacter.norm_LFunction_product_ge_one (1 : DirichletCharacter ℂ 1) hx y

/-- The literal positive eta mass rules out a real nontrivial zero. -/
theorem NontrivialZetaZero.im_ne_zero_of_eta_mass (rho : NontrivialZetaZero) : rho.1.im ≠ 0 := by
  intro him
  have h := (pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho).1
  rw [him] at h
  have hp := pairedEtaTiltedCosineMoment_zero_pos rho.1.re (NontrivialZetaZero.zero_lt_re rho)
  linarith

/-- Away from the real axis, the ordinate bounds the original pole
denominator from below. -/
theorem norm_riemannZeta_le_poleRemoved_div_abs_im {s : ℂ} (hsim : s.im ≠ 0) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta₁ s‖ / |s.im| := by
  have hs1 : s ≠ 1 := by intro h; apply hsim; simp [h]
  have himpos : 0 < |s.im| := abs_pos.mpr hsim
  have hden : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
  rw [riemannZeta_eq_inv_sub_mul hs1, norm_mul, norm_inv]
  simpa only [div_eq_mul_inv, mul_comm] using
    div_le_div_of_nonneg_left (norm_nonneg (riemannZeta₁ s)) himpos hden

/-- An explicit real-axis pole bound sufficient for the prime-product
argument, obtained from the same checked eta rectangle estimate. -/
theorem norm_riemannZeta_one_add_le_etaPole {x : ℝ} (hx : 0 < x) (hxhi : x ≤ 1 / 4) :
    ‖riemannZeta (1 + (x : ℂ))‖ ≤ 3200 / x := by
  have hs1 : (1 + (x : ℂ)) ≠ 1 := by simp [ne_of_gt hx]
  have hb : ‖riemannZeta₁ (1 + (x : ℂ))‖ ≤ 3200 := by
    have hlo : 1 / 2 ≤ (1 + (x : ℂ)).re := by simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith
    have hhi : (1 + (x : ℂ)).re ≤ 3 / 2 := by simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith
    have h := norm_riemannZeta₁_le_etaStrip hlo hhi
    norm_num at h
    exact h
  have hn : ‖(1 + (x : ℂ)) - 1‖ = x := by simp [abs_of_pos hx]
  rw [riemannZeta_eq_inv_sub_mul hs1, norm_mul, norm_inv, hn]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hx.le)

/-- The actual zeta value at twice the zero ordinate has an explicit
bound on the short segment to the right of one. -/
theorem norm_riemannZeta_one_add_double_ordinate_le {x y : ℝ}
    (hx : 0 < x) (hxhi : x ≤ 1 / 4) (hy : y ≠ 0) :
    ‖riemannZeta (1 + x + 2 * I * y)‖ ≤ 16 * (|y| + 21) ^ 2 / |y| := by
  have him : (1 + (x : ℂ) + 2 * I * y).im = 2 * y := by simp
  have himabs : |(1 + (x : ℂ) + 2 * I * y).im| = 2 * |y| := by rw [him, abs_mul]; norm_num
  have hlo : 1 / 2 ≤ (1 + (x : ℂ) + 2 * I * y).re := by simp; linarith
  have hhi : (1 + (x : ℂ) + 2 * I * y).re ≤ 3 / 2 := by simp; linarith
  have hb : ‖riemannZeta₁ (1 + x + 2 * I * y)‖ ≤ 32 * (|y| + 21) ^ 2 := by
    have h := norm_riemannZeta₁_le_etaStrip hlo hhi
    rw [himabs] at h
    calc
      _ ≤ 8 * (2 * |y| + 20) ^ 2 := h
      _ ≤ 8 * (2 * (|y| + 21)) ^ 2 := by gcongr; linarith
      _ = _ := by ring
  calc
    _ ≤ ‖riemannZeta₁ (1 + x + 2 * I * y)‖ / |(1 + (x : ℂ) + 2 * I * y).im| :=
      norm_riemannZeta_le_poleRemoved_div_abs_im (by rw [him]; exact mul_ne_zero (by norm_num) hy)
    _ ≤ (32 * (|y| + 21) ^ 2) / (2 * |y|) := by rw [himabs]; gcongr
    _ = _ := by ring

/-- A hypothetical zero near the right edge must satisfy this explicit
arithmetic inequality. The prime-product lower bound and every analytic
upper bound in it have been proved for the actual zeta function. -/
theorem one_le_etaPrimeProduct_zero_gap (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) :
    1 ≤ (16 * 3200 ^ 3 * 64 ^ 4 * (|rho.1.im| + 21) ^ 10 / |rho.1.im| ^ 5) *
      (1 - rho.1.re) := by
  let d := 1 - rho.1.re
  let t := |rho.1.im|
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hdhi : d ≤ 1 / 4 := by dsimp [d]; linarith
  have him := NontrivialZetaZero.im_ne_zero_of_eta_mass rho
  have ht : 0 < t := abs_pos.mpr him
  have hbase : (1 + (d : ℂ) + I * rho.1.im) =
      (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) := by dsimp [d]; push_cast; ring
  have hvalue : ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ≤
      64 * (t + 21) ^ 2 * d / t := by
    have him' : (1 + (d : ℂ) + I * rho.1.im).im = rho.1.im := by simp
    calc
      _ ≤ ‖riemannZeta₁ (1 + (d : ℂ) + I * rho.1.im)‖ / t := by
        simpa only [him', t] using norm_riemannZeta_le_poleRemoved_div_abs_im
          (s := 1 + (d : ℂ) + I * rho.1.im) (by rw [him']; exact him)
      _ ≤ _ := by
        rw [hbase]
        exact div_le_div_of_nonneg_right
          (norm_riemannZeta₁_reflected_across_one_le rho hrho) ht.le
  have hreal := norm_riemannZeta_one_add_le_etaPole hd hdhi
  have hdouble := norm_riemannZeta_one_add_double_ordinate_le hd hdhi him
  have hp := one_le_riemannZeta_three_four_one hd rho.1.im
  have hupper : ‖riemannZeta (1 + (d : ℂ))‖ ^ 3 *
      ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ^ 4 *
      ‖riemannZeta (1 + (d : ℂ) + 2 * I * rho.1.im)‖ ≤
      (3200 / d) ^ 3 * (64 * (t + 21) ^ 2 * d / t) ^ 4 * (16 * (t + 21) ^ 2 / t) := by
    gcongr
  refine (hp.trans hupper).trans_eq ?_
  change (3200 / d) ^ 3 * (64 * (t + 21) ^ 2 * d / t) ^ 4 * (16 * (t + 21) ^ 2 / t) =
    (16 * 3200 ^ 3 * 64 ^ 4 * (t + 21) ^ 10 / t ^ 5) * d
  field_simp

end

end RiemannGaussian
