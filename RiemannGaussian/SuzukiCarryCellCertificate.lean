/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrySmallCell

/-!
# Sharper certified tails of the literal polynomial-cell series

These are bounds for the actual Mellin coefficients, uniform in imaginary
height. They do not certify a finite prefix or any exceptional root.
-/

namespace RiemannGaussian.SuzukiCarryCellCertificate
noncomputable section
open Complex MeasureTheory Set
open SuzukiCarryMellinJet SuzukiCarryMellinBranches SuzukiCarrySmallCell
open scoped BigOperators

private theorem edge_le_one {N : ℕ} (hN : 11 ≤ N) : edge N ≤ 1 := by
  unfold edge
  rw [div_le_iff₀ (show (0 : ℝ) < (N+1 : ℕ) by positivity), one_mul]
  exact_mod_cast (show 12 ≤ N+1 by omega)

private theorem density_tail_bound {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 11 ≤ N)
    (g : ℝ → ℝ) {D : ℝ}
    (hb : ∀ x : ℝ, 0 < x → x ≤ 1 → |g x| ≤ D*x^2) :
    ‖∫ t in Iic (Real.log (edge N)), Complex.exp (s*t)*(g (Real.exp t) : ℂ)‖ ≤
      D*Real.exp ((s.re+2)*Real.log (edge N))/(s.re+2) := by
  have hs2 : 0 < s.re+2 := by linarith
  have hi := (integrableOn_exp_mul_Iic hs2 (Real.log (edge N))).const_mul D
  apply (norm_integral_le_of_norm_le hi ?_).trans_eq
    (by rw [integral_const_mul, integral_exp_mul_Iic hs2]; ring)
  filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
  have hx : Real.exp t ≤ 1 := by
    apply (Real.exp_le_exp.mpr ht).trans
    rw [Real.exp_log (edge_pos _)]
    exact edge_le_one hN
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hr : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
  rw [hr]
  calc
    _ ≤ Real.exp (s.re*t)*(D*(Real.exp t)^2) :=
      mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos t) hx) (Real.exp_pos _).le
    _ = D*(Real.exp (s.re*t)*(Real.exp t)^2) := by ring
    _ = D*Real.exp ((s.re+2)*t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      ring

/-- Quadratic coefficient: the certified tail gains two powers of the
cell edge, uniformly at every imaginary height. -/
theorem B_prefix_error_small {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 11 ≤ N) :
    ‖B s-∑ n ∈ Finset.range N, polynomialCell (bPolynomial (n+1)) s n‖ ≤
      10*Real.exp ((s.re+2)*Real.log (edge N))/(s.re+2) := by
  rw [B_sub_prefix_eq_tail hs]
  exact density_tail_bound hs hN quadraticDensity (fun _ hx hx1 => quadraticDensity_small hx hx1)

/-- Quartic coefficient: the same certified accumulation-point saving. -/
theorem C_prefix_error_small {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 11 ≤ N) :
    ‖C s-∑ n ∈ Finset.range N, polynomialCell (cPolynomial (n+1)) s n‖ ≤
      24*Real.exp ((s.re+2)*Real.log (edge N))/(s.re+2) := by
  rw [C_sub_prefix_eq_tail hs]
  exact density_tail_bound hs hN quarticDensity (fun _ hx hx1 => quarticDensity_small hx hx1)

private theorem exp_three_log_edge (N : ℕ) :
    Real.exp (3*Real.log (edge N)) = edge N^3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log (edge_pos _)]

/-- A quantitative certificate of the tail precision needed by a compact
root enclosure. Evaluation and outward rounding of this finite prefix remain
separate obligations; this theorem does not assert a root. -/
theorem tail_precision_at_re_one {s : ℂ} (hs : s.re = 1) :
    ‖B s-∑ n ∈ Finset.range 32000000,
      polynomialCell (bPolynomial (n+1)) s n‖ < 1/10^18 ∧
    ‖C s-∑ n ∈ Finset.range 32000000,
      polynomialCell (cPolynomial (n+1)) s n‖ < 1/10^18 := by
  have hp : 0 < s.re := by rw [hs]; norm_num
  have hb := B_prefix_error_small hp (N := 32000000) (by norm_num)
  have hc := C_prefix_error_small hp (N := 32000000) (by norm_num)
  rw [hs] at hb hc
  norm_num only [show (1 : ℝ)+2 = 3 by norm_num] at hb hc
  rw [exp_three_log_edge] at hb hc
  constructor
  · exact hb.trans_lt (by norm_num [edge])
  · exact hc.trans_lt (by norm_num [edge])

end
end RiemannGaussian.SuzukiCarryCellCertificate
