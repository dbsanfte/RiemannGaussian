/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFermiGlobalMargin
import RiemannGaussian.ZetaSquarefreeEulerReserveRadius

/-!
# The Fermi zero-free region in the marked squarefree theorem chain

The global monotone Fermi margin enlarges the analytic disc for the genuine
quotient `zeta(s)/zeta(2*s)`. Its radius never decreases and eventually
increases strictly, with an exact reciprocal-logarithmic formula. The
larger disc supplies a uniform Cauchy bound for all arithmetic marks and
all complex polynomials. The radius-dependent Euler budget is retained;
the independent signed ordinary-prime-tail estimate is not inferred.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- A common analytic radius from the global Fermi margin. The ordinate
cap keeps the disc away from the numerator and denominator poles. -/
def squarefreeEulerFermiRadius (y : ℝ) : ℝ :=
  1 + min ((|y| - 1) / 2) (zetaFermiZeroMargin (2 * |y| + 3) / 2)

/-- The radius is above one, below both the pole separation and `9/8`,
and within the full doubled-argument zero-free allowance. -/
theorem squarefreeEulerFermiRadius_bounds {y : ℝ} (hy : 1 < |y|) :
    1 < squarefreeEulerFermiRadius y ∧ squarefreeEulerFermiRadius y < |y| ∧
      squarefreeEulerFermiRadius y < 9 / 8 ∧
      2 * (squarefreeEulerFermiRadius y - 1) ≤ zetaFermiZeroMargin (2 * |y| + 3) := by
  obtain ⟨hm, hmu⟩ := zetaFermiZeroMargin_bounds (2 * |y| + 3)
  have hmin : 0 < min ((|y| - 1) / 2) (zetaFermiZeroMargin (2 * |y| + 3) / 2) :=
    lt_min (by linarith) (by positivity)
  have hleft := min_le_left ((|y| - 1) / 2) (zetaFermiZeroMargin (2 * |y| + 3) / 2)
  have hright := min_le_right ((|y| - 1) / 2) (zetaFermiZeroMargin (2 * |y| + 3) / 2)
  unfold squarefreeEulerFermiRadius
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Every previously proved reserve disc is contained in the new one. -/
theorem squarefreeEulerReserveRadius_le_fermiRadius (y : ℝ) :
    squarefreeEulerReserveRadius y ≤ squarefreeEulerFermiRadius y := by
  have h := zetaPoleReserve_margin_le_fermi (2 * |y| + 3)
  unfold squarefreeEulerReserveRadius squarefreeEulerFermiRadius
  exact add_le_add le_rfl (min_le_min_left _ (by linarith))

/-- A strict margin gain gives a strict radius gain whenever the pole cap
is inactive. The eventual theorem below discharges the margin premise. -/
theorem squarefreeEulerReserveRadius_lt_fermiRadius {y : ℝ} (hy : 3 / 2 ≤ |y|)
    (hm : zetaPoleReserveZeroMargin (2 * |y| + 3) < zetaFermiZeroMargin (2 * |y| + 3)) :
    squarefreeEulerReserveRadius y < squarefreeEulerFermiRadius y := by
  have ho := (zetaPoleReserveZeroMargin_bounds (2 * |y| + 3)).2
  have hf := (zetaFermiZeroMargin_bounds (2 * |y| + 3)).2
  unfold squarefreeEulerReserveRadius squarefreeEulerFermiRadius
  rw [min_eq_right (by linarith : zetaPoleReserveZeroMargin (2 * |y| + 3) / 2 ≤ (|y| - 1) / 2),
    min_eq_right (by linarith : zetaFermiZeroMargin (2 * |y| + 3) / 2 ≤ (|y| - 1) / 2)]
  linarith

/-- Beyond a proved finite height the new radius is strictly larger than
the old one and equals `1+3/(40*log(2*abs(y)+3))`. No arithmetic or analytic
premise is left, and the height is not numerically evaluated. -/
theorem exists_eventual_squarefreeEulerFermiRadius_gain :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      squarefreeEulerReserveRadius y < squarefreeEulerFermiRadius y ∧
        squarefreeEulerFermiRadius y = 1 + 3 / (40 * Real.log (2 * |y| + 3)) := by
  obtain ⟨T, _, hT⟩ := exists_eventual_fermiZeroMargin_eq
  refine ⟨max (3 / 2) T, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyT : T ≤ |y| := (le_max_right _ _).trans hy
  have harg : T ≤ |2 * |y| + 3| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
    linarith
  obtain ⟨he, hg⟩ := hT (2 * |y| + 3) harg
  refine ⟨squarefreeEulerReserveRadius_lt_fermiRadius hy1 hg, ?_⟩
  have hm := (zetaFermiZeroMargin_bounds (2 * |y| + 3)).2
  unfold squarefreeEulerFermiRadius
  rw [min_eq_right (by linarith : zetaFermiZeroMargin (2 * |y| + 3) / 2 ≤ (|y| - 1) / 2),
    he, abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
  ring

/-- The entire new closed disc avoids the numerator pole and every zero
or pole of the actual doubled zeta denominator. -/
theorem squarefreeEuler_fermi_disc_safe {y : ℝ} (hy : 1 < |y|) {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (squarefreeEulerFermiRadius y)) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨hr, hry, hru, hmargin⟩ := squarefreeEulerFermiRadius_bounds hy
  have hre := (Complex.abs_re_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  have him := (Complex.abs_im_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hre him
  have him0 : s.im ≠ 0 := by
    intro h
    simp only [h, zero_sub, abs_neg] at him
    linarith
  have hs1 : s ≠ 1 := by intro h; apply him0; simp [h]
  have hs2 : 2 * s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact him0 (by linarith)
  have himBound : |s.im| ≤ |y| + squarefreeEulerFermiRadius y := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, le_abs_self y, neg_abs_le y]
  have harg : |(2 * s).im| ≤ |2 * |y| + 3| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
    norm_num [abs_mul]
    linarith
  have hwidth := zetaFermiZeroMargin_antitone_abs harg
  have hedge : 1 - zetaFermiZeroMargin (2 * s).im ≤ (2 * s).re := by
    norm_num at hwidth ⊢
    have hM := (zetaFermiZeroMargin_bounds (2 * |y| + 3)).1
    nlinarith [(abs_le.mp hre).1]
  exact ⟨hs1, hs2, riemannZeta_ne_zero_of_fermi_margin hs2 hedge⟩

/-- The genuine complete squarefree quotient is analytic on a neighbourhood
of the entire larger closed disc. -/
theorem analyticOnNhd_squarefreeEulerResponse_fermi {y : ℝ} (hy : 1 < |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (squarefreeEulerFermiRadius y)) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := squarefreeEuler_fermi_disc_safe hy hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- The stronger zero-free region reaches every valid arithmetic mark and
every complex polynomial in the original squarefree response. A single
constant works on every smaller radius; the full radius-dependent Euler
budget is retained explicitly, including for moving marks and families. -/
theorem exists_squarefreeEuler_fermi_radius_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ squarefreeEulerFermiRadius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * squarefreeEulerBudget (3 / 2 - r) S P * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  exists_squarefreeEuler_variable_radius_bound_of_analytic y (squarefreeEulerFermiRadius y)
    (by linarith [(squarefreeEulerFermiRadius_bounds hy).1])
    (by linarith [(squarefreeEulerFermiRadius_bounds hy).2.2.1])
    (analyticOnNhd_squarefreeEulerResponse_fermi hy)

/-- For every fixed valid mark and polynomial, the actual complex response
decays after multiplication by any nonnegative geometric rate below the
new radius. Fixing the marks keeps their full Euler budget independent of
the moment order; no uniform claim for a growing sieve is implicit. -/
theorem tendsto_squarefreeEuler_scaled_response_fermi (y : ℝ) (hy : 1 < |y|)
    {a : ℝ} (ha : 0 ≤ a) (har : a < squarefreeEulerFermiRadius y)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (P : ℕ)
    (hP : Squarefree P) (hPS : ∀ q ∈ P.primeFactors, q ∉ S) (p : Polynomial ℂ) :
    Tendsto (fun N : ℕ ↦ ((a ^ N : ℝ) : ℂ) *
      RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_squarefreeEuler_fermi_radius_bound y hy
  let r := squarefreeEulerFermiRadius y
  let A := squarefreeEulerBudget (3 / 2 - r) S P
  let E := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; linarith [(squarefreeEulerFermiRadius_bounds hy).1]
  have hratio : a * r⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one hr).mpr har
  have hbound (N : ℕ) :
      ‖((a ^ N : ℝ) : ℂ) * RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
        (C * A * E) * (a * r⁻¹) ^ N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg ha _)]
    calc
      _ ≤ a ^ N * (C * A * r⁻¹ ^ N * E) :=
        mul_le_mul_of_nonneg_left (hb r hr le_rfl S hS P hP hPS p N) (pow_nonneg ha _)
      _ = _ := by rw [mul_pow]; ring
  apply squeeze_zero_norm hbound
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha (inv_nonneg.mpr hr.le)) hratio).const_mul
      (C * A * E)

/-- The strict eventual radius gain gives an actual stronger decay theorem:
for every fixed arithmetic mark and complex polynomial, multiplying the
response by the old outer radius to the moment order still tends to zero.
The finite height threshold and all analytic premises are discharged. -/
theorem exists_eventual_squarefreeEuler_reserve_scaled_decay :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ q ∈ P.primeFactors, q ∉ S) → ∀ p : Polynomial ℂ,
          Tendsto (fun N : ℕ ↦ ((squarefreeEulerReserveRadius y ^ N : ℝ) : ℂ) *
            RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨T, hT, hgain⟩ := exists_eventual_squarefreeEulerFermiRadius_gain
  refine ⟨T, hT, ?_⟩
  intro y hy S hS P hP hPS p
  have hy1 : 1 < |y| := by linarith
  exact tendsto_squarefreeEuler_scaled_response_fermi y hy1
    (by linarith [(squarefreeEulerReserveRadius_bounds hy1).1])
    (hgain y hy).1 S hS P hP hPS p

end
end RiemannGaussian
