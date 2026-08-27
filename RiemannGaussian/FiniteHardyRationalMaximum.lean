import RiemannGaussian.FiniteHardyMultipointRational
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# A rational maximum principle for the finite Hardy argument

This file proves the analytic maximum principle needed after the complete
inside-core root polynomial has been cancelled from the common disk-transform
difference.  The degree condition supplies bounded growth at infinity, while
nonvanishing of the denominator excludes poles on the closed upper half-plane.
-/

open Polynomial
open Filter Asymptotics

namespace RiemannGaussian

noncomputable section

/-- Subtracting a nontrivial scalar multiple of one monic polynomial from
another monic polynomial of the same degree preserves that degree. -/
theorem natDegree_sub_C_mul_eq_of_monic_sameDegree
    {N D : ℂ[X]} (hN : N.Monic) (hD : D.Monic)
    (hdegree : N.natDegree = D.natDegree) {c : ℂ} (hc : c ≠ 1) :
    (D - C c * N).natDegree = D.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans <|
      max_le le_rfl (natDegree_C_mul_le c N |>.trans_eq hdegree)
  · rw [coeff_sub, coeff_C_mul, hD.coeff_natDegree,
      ← hdegree, hN.coeff_natDegree, mul_one]
    exact sub_ne_zero.mpr hc.symm

/-- Maximum-modulus principle for a proper rational function on the closed
upper half-plane. The degree condition supplies bounded growth at infinity,
so a real-boundary norm estimate propagates throughout the half-plane. -/
theorem polynomial_div_norm_le_of_upperHalfPlane_boundary
    (q P : ℂ[X]) {C : ℝ}
    (hdegree : q.degree ≤ P.degree)
    (hupper : ∀ z : ℂ, 0 ≤ z.im → P.eval z ≠ 0)
    (hboundary : ∀ x : ℝ, ‖q.eval (x : ℂ) / P.eval (x : ℂ)‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖q.eval z / P.eval z‖ ≤ C := by
  let f : ℂ → ℂ := fun w => q.eval (Complex.I * w) / P.eval (Complex.I * w)
  let right : Set ℂ := {w | 0 < w.re}
  let l : Filter ℂ := Bornology.cobounded ℂ ⊓ Filter.principal right
  have hdenClosed : ∀ w : ℂ, 0 ≤ w.re → P.eval (Complex.I * w) ≠ 0 := by
    intro w hw
    apply hupper
    simpa using hw
  have hdiff : DiffContOnCl ℂ f right := by
    constructor
    · intro w hw
      have hden : P.eval (Complex.I * w) ≠ 0 :=
        hdenClosed w (le_of_lt hw)
      dsimp only [f]
      fun_prop
    · change ContinuousOn f (closure {w : ℂ | 0 < w.re})
      rw [Complex.closure_setOfPred_lt_re]
      intro w hw
      have hden : P.eval (Complex.I * w) ≠ 0 := hdenClosed w hw
      dsimp only [f]
      fun_prop
  have hpoly : q.eval =O[Bornology.cobounded ℂ] P.eval :=
    Polynomial.isBigO_cobounded_of_degree_le hdegree
  have hrot : (fun w : ℂ => q.eval (Complex.I * w)) =O[Bornology.cobounded ℂ]
      (fun w : ℂ => P.eval (Complex.I * w)) := by
    simpa [Function.comp_def] using
      hpoly.comp_tendsto (Filter.tendsto_mul_left_cobounded Complex.I_ne_zero)
  have hrotRight := hrot.mono (show l ≤ Bornology.cobounded ℂ from inf_le_left)
  obtain ⟨K, hK⟩ := hrotRight.bound
  have hquot : f =O[l] (fun _ : ℂ => (1 : ℂ)) := by
    apply IsBigO.of_bound K
    filter_upwards [hK,
      mem_inf_of_right (mem_principal_self right)] with w hw hright
    have hPpos : 0 < ‖P.eval (Complex.I * w)‖ :=
      norm_pos_iff.mpr (hdenClosed w (le_of_lt hright))
    dsimp only [f]
    rw [norm_div, norm_one, mul_one]
    exact (div_le_iff₀ hPpos).2 hw
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[l] fun w => Real.exp (B * ‖w‖ ^ c) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    simpa using hquot
  have htendsto : Tendsto (fun x : ℝ => (x : ℂ)) atTop l := by
    apply tendsto_inf.2
    constructor
    · exact RCLike.tendsto_ofReal_atTop_cobounded ℂ
    · apply tendsto_principal.2
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simpa [right] using hx
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ := by
    simpa [Function.comp_def] using
      (hquot.comp_tendsto htendsto).isBoundedUnder_le
  have him : ∀ x : ℝ, ‖f ((x : ℂ) * Complex.I)‖ ≤ C := by
    intro x
    have harg : Complex.I * ((x : ℂ) * Complex.I) = (-x : ℝ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    dsimp only [f]
    rw [harg]
    exact hboundary (-x)
  have hwre : 0 ≤ (-Complex.I * z).re := by
    simpa using hz
  have hmax := PhragmenLindelof.right_half_plane_of_bounded_on_real
    hdiff hexp hre him hwre
  have harg : Complex.I * (-Complex.I * z) = z := by
    rw [← mul_assoc]
    simp
  dsimp only [f] at hmax
  rw [harg] at hmax
  exact hmax

end

end RiemannGaussian
