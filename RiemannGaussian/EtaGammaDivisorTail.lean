import RiemannGaussian.EtaGammaPhysicalAverage

/-!
# Exponential tails of the actual gamma-damped Möbius series

The literal gamma survival and eta kernels have explicit exponential
envelopes. They prove absolute convergence of the original completed
Möbius divisor series and bound its entire signed tail beyond `R >= 2 A`.
No arithmetic cancellation assumption is used in this outer-tail estimate.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

/-- The actual gamma survival function has a global exponential envelope. -/
theorem gammaSurvival_le_exp_half {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvival x ≤ 4 * Real.exp (-x / 2) := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ x / 2 by positivity) 3
  norm_num [Finset.sum_range_succ] at he
  have hp : 1 + x + x ^ 2 / 2 ≤ 4 * Real.exp (x / 2) := by nlinarith
  calc
    _ ≤ Real.exp (-x) * (4 * Real.exp (x / 2)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, mul_comm (Real.exp (-x)) 4, mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The entire positive integer exponential tail has its exact geometric mass. -/
theorem hasSum_exp_nat_tail {x : ℝ} (hx : 0 < x) (R : ℕ) :
    HasSum (fun n : ℕ ↦ Real.exp (-((R + n + 1 : ℕ) : ℝ) * x))
      (Real.exp (-(R : ℝ) * x) / (Real.exp x - 1)) := by
  have hq : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one (Real.exp_pos (-x)).le hq).mul_left
    (Real.exp (-(R : ℝ) * x) * Real.exp (-x))
  convert! h using 1
  · funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have he1 : Real.exp x - 1 ≠ 0 := by
      have hlt : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
      linarith
    rw [Real.exp_neg]
    field_simp

/-- Each survival-weighted eta term is bounded before summing its complex phase. -/
theorem norm_gammaDampedEta_term_le {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ‖(gammaEtaCoefficient x n : ℂ) * ((n + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      4 * Real.exp (-((n + 1 : ℝ) * x) / 2) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hQ := gammaSurvival_nonneg (show 0 ≤ (n + 1 : ℝ) * x by positivity)
  have hp : (n + 1 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
  rw [norm_mul, gammaEtaCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hQ,
    Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.neg_re]
  exact (mul_le_of_le_one_right hQ hp).trans (gammaSurvival_le_exp_half (by positivity))

/-- The full damped eta kernel has an explicit exponential tail, uniformly in its imaginary parameter. -/
theorem norm_gammaDampedEta_le_exp_half {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖gammaDampedEta s x‖ ≤ 8 * Real.exp (-x / 2) := by
  have hx0 : 0 < x := by linarith
  have hb := (hasSum_exp_nat_tail (show 0 < x / 2 by positivity) 0).mul_left 4
  have hmajor : HasSum (fun n : ℕ ↦ 4 * Real.exp (-((n + 1 : ℝ) * x) / 2))
      (4 / (Real.exp (x / 2) - 1)) := by
    convert! hb using 1
    · funext n
      push_cast
      congr 2
      ring
    · norm_num
      ring
  have hnorm : ‖gammaDampedEta s x‖ ≤ 4 / (Real.exp (x / 2) - 1) := by
    rw [gammaDampedEta_eq_mellin hs hx0]
    exact (hasSum_gammaDampedEta hs hx0).norm_le_of_bounded hmajor
      (norm_gammaDampedEta_term_le hs hx0.le)
  have he : 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hden : 0 < Real.exp (x / 2) - 1 := by linarith
  apply hnorm.trans
  rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  apply (div_le_iff₀ hden).mpr
  have hE := Real.exp_pos (x / 2)
  field_simp
  nlinarith

/-- In the large-divisor range the literal completed term has an exponential envelope. -/
theorem norm_gammaMoebiusTerm_large_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {d : ℕ} (hd : 1 ≤ d) (hAd : 2 * A ≤ d) :
    ‖gammaMoebiusTerm rho A d‖ ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (d : ℝ) ^ (-rho.1.re) * Real.exp (-(d : ℝ) / (2 * A)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hg := norm_gammaDampedEta_le_exp_half (NontrivialZetaZero.zero_lt_re rho)
    ((le_div_iff₀ hA).mpr hAd)
  rw [gammaMoebiusTerm, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hd, Complex.neg_re]
  calc
    _ ≤ 1 * (d : ℝ) ^ (-rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ * (8 * Real.exp (-((d : ℝ) / A) / 2))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hdR.le _))
        (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) (by positivity) (by positivity)
    _ = _ := by
      rw [show -((d : ℝ) / A) / 2 = -(d : ℝ) / (2 * A) by ring]
      ring

private theorem gammaMoebiusTail_majorant (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {R : ℕ} (hR : 2 * A ≤ R) (n : ℕ) :
    ‖gammaMoebiusTerm rho A (R + n + 1)‖ ≤
      (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (R : ℝ) ^ (-rho.1.re)) *
        Real.exp (-((R + n + 1 : ℕ) : ℝ) * (1 / (2 * A))) := by
  have hR0 : (0 : ℝ) < R := (by positivity : (0 : ℝ) < 2 * A).trans_le hR
  have hRd : (R : ℝ) ≤ (R + n + 1 : ℕ) := by exact_mod_cast (show R ≤ R + n + 1 by omega)
  have hd : 1 ≤ R + n + 1 := by omega
  have hp := Real.rpow_le_rpow_of_nonpos hR0 hRd
    (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  apply (norm_gammaMoebiusTerm_large_le rho hA hd (hR.trans hRd)).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖))
    (Real.exp_pos (-((R + n + 1 : ℕ) : ℝ) / (2 * A))).le
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- The actual infinite Möbius divisor series is absolutely convergent at every positive gamma scale. -/
theorem summable_norm_gammaMoebiusTerm (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ ↦ ‖gammaMoebiusTerm rho A (n + 1)‖) := by
  let R : ℕ := ⌈2 * A⌉₊
  have hR : 2 * A ≤ R := Nat.le_ceil _
  have hb := (hasSum_exp_nat_tail (show 0 < 1 / (2 * A) by positivity) R).summable.mul_left
    (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (R : ℝ) ^ (-rho.1.re))
  apply (summable_nat_add_iff R).mp
  apply hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  simpa only [Nat.add_comm n R] using gammaMoebiusTail_majorant rho hA hR n

/-- The full signed infinite tail has an explicit bound, with no Möbius cancellation assumed. -/
theorem norm_tsum_gammaMoebiusTerm_tail_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {R : ℕ} (hR : 2 * A ≤ R) :
    ‖∑' n : ℕ, gammaMoebiusTerm rho A (R + n + 1)‖ ≤
      16 * ‖pairedEtaXiCompletionFactor rho.1‖ * A * (R : ℝ) ^ (-rho.1.re) *
        Real.exp (-(R : ℝ) / (2 * A)) := by
  have hx : 0 < 1 / (2 * A) := by positivity
  have hb := (hasSum_exp_nat_tail hx R).mul_left
    (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (R : ℝ) ^ (-rho.1.re))
  have hs : Summable (fun n : ℕ ↦ gammaMoebiusTerm rho A (R + n + 1)) := by
    apply Summable.of_norm
    exact hb.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (gammaMoebiusTail_majorant rho hA hR)
  have hnorm := hs.hasSum.norm_le_of_bounded hb (gammaMoebiusTail_majorant rho hA hR)
  have he : 1 / (2 * A) ≤ Real.exp (1 / (2 * A)) - 1 := by
    linarith [Real.add_one_le_exp (1 / (2 * A))]
  apply hnorm.trans
  rw [← mul_div_assoc]
  calc
    _ ≤ (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (R : ℝ) ^ (-rho.1.re) *
        Real.exp (-(R : ℝ) * (1 / (2 * A)))) / (1 / (2 * A)) :=
      div_le_div_of_nonneg_left (by positivity) hx he
    _ = _ := by
      simp only [one_div, div_inv_eq_mul]
      rw [show -(R : ℝ) * (2 * A)⁻¹ = -(R : ℝ) / (2 * A) by ring]
      ring


end

end RiemannGaussian.EtaGammaSmoothing
