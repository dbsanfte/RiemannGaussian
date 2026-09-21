/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PrimeCountEuler
import RiemannGaussian.DirichletFamilyMoments
import RiemannGaussian.NatDivisorSquareDirichlet

/-!
# The D and K operators on the complete signed prime-count series

All sums genuinely converge in Re(s)>1. The polynomial reflected
coefficient is exact only on its stated cutoff class; no completion of
that class or of the actual allocation is presumed.
-/

namespace RiemannGaussian.PrimeCountEuler
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius

theorem coefficient_norm_le_divisors {z : ℂ} (hz : ‖z‖ ≤ 2) (n : ℕ) :
    ‖coefficient z n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hn : Squarefree n
  · have hmu : ‖(μ n : ℂ)‖ = 1 := by
      rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hn]
      simp
    rw [coefficient, norm_mul, norm_pow, hmu, one_mul,
      RoughCoprimeFactor.card_divisors_eq hn, count_eq_card]
    exact pow_le_pow_left₀ (norm_nonneg z) hz _
  · simp [coefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

private theorem card_le_square (n : ℕ) :
    (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ)^2 := by
  rcases Nat.eq_zero_or_pos n.divisors.card with h | h
  · simp [h]
  · have hh : (1 : ℝ) ≤ n.divisors.card := by exact_mod_cast h
    nlinarith

theorem coefficient_feature_bound {z : ℂ} (hz : ‖z‖ ≤ 2) (n : ℕ) (σ : ℝ) :
    ‖coefficient z n*zetaPrimeFeature (σ : ℂ) n‖ ≤
      (n.divisors.card : ℝ)^2*(n : ℝ)^(-σ) := by
  by_cases hn : n = 0
  · simp [hn, coefficient]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [norm_mul, norm_zetaPrimeFeature, Complex.ofReal_re, zetaPrimeExpWeight,
    Real.rpow_def_of_pos hn0]
  have he : -σ*Real.log n = Real.log n*(-σ) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right ((coefficient_norm_le_divisors hz n).trans
    (card_le_square n)) (Real.exp_pos _).le

theorem summable_coefficient_feature {z : ℂ} (hz : ‖z‖ ≤ 2) {σ : ℝ} (hσ : 1<σ) :
    Summable (fun n => coefficient z n*zetaPrimeFeature (σ : ℂ) n) :=
  (summable_card_divisors_sq_mul_rpow_neg hσ).of_norm_bounded
    (fun n => coefficient_feature_bound hz n σ)

/-- Complete D-moments, with the prime-count parameter retained. -/
def factorialMoment (z : ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  DirichletFamilyMoments.moment (coefficient z) id N s

theorem generating_eq_moment_zero (z s : ℂ) : generating z s = factorialMoment z 0 s := by
  unfold generating LSeries factorialMoment DirichletFamilyMoments.moment
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn, LSeries.term, coefficient]
  rw [LSeries.term_of_ne_zero hn]
  simp only [zetaPrimeLogKernel, pow_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, id_eq, div_eq_mul_inv]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    ← Complex.exp_neg, ← Complex.natCast_log]
  simp only [inv_one, one_mul, zetaPrimeFeature]
  congr 2
  ring

/-- D=-partial_s inserts the actual product logarithm at every order. -/
theorem signedTaylorMoment_generating {z : ℂ} (hz : ‖z‖ ≤ 2)
    (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    signedTaylorMoment N (generating z) s = factorialMoment z N s := by
  have he : generating z = DirichletFamilyMoments.moment (coefficient z) id 0 := by
    funext w
    exact generating_eq_moment_zero z w
  rw [he]
  exact DirichletFamilyMoments.signedTaylorMoment_eq (coefficient z) id
    (fun _ hσ => summable_coefficient_feature hz hσ) N hs

/-- K=z partial_z inserts the prime count into each exact coefficient. -/
theorem coefficient_K (z : ℂ) (n : ℕ) :
    z*deriv (fun w => coefficient w n) z = (count n : ℂ)*coefficient z n := by
  have hd : HasDerivAt (fun w => coefficient w n)
      ((μ n : ℂ)*((count n : ℂ)*z^(count n-1))) z := by
    simpa only [coefficient, Pi.pow_apply, id_eq, mul_one] using
      (((hasDerivAt_id z).pow (count n)).const_mul (μ n : ℂ))
  rw [hd.deriv, coefficient]
  cases h : count n with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- The complete count insertion at z=1 is justified by a summable
divisor-square majorant on a full neighbourhood of that parameter. -/
theorem hasSum_countMoment (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun n => (count n : ℂ)*(μ n : ℂ)*zetaPrimeLogKernel N s n)
      (deriv (fun z => factorialMoment z N s) 1) := by
  let σ := (1+s.re)/2
  let q := (s.re-1)/2
  let U : Set ℂ := Metric.ball 0 2
  have hσ : 1<σ := by dsimp [σ]; linarith
  have hq : 0<q := by dsimp [q]; linarith
  have hg := (summable_card_divisors_sq_mul_rpow_neg hσ).mul_left (q⁻¹^N)
  have hd (n : ℕ) : DifferentiableOn ℂ
      (fun z => coefficient z n*zetaPrimeLogKernel N s n) U := by
    intro z _
    exact ((((hasDerivAt_id z).pow (count n)).const_mul (μ n : ℂ)).mul_const
      (zetaPrimeLogKernel N s n)).differentiableAt.differentiableWithinAt
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖coefficient z n*zetaPrimeLogKernel N s n‖ ≤
        q⁻¹^N*((n.divisors.card : ℝ)^2*(n : ℝ)^(-σ)) := by
    have hz2 : ‖z‖ ≤ 2 := (by simpa [U, Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < 2).le
    have h := DirichletFamilyMoments.term_bound (coefficient z) id N hq
      (by dsimp [σ,q]; linarith : σ+q ≤ s.re) n
    exact h.trans (mul_le_mul_of_nonneg_left (coefficient_feature_bound hz2 n σ) (by positivity))
  have h1 : (1 : ℂ) ∈ U := by norm_num [U,Metric.mem_ball]
  have ht := Complex.hasSum_deriv_of_summable_norm hg hd Metric.isOpen_ball hb h1
  change HasSum _ (deriv (fun z => ∑' n, coefficient z n*zetaPrimeLogKernel N s n) 1)
  apply ht.congr_fun
  intro n
  have hd : HasDerivAt (fun z => coefficient z n*zetaPrimeLogKernel N s n)
      ((μ n : ℂ)*(count n : ℂ)*zetaPrimeLogKernel N s n) 1 := by
    simpa only [coefficient, Pi.pow_apply, id_eq, one_pow, mul_one] using
      ((((hasDerivAt_id (1 : ℂ)).pow (count n)).const_mul (μ n : ℂ)).mul_const
        (zetaPrimeLogKernel N s n))
  rw [hd.deriv]
  ring

end
end RiemannGaussian.PrimeCountEuler
