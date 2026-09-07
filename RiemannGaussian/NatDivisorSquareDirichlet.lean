import RiemannGaussian.NatDivisorSquareMean
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Summable weighted factorization collisions

The complete divisor-square mean bound implies convergence of its
Dirichlet series at every real exponent above one. Keeping a smaller
summable exponent gives a power bound for every finite weighted tail,
uniformly in its upper endpoint. This controls product collisions only;
it does not control correlations between different products.
-/

open Complex Filter Asymptotics
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

private theorem divisor_square_partial_sum_isBigO {r : ℝ} (hr : 1 < r) :
    (fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ 2) =O[atTop]
      fun M ↦ (M : ℝ) ^ r := by
  let e : ℝ := (r - 1) / 3
  have he : 0 < e := by dsimp [e]; linarith
  refine isBigO_iff.mpr ⟨(1 + 1 / e) ^ 3, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hMR
  have hl : 0 ≤ Real.log M := Real.log_nonneg hMR
  have hpow : 1 ≤ (M : ℝ) ^ e := Real.one_le_rpow hMR he.le
  have hlog := Real.log_le_rpow_div hMp.le he
  have hb : 1 + Real.log M ≤ (1 + 1 / e) * (M : ℝ) ^ e := by
    calc
      _ ≤ (M : ℝ) ^ e + (M : ℝ) ^ e / e := add_le_add hpow hlog
      _ = _ := by ring
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)),
    Real.norm_of_nonneg (Real.rpow_nonneg hMp.le _)]
  calc
    _ ≤ (M : ℝ) * (1 + Real.log M) ^ 3 := sum_Icc_card_divisors_sq_le_log_cube M
    _ ≤ (M : ℝ) * ((1 + 1 / e) * (M : ℝ) ^ e) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 3) hMp.le
    _ = (1 + 1 / e) ^ 3 * ((M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (e * 3)) := by
      rw [show (M : ℝ) ^ (e * 3) = ((M : ℝ) ^ e) ^ 3 by
        simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hMp.le e 3,
        Real.rpow_one, mul_pow]
      ring
    _ = (1 + 1 / e) ^ 3 * (M : ℝ) ^ r := by
      rw [← Real.rpow_add hMp]
      congr 2
      dsimp [e]
      ring

/-- The complete factorization-collision Dirichlet mass converges at every exponent strictly greater than one. -/
theorem summable_card_divisors_sq_mul_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ ↦ (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-p)) := by
  have hO := divisor_square_partial_sum_isBigO (by linarith : 1 < (p + 1) / 2)
  have hs := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n : ℕ ↦ (n.divisors.card : ℝ) ^ 2) (r := (p + 1) / 2) (s := (p : ℂ))
    hO (fun _ ↦ sq_nonneg _) (by linarith) (by simp only [Complex.ofReal_re]; linarith)
  refine hs.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The genuine summable divisor-square Dirichlet mass, available as a finite constant whenever its exponent is greater than one. -/
def divisorSquareDirichletMass (p : ℝ) : ℝ :=
  ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-p)

/-- The divisor collision mass is nonnegative, independently of the totalized-series convention outside its proved convergence domain. -/
theorem divisorSquareDirichletMass_nonneg (p : ℝ) : 0 ≤ divisorSquareDirichletMass p := by
  exact tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- A finite weighted divisor-square tail has an explicit power saving whenever a strictly smaller summable exponent is retained. The bound is uniform in the upper endpoint. -/
theorem sum_Ioc_card_divisors_sq_mul_rpow_neg_le {p s : ℝ} (hp : 1 < p) (hps : p ≤ s)
    {D : ℕ} (hD : 1 ≤ D) (M : ℕ) :
    (∑ n ∈ Finset.Ioc D M, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)) ≤
      divisorSquareDirichletMass p * (D : ℝ) ^ (p - s) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    _ ≤ ∑ n ∈ Finset.Ioc D M,
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-p)) * (D : ℝ) ^ (p - s) := by
      apply Finset.sum_le_sum
      intro n hn
      have hDn : (D : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
      have hnp := lt_of_lt_of_le hDp hDn
      have he : (n : ℝ) ^ (-s) = (n : ℝ) ^ (-p) * (n : ℝ) ^ (p - s) := by
        rw [← Real.rpow_add hnp]
        congr 1
        ring
      rw [he, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hDp hDn (sub_nonpos.mpr hps)) (by positivity)
    _ = (∑ n ∈ Finset.Ioc D M, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-p)) *
        (D : ℝ) ^ (p - s) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((summable_card_divisors_sq_mul_rpow_neg hp).sum_le_tsum _
        (fun n _ ↦ by positivity)) (by positivity)

end

end RiemannGaussian
