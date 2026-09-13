/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerQuadratic
import RiemannGaussian.ZetaRoughCoprimeFactorDecay
import RiemannGaussian.ZetaPrimeDensityEulerBudget
import RiemannGaussian.NatDivisorSquareDirichlet
import RiemannGaussian.NatLcmSqrtMass
import RiemannGaussian.ZetaVaughanCutoffBudget
import RiemannGaussian.ZetaSquarefreeEulerLogDecay
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Removing the full nonsquarefree Vaughan band

Averaging the complete reciprocal squarefree Euler correction costs only
an inverse-square-root divisor mass with one genuinely convergent constant.
The exact coprime Möbius--prime prefix therefore keeps the square-root
product budget at the larger Vaughan cutoffs. The logarithmic prefix and
ordinary-prime head also have independent bounds. Together they prove the
entire nonsquarefree band negligible for every fixed polynomial, eligible
ordinate and normalization 0 < u < 1, at D_N = floor(u^(-N)/(N+1)).

The squarefree band retains the original conditional negative-multiplicity
source. Its independent cofinal signed lower bound remains open. This uses
classical Euler products, divisor expansions, Chebyshev density and Cauchy
estimates; no historical novelty or additional zero-free region is claimed.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.SquarefreeVaughanProjection
noncomputable section

private theorem prime_sqrt_lower {p : ℕ} (hp : p.Prime) :
    (4 / 3 : ℝ) ≤ Real.sqrt p := by
  apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)).mpr
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

/-- The complete reciprocal local factor has a summable divisor-expansion
majorant, uniformly including the boundary Re(s) = 1/2. -/
theorem norm_inverse_local_le {s : ℂ} (hs : 1 / 2 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖(1 + zetaPrimeFeature s p)⁻¹‖ ≤ 1 + 4 / Real.sqrt p := by
  let t := Real.sqrt (p : ℝ)
  have ht : 4 / 3 ≤ t := prime_sqrt_lower hp
  have ht0 : 0 < t := by linarith
  have hx := norm_zetaPrimeFeature_le_inv_sqrt hs hp.pos
  have htri : 1 ≤ ‖1 + zetaPrimeFeature s p‖ + ‖zetaPrimeFeature s p‖ := by
    simpa using norm_sub_le (1 + zetaPrimeFeature s p) (zetaPrimeFeature s p)
  have hlow : 1 - 1 / t ≤ ‖1 + zetaPrimeFeature s p‖ := by linarith
  have hi : 1 / t < 1 := (div_lt_one ht0).mpr (by linarith)
  have hlow0 : 0 < 1 - 1 / t := by linarith
  rw [norm_inv, ← one_div]
  calc
    _ ≤ 1 / (1 - 1 / t) := one_div_le_one_div_of_le hlow0 hlow
    _ ≤ 1 + 4 / t := by
      apply (div_le_iff₀ hlow0).mpr
      field_simp
      nlinarith

private def localMajorant : ArithmeticFunction ℝ :=
  .prodPrimeFactors (fun p ↦ 4 / Real.sqrt p)

private theorem localMajorant_eq {n : ℕ} (hn : Squarefree n) :
    localMajorant n = (n.divisors.card : ℝ) ^ 2 / Real.sqrt n := by
  have hs : (∏ p ∈ n.primeFactors, Real.sqrt (p : ℝ)) = Real.sqrt n := by
    rw [← Real.sqrt_prod _ (fun p _ ↦ Nat.cast_nonneg p), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hn]
  rw [localMajorant, ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero,
    Finset.prod_div_distrib, Finset.prod_const, hs, RoughCoprimeFactor.card_divisors_eq hn]
  congr 1
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- Expanding every reciprocal prime correction produces a full divisor
majorant. The divisor-square weight retains all shared prime combinations. -/
theorem inverse_product_le_divisor_sum {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {n : ℕ} (hn : Squarefree n) :
    (∏ p ∈ n.primeFactors, ‖(1 + zetaPrimeFeature s p)⁻¹‖) ≤
      ∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ 2 / Real.sqrt d := by
  have he := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p ↦ 4 / Real.sqrt p)).prodPrimeFactors_one_add_of_squarefree hn
  have hp (p : ℕ) (hp : p ∈ n.primeFactors) :
      localMajorant p = 4 / Real.sqrt p := by
    rw [localMajorant, ArithmeticFunction.prodPrimeFactors_apply
      (Nat.prime_of_mem_primeFactors hp).ne_zero,
      (Nat.prime_of_mem_primeFactors hp).primeFactors, Finset.prod_singleton]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (1 + 4 / Real.sqrt p) :=
      Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
        (fun _ hp ↦ norm_inverse_local_le hs (Nat.prime_of_mem_primeFactors hp))
    _ = ∏ p ∈ n.primeFactors, (1 + localMajorant p) :=
      Finset.prod_congr rfl (fun p hp' ↦ by rw [hp p hp'])
    _ = ∑ d ∈ n.divisors, localMajorant d := he
    _ = _ := Finset.sum_congr rfl (fun d hd ↦
      localMajorant_eq (hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)))

/-- Each actual squarefree Euler atom keeps its inverse-square-root scale
and the entire reciprocal-factor divisor correction. -/
theorem norm_atom_le_divisor_sum {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {n : ℕ} (hn : Squarefree n) :
    ‖SquarefreeEulerQuadratic.atom s n‖ ≤
      (1 / Real.sqrt n) * ∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ 2 / Real.sqrt d := by
  rw [SquarefreeEulerQuadratic.atom_eq_feature_product hn, norm_mul, norm_prod]
  exact mul_le_mul (norm_zetaPrimeFeature_le_inv_sqrt hs (Nat.pos_of_ne_zero hn.ne_zero))
    (inverse_product_le_divisor_sum hs hn) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
    (by positivity)

/-- Averaging the complete divisor correction costs only a square root of
the cutoff; its constant is a genuinely convergent divisor-square series. -/
theorem sum_divisor_majorant_le (U : ℕ) :
    (∑ n ∈ Finset.Icc 1 U, (1 / Real.sqrt n) *
      ∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ 2 / Real.sqrt d) ≤
      2 * Real.sqrt U * divisorSquareDirichletMass (3 / 2) := by
  let w : ℕ → ℝ := fun d ↦ (d.divisors.card : ℝ) ^ 2 / Real.sqrt d
  have hdiv (n : ℕ) (hn : n ∈ Finset.Icc 1 U) :
      (∑ d ∈ n.divisors, w d) =
        ∑ d ∈ Finset.Icc 1 U, if d ∣ n then w d else 0 := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    calc
      _ = ∑ d ∈ n.divisors, if d ∣ n then w d else 0 :=
        Finset.sum_congr rfl (fun d hd ↦ (if_pos (Nat.dvd_of_mem_divisors hd)).symm)
      _ = _ := Finset.sum_subset (fun d hd ↦ Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans
          (Finset.mem_Icc.mp hn).2⟩) (by
        intro d _ hd
        have hnot : ¬d ∣ n := fun h ↦ hd (Nat.mem_divisors.mpr ⟨h, hn0⟩)
        simp [hnot])
  have he : (∑ n ∈ Finset.Icc 1 U, (1 / Real.sqrt n) * ∑ d ∈ n.divisors, w d) =
      ∑ d ∈ Finset.Icc 1 U, w d *
        ∑ n ∈ Finset.Icc 1 U, if d ∣ n then 1 / Real.sqrt n else 0 := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
          w d * (if d ∣ n then 1 / Real.sqrt n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hdiv n hn, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
  have hw (d : ℕ) (hd : d ∈ Finset.Icc 1 U) :
      w d / d = (d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hs0 : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
    have hexp : (1 / Real.sqrt d) / d = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      calc
        _ = Real.exp (-(Real.log d + Real.log (Real.sqrt d))) := by
          rw [Real.exp_neg, Real.exp_add, Real.exp_log hd0, Real.exp_log hs0]
          ring
        _ = _ := by
          rw [Real.log_sqrt hd0.le, Real.rpow_def_of_pos hd0]
          congr 1
          ring
    rw [← hexp]
    dsimp [w]
    ring
  change (∑ n ∈ Finset.Icc 1 U, (1 / Real.sqrt n) * ∑ d ∈ n.divisors, w d) ≤ _
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U, w d * (2 * Real.sqrt U / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_dvd_inv_sqrt_le (Finset.mem_Icc.mp hd).1 U) (by dsimp [w]; positivity)
    _ = 2 * Real.sqrt U * ∑ d ∈ Finset.Icc 1 U,
        (d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← hw d hd]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ) < 3 / 2)).sum_le_tsum _
        (fun d _ ↦ by positivity)) (by positivity)

/-- The full squarefree marked Euler mass has a uniform square-root
prefix bound on the closed half-plane, without a pointwise epsilon loss. -/
theorem sum_squarefree_norm_atom_le (U : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (∑ n ∈ (Finset.Icc 1 U).filter Squarefree, ‖SquarefreeEulerQuadratic.atom s n‖) ≤
      2 * Real.sqrt U * divisorSquareDirichletMass (3 / 2) := by
  apply le_trans (Finset.sum_le_sum (fun n hn ↦ norm_atom_le_divisor_sum hs
    (Finset.mem_filter.mp hn).2))
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun n _ _ ↦ by positivity))
  exact sum_divisor_majorant_le U

/-- An ordinary prime mark retains its actual inverse square-root weight. -/
theorem norm_prime_atom_le {s : ℂ} (hs : 1 / 2 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖SquarefreeEulerQuadratic.atom s p‖ ≤ 4 / Real.sqrt p := by
  have ht := prime_sqrt_lower hp
  have ht0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hi : ‖(1 + zetaPrimeFeature s p)⁻¹‖ ≤ 4 := by
    apply (norm_inverse_local_le hs hp).trans
    have hdiv : 4 / Real.sqrt (p : ℝ) ≤ 3 := (div_le_iff₀ ht0).mpr (by linarith)
    linarith
  rw [SquarefreeEulerQuadratic.atom_eq_feature_product hp.squarefree,
    hp.primeFactors, Finset.prod_singleton, norm_mul]
  exact (mul_le_mul (norm_zetaPrimeFeature_le_inv_sqrt hs hp.pos) hi
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Actual Chebyshev prime density pays for the logarithmic prime mark. -/
theorem sum_prime_log_norm_atom_le (V : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (∑ p ∈ zetaSquarePrimesThrough V, Real.log p * ‖SquarefreeEulerQuadratic.atom s p‖) ≤
      12 * Real.sqrt V := by
  calc
    _ ≤ ∑ p ∈ zetaSquarePrimesThrough V, 4 * (Real.log p / Real.sqrt p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      exact (mul_le_mul_of_nonneg_left (norm_prime_atom_le hs hprime)
        (Real.log_natCast_nonneg p)).trans_eq (by ring)
    _ = 4 * ∑ p ∈ zetaSquarePrimesThrough V, Real.log p / Real.sqrt p :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_prime_log_inv_sqrt_le V)
      (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

/-- The full coprime squarefree--prime prefix, with the original complex
weight and the phase of the entire product at every entry. -/
def coprimePrefix (U V : ℕ) (w : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 U).filter Squarefree, ∑ p ∈ zetaSquarePrimesThrough V,
    if a.Coprime p then w a * (Real.log p : ℂ) * SquarefreeEulerQuadratic.atom s (a * p) else 0

/-- The exact coprime prefix has a square-root product bound. The
coprimality restriction is retained in its definition and charged only here. -/
theorem norm_prefix_le (U V : ℕ) (w : ℕ → ℂ)
    (hw : ∀ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖w a‖ ≤ 1)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖coprimePrefix U V w s‖ ≤
      24 * divisorSquareDirichletMass (3 / 2) * Real.sqrt U * Real.sqrt V := by
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 U).filter Squarefree,
        ‖SquarefreeEulerQuadratic.atom s a‖ *
          ∑ p ∈ zetaSquarePrimesThrough V, Real.log p * ‖SquarefreeEulerQuadratic.atom s p‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      by_cases hcop : a.Coprime p
      · rw [if_pos hcop, (SquarefreeEulerQuadratic.atom_multiplicative s).map_mul_of_coprime hcop,
          norm_mul, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
        have h := mul_le_mul_of_nonneg_right (hw a ha)
          (show 0 ≤ Real.log p * (‖SquarefreeEulerQuadratic.atom s a‖ *
            ‖SquarefreeEulerQuadratic.atom s p‖) by positivity)
        nlinarith only [h]
      · rw [if_neg hcop, norm_zero]
        positivity
    _ ≤ ∑ a ∈ (Finset.Icc 1 U).filter Squarefree,
        ‖SquarefreeEulerQuadratic.atom s a‖ * (12 * Real.sqrt V) :=
      Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (sum_prime_log_norm_atom_le V hs) (norm_nonneg _))
    _ = (∑ a ∈ (Finset.Icc 1 U).filter Squarefree,
        ‖SquarefreeEulerQuadratic.atom s a‖) * (12 * Real.sqrt V) := (Finset.sum_mul ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_right (sum_squarefree_norm_atom_le U hs)
      (by positivity : 0 ≤ 12 * Real.sqrt (V : ℝ))).trans_eq (by ring)

private theorem atom_eq_multiplier {n : ℕ} (hn : Squarefree n) (s : ℂ) :
    SquarefreeEulerQuadratic.atom s n = squarefreeEulerMultiplier ∅ n s := by
  symm
  simpa using SquarefreeEulerQuadratic.multiplier_eq ∅ hn (by simp) s

/-- The exact prefix is analytic throughout the positive half-plane;
the reciprocal local denominators are proved nonzero there. -/
theorem analyticAt_prefix (U V : ℕ) (w : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (coprimePrefix U V w) s := by
  apply Finset.analyticAt_fun_sum
  intro a ha
  apply Finset.analyticAt_fun_sum
  intro p hp
  by_cases hcop : a.Coprime p
  · simp only [if_pos hcop]
    have hsf : Squarefree (a * p) := (Nat.squarefree_mul hcop).mpr
      ⟨(Finset.mem_filter.mp ha).2, (show p.Prime from (Finset.mem_filter.mp hp).2).squarefree⟩
    have he : (fun z ↦ SquarefreeEulerQuadratic.atom z (a * p)) =
        squarefreeEulerMultiplier ∅ (a * p) := funext (atom_eq_multiplier hsf)
    apply analyticAt_const.mul
    rw [he]
    exact analyticAt_squarefreeEulerMultiplier ∅ (by simp) (a * p) hs
  · simp only [if_neg hcop]
    exact analyticAt_const

private theorem re_half_of_mem_unit_disc {y : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) 1) : 1 / 2 ≤ s.re := by
  have hre := Complex.abs_re_le_norm (s - (3 / 2 + I * y))
  rw [Metric.mem_closedBall, dist_eq_norm] at hs
  have h := (abs_le.mp (hre.trans hs)).1
  norm_num at h
  linarith

/-- A unit-circle Cauchy bound for every bounded analytic multiplier of
the actual squarefree quotient, with one constant for the fixed ordinate. -/
theorem exists_unit_multiplier_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall (3 / 2 + I * y) 1) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ s ∈ Metric.closedBall (3 / 2 + I * y) 1, ‖f s‖ ≤ A) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
          (fun s ↦ f s * squarefreeEulerResponse s) (3 / 2 + I * y)) N‖ ≤
          C * A * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  let c : ℂ := 3 / 2 + I * y
  have hQ : AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall c 1) :=
    (analyticOnNhd_squarefreeEulerResponse hy).mono
      (Metric.closedBall_subset_closedBall (squarefreeEulerRadius_bounds hy).1.le)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c 1).image_of_continuousOn
    hQ.continuousOn.norm).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨c, Metric.mem_closedBall_self (by norm_num), rfl⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  intro f hf A hA hfA p N
  have ha : AnalyticOnNhd ℂ (fun s ↦ f s * squarefreeEulerResponse s) (Metric.closedBall c 1) :=
    fun s hs ↦ (hf s hs).mul (hQ s hs)
  have hd : DiffContOnCl ℂ (fun s ↦ f s * squarefreeEulerResponse s) (Metric.ball c 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact ha.differentiableOn
  have hb (s : ℂ) (hs : s ∈ Metric.sphere c 1) :
      ‖f s * squarefreeEulerResponse s‖ ≤ (M + 1) * A := by
    have hsB := Metric.sphere_subset_closedBall hs
    have hbound := hM _ ⟨s, hsB, rfl⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hbound
    rw [norm_mul]
    have h := mul_le_mul (hfA s hsB) (show ‖squarefreeEulerResponse s‖ ≤ M + 1 by linarith)
      (norm_nonneg _) hA
    simpa only [mul_comm] using h
  have hmoment (k : ℕ) :
      ‖signedTaylorMoment k (fun s ↦ f s * squarefreeEulerResponse s) c‖ ≤ (M + 1) * A := by
    simpa using norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 1) hd hb k
  rw [zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((M + 1) * A) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmoment (N + k)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The complete filtered coprime prefix has the same square-root
product budget as the larger-cutoff Vaughan decomposition. -/
theorem exists_prefix_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V : ℕ) (w : ℕ → ℂ),
      (∀ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖w a‖ ≤ 1) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
          (fun s ↦ coprimePrefix U V w s * squarefreeEulerResponse s) (3 / 2 + I * y)) N‖ ≤
          C * ZetaVaughanCutoffBudget.budget U V * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_unit_multiplier_filter_bound y hy
  let M := divisorSquareDirichletMass (3 / 2)
  have hM : 0 ≤ M := divisorSquareDirichletMass_nonneg _
  refine ⟨C * (24 * M + 1), by positivity, ?_⟩
  intro U V w hw p N
  have hf : AnalyticOnNhd ℂ (coprimePrefix U V w) (Metric.closedBall (3 / 2 + I * y) 1) := by
    intro s hs
    exact analyticAt_prefix U V w (by linarith [re_half_of_mem_unit_disc hs])
  have hB : Real.sqrt U * Real.sqrt V ≤ ZetaVaughanCutoffBudget.budget U V := by
    unfold ZetaVaughanCutoffBudget.budget
    gcongr <;> linarith
  have h := hb (coprimePrefix U V w) hf (24 * M * Real.sqrt U * Real.sqrt V)
    (by positivity) (fun s hs ↦ norm_prefix_le U V w hw (re_half_of_mem_unit_disc hs)) p N
  apply h.trans
  have hcost : C * (24 * M * Real.sqrt U * Real.sqrt V) ≤
      C * (24 * M + 1) * ZetaVaughanCutoffBudget.budget U V := by
    have hb0 := (ZetaVaughanCutoffBudget.budget_pos U V).le
    nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ C * (24 * M) by positivity)]
  exact mul_le_mul_of_nonneg_right hcost (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))

/-- The literal squarefree divisibility coefficient of the coprime prefix. -/
def coprimeCoefficient (U V : ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 U).filter Squarefree,
    ∑ p ∈ (zetaSquarePrimesThrough V).filter (fun p ↦ a.Coprime p),
      (w a * (Real.log p : ℂ)) * RoughSquarefreeBare.coefficient ∅ (a * p) n

/-- Absolute convergence identifies the exact finite marked sum with its
analytic prefix times the genuine squarefree Euler quotient. -/
theorem LSeriesHasSum_coprimeCoefficient (U V : ℕ) (w : ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (coprimeCoefficient U V w) s
      (coprimePrefix U V w s * squarefreeEulerResponse s) := by
  have hm (a : ℕ) (ha : a ∈ (Finset.Icc 1 U).filter Squarefree)
      (p : ℕ) (hp : p ∈ (zetaSquarePrimesThrough V).filter (fun p ↦ a.Coprime p)) :
      LSeriesHasSum (RoughSquarefreeBare.coefficient ∅ (a * p)) s
        (SquarefreeEulerQuadratic.atom s (a * p) * squarefreeEulerResponse s) := by
    have hsf : Squarefree (a * p) := (Nat.squarefree_mul (Finset.mem_filter.mp hp).2).mpr
      ⟨(Finset.mem_filter.mp ha).2,
        (show p.Prime from (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2).squarefree⟩
    rw [atom_eq_multiplier hsf]
    exact LSeriesHasSum_markedSquarefreeEuler ∅ (by simp) hsf (by simp) hs
  have h := LSeriesHasSum.sum (S := (Finset.Icc 1 U).filter Squarefree) (fun a ha ↦
    LSeriesHasSum.sum (S := (zetaSquarePrimesThrough V).filter (fun p ↦ a.Coprime p))
      (fun p hp ↦ (hm a ha p hp).smul (w a * (Real.log p : ℂ))))
  convert h using 1
  · funext n
    simp only [coprimeCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [coprimePrefix, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring

/-- Every factorial moment is the actual convergent arithmetic moment. -/
theorem hasSum_coprime_moment (U V : ℕ) (w : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ coprimeCoefficient U V w n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N (fun z ↦ coprimePrefix U V w z * squarefreeEulerResponse z) s) := by
  have hab : LSeries.abscissaOfAbsConv (coprimeCoefficient U V w) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_coprimeCoefficient U V w (by simpa using hy)).LSeriesSummable
  have he : (fun z ↦ coprimePrefix U V w z * squarefreeEulerResponse z) =ᶠ[𝓝 s]
      LSeries (coprimeCoefficient U V w) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_coprimeCoefficient U V w hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _
    (by simp [coprimeCoefficient, RoughSquarefreeBare.coefficient])
    (lt_of_le_of_lt hab (by exact_mod_cast hs)) N

/-- Every fixed polynomial filter preserves the complete coefficient
and all complex phases through the genuine convergent-series identity. -/
theorem hasSum_coprime_filter (U V : ℕ) (w : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coprimeCoefficient U V w n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
        (fun z ↦ coprimePrefix U V w z * squarefreeEulerResponse z) s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_coprime_moment U V w (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

private theorem truncated_divisor_sum (f : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) (U : ℕ) :
    (∑ d ∈ n.divisors, if d ≤ U then f d else 0) =
      ∑ d ∈ Finset.Icc 1 U, if d ∣ n then f d else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · exact fun h ↦ ⟨⟨Nat.pos_of_dvd_of_pos h.1.1 (Nat.pos_of_ne_zero hn), h.2⟩, h.1.1⟩
  · exact fun h ↦ ⟨⟨h.2, hn⟩, h.1.2⟩

private theorem prime_prefix_divisor_sum (V : ℕ) {n : ℕ} (hn : Squarefree n) :
    (ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
      ∑ p ∈ zetaSquarePrimesThrough V, if p ∣ n then Real.log p else 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change (∑ d ∈ n.divisors,
    if d ≤ V then ArithmeticFunction.vonMangoldt d else 0) = _
  rw [truncated_divisor_sum _ hn.ne_zero, zetaSquarePrimesThrough, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hdvd : p ∣ n
  · have hsf := hn.squarefree_of_dvd hdvd
    by_cases hp : p.Prime
    · simp [hdvd, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · have hnot : ¬IsPrimePow p := fun h ↦ hp
        (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf, h⟩)
      simp [hdvd, hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot]
  · simp [hdvd]

/-- The marked coefficient is exactly the squarefree projection of the
truncated convolution, for every original real arithmetic weight. -/
theorem coprimeCoefficient_eq_projected_convolution (U V : ℕ)
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    coprimeCoefficient U V (fun a ↦ (f a : ℂ)) n =
      if Squarefree n then ((ZetaVaughanReduction.head U f *
        ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℂ) else 0 := by
  by_cases hn : Squarefree n
  · rw [if_pos hn]
    have hconv : (ZetaVaughanReduction.head U f *
        ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
        ∑ a ∈ Finset.Icc 1 U, if a ∣ n then f a *
          ∑ p ∈ zetaSquarePrimesThrough V, if p ∣ n / a then Real.log p else 0 else 0 := by
      rw [mul_assoc, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
        (fun a b ↦ ZetaVaughanReduction.head U f a *
          (ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) b)]
      have hsum : (∑ a ∈ n.divisors, ZetaVaughanReduction.head U f a *
          (ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (n / a)) =
          ∑ a ∈ n.divisors, if a ≤ U then f a *
            ∑ p ∈ zetaSquarePrimesThrough V, if p ∣ n / a then Real.log p else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [prime_prefix_divisor_sum V (hn.squarefree_of_dvd
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha)))]
        simp only [ZetaVaughanReduction.head, ArithmeticFunction.coe_mk, ite_mul, zero_mul]
      rw [hsum, truncated_divisor_sum _ hn.ne_zero]
    rw [hconv, Complex.ofReal_sum]
    simp only [coprimeCoefficient, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∣ n
    · have hsf := hn.squarefree_of_dvd ha
      simp only [if_pos hsf, if_pos ha, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have hd : p ∣ n / a ↔ a * p ∣ n := by
        simpa only [Nat.mul_comm] using Nat.dvd_div_iff_mul_dvd ha
      by_cases hap : a * p ∣ n
      · have hc := Nat.coprime_of_squarefree_mul (hn.squarefree_of_dvd hap)
        simp [RoughSquarefreeBare.coefficient, hn, hap, hc, hd]
      · simp [RoughSquarefreeBare.coefficient, hn, hap, hd]
    · have hno (p : ℕ) : ¬a * p ∣ n := fun h ↦ ha ((dvd_mul_right a p).trans h)
      simp [ha, RoughSquarefreeBare.coefficient, hn, hno]
  · simp [coprimeCoefficient, RoughSquarefreeBare.coefficient, hn]

/-- The full squarefree Vaughan cross term has an independently
vanishing normalized filter for every pair of paid moving cutoffs. -/
theorem tendsto_projected_cross_of_budget (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (U V : ℕ → ℕ)
    (hbudget : Tendsto (fun N ↦ u ^ (N + 1) * ZetaVaughanCutoffBudget.budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑' n,
      (if Squarefree n then ((ZetaVaughanReduction.head (U N) (μ : ArithmeticFunction ℝ) *
        ZetaVaughanReduction.head (V N) ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℂ) else 0) *
            zetaPrimeFilterKernel p N (3 / 2 + I * y) n) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_prefix_filter_bound y hy
  have hw (a : ℕ) : ‖((μ : ArithmeticFunction ℝ) a : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    change |((μ a : ℤ) : ℝ)| ≤ 1
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  apply squeeze_zero_norm (fun N ↦ ?_) (by
    simpa only [mul_zero] using hbudget.const_mul (C * S))
  simp_rw [← coprimeCoefficient_eq_projected_convolution]
  rw [(hasSum_coprime_filter (U N) (V N) (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ))
    p N (by norm_num)).tsum_eq, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hu.le]
  exact (mul_le_mul_of_nonneg_left (hb (U N) (V N) _ (fun a _ ↦ hw a) p N)
    (by positivity)).trans_eq (by ring)

/-- In particular the actual projected cross term decays at both of
the new larger cutoffs floor(u^(-N)/(N+1)). -/
theorem tendsto_projected_cross_linearDampedCutoff (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑' n,
      (if Squarefree n then ((ZetaVaughanReduction.head
        (ZetaVaughanCutoffBudget.linearDampedCutoff u N) (μ : ArithmeticFunction ℝ) *
          ZetaVaughanReduction.head (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
            ArithmeticFunction.vonMangoldt * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℂ)
        else 0) * zetaPrimeFilterKernel p N (3 / 2 + I * y) n) atTop (𝓝 0) :=
  tendsto_projected_cross_of_budget p y hy hu _ _
    (ZetaVaughanCutoffBudget.tendsto_budget_linearDampedCutoff hu hu1)

/-- Squarefree projection of a truncated logarithmic convolution keeps
the exact physical logarithm minus the divisor logarithm. -/
theorem projected_head_log_eq (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    (if Squarefree n then ((ZetaVaughanReduction.head U f * ArithmeticFunction.log) n : ℂ)
      else 0) = ∑ a ∈ Finset.Icc 1 U, (f a : ℂ) *
        RoughSquarefreeBare.coefficient ∅ a n * ((Real.log n : ℂ) - (Real.log a : ℂ)) := by
  by_cases hn : Squarefree n
  · rw [if_pos hn, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b ↦ ZetaVaughanReduction.head U f a * ArithmeticFunction.log b)]
    simp only [ZetaVaughanReduction.head, ArithmeticFunction.coe_mk,
      ArithmeticFunction.log_apply, ite_mul, zero_mul]
    rw [truncated_divisor_sum _ hn.ne_zero, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hd : a ∣ n
    · have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
      have hlog : Real.log (n / a : ℕ) = Real.log n - Real.log a := by
        rw [Nat.cast_div hd (by exact_mod_cast ha0.ne'),
          Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast ha0.ne')]
      simp only [if_pos hd, hlog, Complex.ofReal_mul, Complex.ofReal_sub]
      simp [RoughSquarefreeBare.coefficient, hn, hd]
    · simp [RoughSquarefreeBare.coefficient, hn, hd]
  · simp [RoughSquarefreeBare.coefficient, hn]

private theorem summable_bare_all (p : Polynomial ℂ) (a N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ RoughSquarefreeBare.coefficient ∅ a n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_squarefreeEuler_filter p N hs).summable.indicator {n | a ∣ n}
  apply h.congr
  intro n
  by_cases hd : a ∣ n <;> simp [Set.indicator, RoughSquarefreeBare.coefficient, hd]

/-- The full projected logarithmic convolution has an exact convergent
sum of its logged and unlogged marked responses. -/
theorem hasSum_projected_head_log (U : ℕ) (f : ArithmeticFunction ℝ)
    (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (if Squarefree n then
      ((ZetaVaughanReduction.head U f * ArithmeticFunction.log) n : ℂ) else 0) *
        zetaPrimeFilterKernel p N s n)
      (∑ a ∈ Finset.Icc 1 U, (f a : ℂ) *
        (SquarefreeEulerLog.response p ∅ a N s - (Real.log a : ℂ) *
          RoughSquarefreeBare.response p ∅ a N s)) := by
  have h := hasSum_sum (s := Finset.Icc 1 U) (fun a _ ↦
    (((SquarefreeEulerLog.summable_response p ∅ (by simp) a N hs).hasSum).sub
      ((summable_bare_all p a N hs).hasSum.mul_left (Real.log a : ℂ))).mul_left (f a : ℂ))
  apply h.congr_fun
  intro n
  rw [projected_head_log_eq, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun a _ ↦ by ring)

private theorem moebius_norm_le_one (a : ℕ) :
    ‖((μ : ArithmeticFunction ℝ) a : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |((μ a : ℤ) : ℝ)| ≤ 1
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)

/-- The independently analytic marked quotient pays for the full
projected Möbius--log term, including every divisor logarithm. -/
theorem exists_projected_head_log_bound (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ U N : ℕ,
      ‖∑' n, (if Squarefree n then
        ((ZetaVaughanReduction.head U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n : ℂ)
        else 0) * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
          C * U * (N + 1 + Real.log (U + 1 : ℝ)) * (squarefreeEulerRadius y)⁻¹ ^ N := by
  obtain ⟨K, _, C, hC, hb⟩ := exists_squarefreeEuler_uniform_mark_filter_bound y hy
  let r := (squarefreeEulerRadius y)⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (by linarith [(squarefreeEulerRadius_bounds hy).1])
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (squarefreeEulerRadius_bounds hy).1.le
  let S : ℝ := ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hplain : (∑ k ∈ p.support, ‖p.coeff k‖) ≤ S := by
    apply Finset.sum_le_sum
    intro k _
    nlinarith [norm_nonneg (p.coeff k), Nat.cast_nonneg (α := ℝ) k]
  have hbare (a N : ℕ) : ‖RoughSquarefreeBare.response p ∅ a N (3 / 2 + I * y)‖ ≤
      C * r ^ N * S := by
    have h := hb ∅ (by simp) a p N
    simp only [Finset.card_empty, pow_zero, mul_one] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_trans _ hplain
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0 hr1)
  have hlog (a N : ℕ) : ‖SquarefreeEulerLog.response p ∅ a N (3 / 2 + I * y)‖ ≤
      C * r ^ N * ((N + 1 : ℝ) * S) := by
    rw [SquarefreeEulerLog.response_eq_raised]
    have h := hb ∅ (by simp) a (Polynomial.X * SquarefreeEulerLog.raisedPolynomial p N) N
    simp only [Finset.card_empty, pow_zero, mul_one] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_trans _ (SquarefreeEulerLog.raisedPolynomial_envelope_le p N)
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0 hr1)
  refine ⟨C * (S + 1), by positivity, ?_⟩
  intro U N
  rw [(hasSum_projected_head_log U (μ : ArithmeticFunction ℝ) p N (by norm_num)).tsum_eq]
  calc
    _ ≤ ∑ _a ∈ Finset.Icc 1 U,
        C * (S + 1) * (N + 1 + Real.log (U + 1 : ℝ)) * r ^ N := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right (moebius_norm_le_one a) (norm_nonneg _)).trans
      rw [one_mul]
      apply (norm_sub_le _ _).trans
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
      have hla : Real.log a ≤ Real.log (U + 1 : ℝ) :=
        Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp ha).1)
          (by exact_mod_cast (Finset.mem_Icc.mp ha).2.trans (Nat.le_succ U))
      have hlu : 0 ≤ Real.log (U + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) U])
      have h := add_le_add (hlog a N)
        (mul_le_mul hla (hbare a N) (norm_nonneg _) hlu)
      have hpow : 0 ≤ r ^ N := pow_nonneg hr0 N
      nlinarith [mul_nonneg hC.le (mul_nonneg hpow
        (show 0 ≤ (N : ℝ) + 1 + Real.log (U + 1 : ℝ) by positivity))]
    _ = _ := by simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

/-- The complete projected logarithmic convolution decays independently
even up to the undamped inverse-source cutoff. -/
theorem tendsto_projected_head_log (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (U : ℕ → ℕ)
    (hU : ∀ N, (U N : ℝ) ≤ u⁻¹ ^ N) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑' n,
      (if Squarefree n then ((ZetaVaughanReduction.head (U N) (μ : ArithmeticFunction ℝ) *
        ArithmeticFunction.log) n : ℂ) else 0) * zetaPrimeFilterKernel p N (3 / 2 + I * y) n)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_projected_head_log_bound p y hy
  let r := (squarefreeEulerRadius y)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (by linarith [(squarefreeEulerRadius_bounds hy).1])
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (squarefreeEulerRadius_bounds hy).1
  have hui : 1 ≤ u⁻¹ := by simpa only [one_div] using (one_le_div hu).mpr hu1.le
  have hlogu : 0 ≤ Real.log u⁻¹ := Real.log_nonneg hui
  have hlog (N : ℕ) : (N + 1 : ℝ) + Real.log (U N + 1 : ℝ) ≤
      (N + 1 : ℝ) * (2 + Real.log u⁻¹) := by
    have hpow : 1 ≤ u⁻¹ ^ N := one_le_pow₀ hui
    have hsum : (U N + 1 : ℝ) ≤ 2 * u⁻¹ ^ N := by linarith [hU N]
    have h := Real.log_le_log (by positivity : 0 < (U N + 1 : ℝ)) hsum
    rw [Real.log_mul (by norm_num) (pow_pos (inv_pos.mpr hu) N).ne', Real.log_pow] at h
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpaid (N : ℕ) : u ^ (N + 1) * (U N : ℝ) ≤ u := by
    calc
      _ ≤ u ^ (N + 1) * u⁻¹ ^ N := mul_le_mul_of_nonneg_left (hU N) (by positivity)
      _ = _ := by rw [pow_succ, inv_pow]; field_simp
  have hlin : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) * r ^ N) atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one hr hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1)
    simpa only [zero_add, add_mul, one_mul] using h
  apply squeeze_zero_norm (fun N ↦ ?_) (by
    simpa only [mul_zero] using hlin.const_mul (C * u * (2 + Real.log u⁻¹)))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * U N * (N + 1 + Real.log (U N + 1 : ℝ)) * r ^ N) :=
      mul_le_mul_of_nonneg_left (hb (U N) N) (by positivity)
    _ = C * (u ^ (N + 1) * U N) * (N + 1 + Real.log (U N + 1 : ℝ)) * r ^ N := by ring
    _ ≤ C * u * ((N + 1 : ℝ) * (2 + Real.log u⁻¹)) * r ^ N := by
      have hnonneg : 0 ≤ (N + 1 : ℝ) + Real.log (U N + 1 : ℝ) :=
        add_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (U N)]))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left (hpaid N) hC.le) (hlog N) hnonneg
          (mul_nonneg hC.le hu.le)) (pow_nonneg hr N)
    _ = _ := by ring

/-- Literal projection to squarefree physical integers. -/
def squarefreePart (f : ArithmeticFunction ℝ) (n : ℕ) : ℂ :=
  if Squarefree n then (f n : ℂ) else 0

/-- The finite ordinary-prime part of the truncated Vaughan head. -/
def primePrefixFilter (V : ℕ) (p : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ zetaSquarePrimesThrough V, (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n

/-- Squarefree projection removes exactly the proper prime powers from
the literal von Mangoldt coefficient. -/
theorem squarefree_vonMangoldt_eq (n : ℕ) :
    squarefreePart ArithmeticFunction.vonMangoldt n =
      (ArithmeticFunction.vonMangoldt n : ℂ) - (zetaProperPrimePowerCoefficient n : ℂ) := by
  by_cases hp : n.Prime
  · simp [squarefreePart, hp.squarefree, zetaProperPrimePowerCoefficient, hp]
  · by_cases hn : Squarefree n
    · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (show ¬IsPrimePow n from
        fun h ↦ hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, h⟩))
      simp [squarefreePart, hn, hz, zetaProperPrimePowerCoefficient, hp]
    · simp [squarefreePart, hn, zetaProperPrimePowerCoefficient, hp]

/-- The projected finite head is a genuine finite ordinary-prime sum. -/
theorem hasSum_projected_head_prime (V : ℕ) (p : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    HasSum (fun n ↦ squarefreePart (ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt) n *
      zetaPrimeFilterKernel p N s n) (primePrefixFilter V p N s) := by
  have hc (n : ℕ) : squarefreePart (ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt) n =
      if n ∈ zetaSquarePrimesThrough V then (Real.log n : ℂ) else 0 := by
    by_cases hp : n.Prime
    · by_cases hV : n ≤ V <;>
        simp [squarefreePart, hp.squarefree, ZetaVaughanReduction.head,
          zetaSquarePrimesThrough, hp, hp.one_lt.le, hV, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · have hz : squarefreePart ArithmeticFunction.vonMangoldt n = 0 := by
        rw [squarefree_vonMangoldt_eq]
        simp [zetaProperPrimePowerCoefficient, hp]
      by_cases hn : Squarefree n
      · simp only [squarefreePart, if_pos hn] at hz
        simp [squarefreePart, hn, ZetaVaughanReduction.head, zetaSquarePrimesThrough, hp,
          Complex.ofReal_eq_zero.mp hz]
      · simp [squarefreePart, hn, zetaSquarePrimesThrough, hp]
  simp_rw [hc]
  have h : HasSum (fun n ↦ (if n ∈ zetaSquarePrimesThrough V then (Real.log n : ℂ) else 0) *
      zetaPrimeFilterKernel p N s n)
      (∑ n ∈ zetaSquarePrimesThrough V,
        (if n ∈ zetaSquarePrimesThrough V then (Real.log n : ℂ) else 0) * zetaPrimeFilterKernel p N s n) :=
    hasSum_sum_of_ne_finset_zero (s := zetaSquarePrimesThrough V)
    (f := fun n ↦ (if n ∈ zetaSquarePrimesThrough V then (Real.log n : ℂ) else 0) *
      zetaPrimeFilterKernel p N s n) (by intro n hn; simp [hn])
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos hn]

/-- The finite projected head keeps the square-root prime-density cost
uniformly in the factorial order and the ordinate. -/
theorem norm_primePrefixFilter_le (V : ℕ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖primePrefixFilter V p N (3 / 2 + I * y)‖ ≤
      3 * Real.sqrt V * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  let S := ∑ k ∈ p.support, ‖p.coeff k‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  calc
    _ ≤ ∑ n ∈ zetaSquarePrimesThrough V, (Real.log n / Real.sqrt n) * S := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have hp : n.Prime := (Finset.mem_filter.mp hn).2
      have hk := norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * y) (x := (n : ℝ))
        (by exact_mod_cast hp.one_lt.le) (by norm_num : (0 : ℝ) < 1)
      norm_num at hk
      have hf := norm_zetaPrimeFeature_le_inv_sqrt (s := (1 / 2 : ℂ)) (by norm_num) hp.pos
      rw [norm_zetaPrimeFeature, zetaPrimeExpWeight] at hf
      norm_num at hf
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      exact (mul_le_mul_of_nonneg_left
        (hk.trans (mul_le_mul_of_nonneg_right hf hS)) (Real.log_natCast_nonneg n)).trans_eq (by ring)
    _ = (∑ n ∈ zetaSquarePrimesThrough V, Real.log n / Real.sqrt n) * S := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_prime_log_inv_sqrt_le V) hS

/-- Any paid square-root product budget also pays the finite projected head. -/
theorem tendsto_projected_head_prime_of_budget (p : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (U V : ℕ → ℕ)
    (hbudget : Tendsto (fun N ↦ u ^ (N + 1) * ZetaVaughanCutoffBudget.budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * primePrefixFilter (V N) p N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  let S := ∑ k ∈ p.support, ‖p.coeff k‖
  apply squeeze_zero_norm (fun N ↦ ?_) (by
    simpa only [mul_zero] using hbudget.const_mul (3 * S))
  have hB : Real.sqrt (V N) ≤ ZetaVaughanCutoffBudget.budget (U N) (V N) := by
    have h1 : 1 ≤ Real.sqrt (U N + 1 : ℝ) :=
      Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) (U N)])
    have hv := Real.sqrt_le_sqrt (show (V N : ℝ) ≤ V N + 1 by linarith)
    unfold ZetaVaughanCutoffBudget.budget
    nlinarith [Real.sqrt_nonneg (V N), Real.sqrt_nonneg (V N + 1 : ℝ)]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  have hS : 0 ≤ S := by dsimp [S]; positivity
  exact ((mul_le_mul_of_nonneg_left (norm_primePrefixFilter_le (V N) p N y)
    (by positivity)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 3)) hS)
        (by positivity))).trans_eq (by ring)

/-- The entire projected Vaughan small part, with its original three
signs, is a genuinely convergent arithmetic filter. -/
theorem hasSum_projected_small (U V : ℕ) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ squarefreePart (ZetaVaughanReduction.small U V) n * zetaPrimeFilterKernel p N s n)
      (primePrefixFilter V p N s +
        zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.head U
          (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)) p N s -
        zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.head U
          (μ : ArithmeticFunction ℝ) * ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) p N s) := by
  have hc := hasSum_coprime_filter U V (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ)) p N hs
  simp_rw [coprimeCoefficient_eq_projected_convolution] at hc
  have h := ((hasSum_projected_head_prime V p N s).add
    (hasSum_projected_head_log U (μ : ArithmeticFunction ℝ) p N hs).summable.hasSum).sub
      hc.summable.hasSum
  apply h.congr_fun
  intro n
  by_cases hn : Squarefree n
  · simp only [squarefreePart, if_pos hn]
    change ((ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt n +
      (ZetaVaughanReduction.head U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n -
      (ZetaVaughanReduction.head U (μ : ArithmeticFunction ℝ) *
        ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * _ = _
    push_cast
    ring
  · simp [squarefreePart, hn]

/-- The complete projected small part decays at both larger Vaughan
cutoffs. Each arithmetic component has an independently proved allowance. -/
theorem tendsto_projected_small_linearDampedCutoff (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * zetaArithmeticFilter
      (squarefreePart (ZetaVaughanReduction.small (D N) (D N))) p N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
  have hD (N : ℕ) : (D N : ℝ) ≤ u⁻¹ ^ N := by
    apply (Nat.floor_le (by positivity : 0 ≤ u⁻¹ ^ N / (N + 1 : ℝ))).trans
    exact div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hp := tendsto_projected_head_prime_of_budget p y hu D D
    (ZetaVaughanCutoffBudget.tendsto_budget_linearDampedCutoff hu hu1)
  have hl := tendsto_projected_head_log p y hy hu hu1 D hD
  have hc := tendsto_projected_cross_linearDampedCutoff p y hy hu hu1
  have h := (hp.add hl).sub hc
  simp only [zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaArithmeticFilter, (hasSum_projected_small (D N) (D N) p N (by norm_num)).tsum_eq]
  dsimp only [zetaArithmeticFilter, squarefreePart, D] at *
  ring

private theorem hasSum_proper_filter (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ) * zetaPrimeFilterKernel p N s n)
      (zetaProperPrimePowerFilter p N s) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (summable_zetaProperPrimePowerMoment (N + k) (s := s) (by linarith)).hasSum.mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

/-- The squarefree projection of the actual bilinear coefficient has
its complete, convergent Vaughan identity, with every correction retained. -/
theorem hasSum_projected_bilinear (U V : ℕ) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ squarefreePart (ZetaVaughanReduction.bilinear U V) n *
      zetaPrimeFilterKernel p N s n)
      (zetaPrimeLogFilter p N s - zetaProperPrimePowerFilter p N s -
        zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.small U V)) p N s) := by
  have hprime : HasSum (fun n ↦ squarefreePart ArithmeticFunction.vonMangoldt n *
      zetaPrimeFilterKernel p N s n) (zetaPrimeLogFilter p N s - zetaProperPrimePowerFilter p N s) := by
    have h := (hasSum_zetaPrimeLogFilter hs p N).sub (hasSum_proper_filter p N hs)
    apply h.congr_fun
    intro n
    rw [squarefree_vonMangoldt_eq, zetaPrimeFilterKernel_nat]
    ring
  have h := hprime.sub (hasSum_projected_small U V p N hs).summable.hasSum
  apply h.congr_fun
  intro n
  by_cases hn : Squarefree n
  · simp only [squarefreePart, if_pos hn]
    have he := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) (ZetaVaughanReduction.vaughan U V)
    rw [ArithmeticFunction.add_apply] at he
    rw [he, Complex.ofReal_add]
    ring
  · simp [squarefreePart, hn]

/-- The entire nonsquarefree part of the actual bilinear response is
independently negligible at the larger cutoffs, for every fixed filter and
eligible ordinate. This theorem assumes no zeta zero. -/
theorem tendsto_nonsquarefree_bilinear (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      (zetaArithmeticFilter (fun n ↦ (ZetaVaughanReduction.bilinear (D N) (D N) n : ℂ))
        p N (3 / 2 + I * y) -
      zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N)))
        p N (3 / 2 + I * y))) atTop (𝓝 0) := by
  let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p y (a := (u : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)
  have hsf := tendsto_projected_small_linearDampedCutoff p y hy hu hu1
  have hsmall := ZetaVaughanCutoffBudget.tendsto_smallFilter_of_budget p y hy hu D D
    (ZetaVaughanCutoffBudget.tendsto_budget_linearDampedCutoff hu hu1)
  have h := (hp.add hsf).sub hsmall
  simp only [zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [zetaArithmeticFilter]
  rw [(ZetaVaughanReduction.hasSum_responseFilter p (D N) (D N) N
      (s := 3 / 2 + I * y) (by norm_num)).tsum_eq,
    (hasSum_projected_bilinear (D N) (D N) p N (s := 3 / 2 + I * y) (by norm_num)).tsum_eq,
    ZetaVaughanReduction.filter_identity p (D N) (D N) N (by norm_num)]
  simp only [zetaArithmeticFilter]
  ring

/-- At a hypothetical right-half zero, the squarefree projection
retains the original negative-multiplicity source at the larger cutoffs. -/
theorem tendsto_actual_squarefree_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let D := ZetaVaughanCutoffBudget.linearDampedCutoff (3 / 2 - rho.1.re)
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticFilter
      (squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N)))
        (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p rho.1.im (a := (u : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)
  have hs := tendsto_projected_small_linearDampedCutoff p rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu hu1
  dsimp only [u, p] at hp hs
  push_cast at hp hs
  have h := ((tendsto_zetaRightHalfPoleJetFilter rho hrho).sub hp).sub hs
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [zetaArithmeticFilter]
  rw [(hasSum_projected_bilinear _ _ _ _ (s := 3 / 2 + I * rho.1.im) (by norm_num)).tsum_eq]
  simp only [zetaArithmeticFilter]
  push_cast
  ring

/-- The original finite band can be restricted to squarefree integers
with the full signed source unchanged. Its independent lower bound is open. -/
theorem tendsto_actual_squarefree_band (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let D := ZetaVaughanCutoffBudget.linearDampedCutoff (3 / 2 - rho.1.re)
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
      (squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N)))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hb (N n : ℕ) : ‖squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N)) n‖ ≤
      zetaMoebiusLogMajorant n := by
    by_cases hn : Squarefree n
    · simpa only [squarefreePart, if_pos hn] using ZetaVaughanReduction.norm_bilinear_le (D N) (D N) n
    · simpa only [squarefreePart, if_neg hn, norm_zero] using zetaMoebiusLogMajorant_nonneg n
  have herr := tendsto_zetaDominatedFilter_sub_band
    (fun N ↦ squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N))) hb p rho.1.im
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have he := hpow.mul herr
  simp only [mul_zero] at he
  dsimp only [u, D, p] at he
  push_cast at he
  have h := (tendsto_actual_squarefree_source rho hrho).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- Every nonsquarefree physical integer in the original finite band
is removed with an independently vanishing signed total at the larger
cutoffs. This is uniform over the full band, not a fixed finite prefix. -/
theorem tendsto_nonsquarefree_band (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑ n ∈ zetaPrimeLogBand N,
      if Squarefree n then 0 else (ZetaVaughanReduction.bilinear (D N) (D N) n : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n) atTop (𝓝 0) := by
  let D := ZetaVaughanCutoffBudget.linearDampedCutoff u
  have hb (N n : ℕ) : ‖squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N)) n‖ ≤
      zetaMoebiusLogMajorant n := by
    by_cases hn : Squarefree n
    · simpa only [squarefreePart, if_pos hn] using ZetaVaughanReduction.norm_bilinear_le (D N) (D N) n
    · simpa only [squarefreePart, if_neg hn, norm_zero] using zetaMoebiusLogMajorant_nonneg n
  have hfull := tendsto_zetaDominatedFilter_sub_band
    (fun N n ↦ (ZetaVaughanReduction.bilinear (D N) (D N) n : ℂ))
      (fun N ↦ ZetaVaughanReduction.norm_bilinear_le (D N) (D N)) p y
  have hsf := tendsto_zetaDominatedFilter_sub_band
    (fun N ↦ squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N))) hb p y
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_nonsquarefree_bilinear p y hy hu hu1).sub (hpow.mul (hfull.sub hsf))
  simp only [sub_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he : (∑ n ∈ zetaPrimeLogBand N,
      if Squarefree n then 0 else (ZetaVaughanReduction.bilinear (D N) (D N) n : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n) =
      zetaArithmeticBand (fun n ↦ (ZetaVaughanReduction.bilinear (D N) (D N) n : ℂ)) p N y -
        zetaArithmeticBand (squarefreePart (ZetaVaughanReduction.bilinear (D N) (D N))) p N y := by
    rw [zetaArithmeticBand, zetaArithmeticBand, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Squarefree n <;> simp [squarefreePart, hn]
  rw [he]
  ring

end
end RiemannGaussian.SquarefreeVaughanProjection
