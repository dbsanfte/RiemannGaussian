/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMultiplierRadiusBound
import RiemannGaussian.ZetaMoebiusLcmBound

/-!
# Genuine divisor-prefix responses at variable radii

The signed finite prefix has its actual convergent arithmetic series for
every positive divisibility factor, including prime powers and one.
Keeping an exponent strictly past one half controls square-factor sums.
The logarithmic companion is paid by a smaller positive exponent margin;
the exact two-channel response is unchanged.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- The negative signed divisor prefix on multiples of an arbitrary
positive factor. It is defined independently of the prime-power leakage. -/
def zetaDivisibilityPrefixCoefficient (D P : ℕ) : ℕ → ℂ :=
  -(∑ d ∈ Finset.Icc 1 D, (μ d : ℂ) • zetaMultipleLogCoefficient d P)

/-- Divisibility restricts the unchanged signed prefix coefficient
pointwise, before any convergence theorem or norm is used. -/
theorem zetaDivisibilityPrefixCoefficient_eq_indicator (D P n : ℕ) :
    zetaDivisibilityPrefixCoefficient D P n =
      if P ∣ n then zetaDivisibilityPrefixCoefficient D 1 n else 0 := by
  by_cases h : P ∣ n <;>
    simp [zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, h]

/-- The true logarithmic Möbius tail is its complete von Mangoldt
coefficient plus the negative finite prefix. Prime-power leakage is
explicitly retained, including the zero and unit indices. -/
theorem zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix (D n : ℕ) :
    zetaMoebiusLogTailCoefficient D n =
      (ArithmeticFunction.vonMangoldt n : ℂ) + zetaDivisibilityPrefixCoefficient D 1 n := by
  by_cases hn : n = 0
  · simp [hn, zetaMoebiusLogTailCoefficient, zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient]
  have hfull : (∑ a ∈ n.divisorsAntidiagonal, (μ a.1 : ℂ) * (Real.log a.2 : ℂ)) =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
    have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply] at h
    exact_mod_cast h
  have he : n.divisors.filter (fun d ↦ d ≤ D) = (Finset.Icc 1 D).filter (fun d ↦ d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hD⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn), hD⟩, hd⟩
    · tauto
  have hsplit : zetaMoebiusLogTailCoefficient D n +
      (∑ d ∈ n.divisors, if d ≤ D then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) =
        (ArithmeticFunction.vonMangoldt n : ℂ) := by
    rw [zetaMoebiusLogTailCoefficient_divisors, ← Finset.sum_add_distrib]
    rw [Nat.sum_divisorsAntidiagonal (fun d k ↦ (μ d : ℂ) * (Real.log k : ℂ))] at hfull
    convert hfull using 1
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ≤ D <;> simp [hd]
  rw [← Finset.sum_filter, he, Finset.sum_filter] at hsplit
  have hp : zetaDivisibilityPrefixCoefficient D 1 n =
      -(∑ d ∈ Finset.Icc 1 D, if d ∣ n then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) := by
    simp [zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, mul_ite]
  rw [hp]
  linear_combination hsplit

/-- The original least-common-multiple response is the convergent
series of this literal prefix for every positive factor, including one
and prime powers. No mixed-prime hypothesis is required for the prefix. -/
theorem LSeriesHasSum_zetaDivisibilityPrefix (D : ℕ) {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaDivisibilityPrefixCoefficient D P) s (zetaMoebiusMultipleResponse D P s) := by
  unfold zetaDivisibilityPrefixCoefficient
  have h := (LSeriesHasSum.sum (S := Finset.Icc 1 D) (fun d hd ↦
    (LSeriesHasSum_zetaMultipleLogCoefficient (Finset.mem_Icc.mp hd).1 hP hs).smul (μ d : ℂ))).neg
  convert h using 1
  unfold zetaMoebiusMultipleResponse zetaMoebiusMultipleDerivativeMultiplier
    zetaMoebiusMultipleValueMultiplier
  simp only [neg_mul, ← neg_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The genuine complete polynomial-filter series of every positive
divisibility prefix agrees with its existing analytic moment response. -/
theorem hasSum_zetaDivisibilityPrefixFilter (p : Polynomial ℂ) (D N : ℕ)
    {P : ℕ} (hP : 0 < P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaDivisibilityPrefixCoefficient D P n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusMultipleFilter p D P N s) := by
  have ha : LSeries.abscissaOfAbsConv (zetaDivisibilityPrefixCoefficient D P) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_zetaDivisibilityPrefix D hP (by simpa using hy)).LSeriesSummable
  have he : zetaMoebiusMultipleResponse D P =ᶠ[𝓝 s]
      LSeries (zetaDivisibilityPrefixCoefficient D P) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_zetaDivisibilityPrefix D hP hz).LSeries_eq.symm
  have hm (k : ℕ) : HasSum (fun n ↦ zetaDivisibilityPrefixCoefficient D P n *
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment k (zetaMoebiusMultipleResponse D P) s) := by
    rw [signedTaylorMoment_congr k he]
    exact hasSum_signedTaylorMoment_LSeries _ (by simp [zetaDivisibilityPrefixCoefficient,
      zetaMultipleLogCoefficient]) (lt_of_le_of_lt ha (by exact_mod_cast hs)) k
  have h := hasSum_sum (s := p.support) (fun k _ ↦ (hm (N + k)).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every positive exponent margin gives a decaying factor weight for
both genuine entire multipliers. The complete logarithmic displacement
costs only the inverse margin, independently of the selected factor. -/
theorem norm_zetaMoebiusMultipleMultipliers_le_expWeight (D : ℕ) {P : ℕ} (hP : 0 < P)
    {σ τ : ℝ} (hτ : 0 ≤ τ) (hgap : τ < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖zetaMoebiusMultipleDerivativeMultiplier D P s‖ ≤ D * zetaPrimeExpWeight τ P ∧
      ‖zetaMoebiusMultipleValueMultiplier D P s‖ ≤
        D * (σ - τ)⁻¹ * zetaPrimeExpWeight τ P := by
  have hm (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hw (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      ‖zetaPrimeFeature s (Nat.lcm d P)‖ ≤ zetaPrimeExpWeight σ P := by
    rw [norm_zetaPrimeFeature]
    apply Real.exp_le_exp.mpr
    have hL : Real.log P ≤ Real.log (Nat.lcm d P) :=
      Real.log_le_log (by exact_mod_cast hP)
        (by exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 hP) (Nat.dvd_lcm_right d P))
    have hlog := Real.log_natCast_nonneg (Nat.lcm d P)
    nlinarith
  have hshift : zetaPrimeExpWeight σ P ≤ zetaPrimeExpWeight τ P := by
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_natCast_nonneg P
    nlinarith
  have hlog : zetaPrimeExpWeight σ P * Real.log P ≤ (σ - τ)⁻¹ * zetaPrimeExpWeight τ P := by
    have h := logMoment_exp_envelope 1 (Real.log_natCast_nonneg P) (sub_pos.mpr hgap) σ
    simpa only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, sub_sub_cancel,
      mul_comm (Real.log P), zetaPrimeExpWeight] using h
  constructor
  · rw [zetaMoebiusMultipleDerivativeMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, zetaPrimeExpWeight τ P := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        exact (mul_le_mul (hm d) ((hw d hd).trans hshift) (norm_nonneg _)
          (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp
  · rw [zetaMoebiusMultipleValueMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (σ - τ)⁻¹ * zetaPrimeExpWeight τ P := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (zetaMultipleLogOffset_bounds (Finset.mem_Icc.mp hd).1 hP).1]
        calc
          _ ≤ zetaPrimeExpWeight σ P * Real.log P := by
            apply mul_le_mul
            · exact (mul_le_mul (hm d) (hw d hd) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
            · exact zetaMultipleLogOffset_le_log_factor (Finset.mem_Icc.mp hd).1 hP
            · exact (zetaMultipleLogOffset_bounds (Finset.mem_Icc.mp hd).1 hP).1
            · exact (Real.exp_pos _).le
          _ ≤ _ := hlog
      _ = _ := by simp; ring

/-- A Cauchy radius below one leaves this strictly larger exponent
than one half after paying the complete logarithmic companion. -/
def zetaSquareSieveExponent (r : ℝ) : ℝ := 1 - r / 2

/-- The exponent margin is positive for every admissible radius. -/
theorem zetaSquareSieveExponent_gt_half {r : ℝ} (hr : r < 1) :
    1 / 2 < zetaSquareSieveExponent r := by
  unfold zetaSquareSieveExponent
  linarith

/-- The genuine factor response has a uniform decaying factor weight
at every fixed Cauchy radius below one. Both original response channels
and the entire polynomial filter are covered. -/
theorem exists_zetaDivisibilityPrefixFilter_expWeight_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ), 0 < P →
      ‖zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)‖ ≤
        C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) *
          zetaPrimeExpWeight (zetaSquareSieveExponent r) P := by
  let σ : ℝ := 3 / 2 - r
  let τ := zetaSquareSieveExponent r
  have hτ : 0 ≤ τ := (show 0 < (1 / 2 : ℝ) by norm_num).le.trans
    (zetaSquareSieveExponent_gt_half hr1).le
  have hgap : τ < σ := by dsimp [τ, σ, zetaSquareSieveExponent]; linarith
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_radius_filter_bound y hy
  refine ⟨C * (1 + (σ - τ)⁻¹), by positivity, fun p D P N hP ↦ ?_⟩
  obtain ⟨hf, hg⟩ := differentiable_zetaMoebiusMultipleMultipliers D P
  have h := hb r hr hr1.le _ _ hf hg
    (D * zetaPrimeExpWeight τ P) (D * (σ - τ)⁻¹ * zetaPrimeExpWeight τ P)
    (by unfold zetaPrimeExpWeight; positivity) (by unfold zetaPrimeExpWeight; positivity)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_expWeight D hP hτ hgap hs).1)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_expWeight D hP hτ hgap hs).2) p N
  exact h.trans_eq (by ring)

end
end RiemannGaussian
