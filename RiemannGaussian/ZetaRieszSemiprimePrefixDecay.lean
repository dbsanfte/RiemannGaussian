/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimePrefix

/-!
# All-scale decay of the actual semiprime prefix

The physical prime-prefix allowance tends to zero for every 0<u<1,
including the contact of the older smooth-cofactor estimate. The exact
two-prime tent bounds the actual coefficient and its completion error
with the same two-logarithm budget. Arbitrary pair masks are permitted
in this finite prefix; no masked infinite-prime cancellation is assumed.
-/

namespace RiemannGaussian.ZetaRieszSemiprimePrefixDecay
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor
open ZetaRieszSemiprimePrefix

/-- The logarithmic prime-prefix factor is absorbed by the damped
inverse-order and geometric allowances at every source scale below one. -/
theorem tendsto_prime_prefix_bracket {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) *
      (u / (N + 1) + 2 * u ^ (N + 1))) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_zero, pow_one, one_mul] using (Real.tendsto_pow_log_div_mul_add_atTop 1 1 0 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun N : ℕ => Real.log N / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_zero, pow_one, one_mul] using (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun N : ℕ => u ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1).comp (tendsto_add_atTop_nat 1)
  have hn : Tendsto (fun N : ℕ => (N : ℝ) * u ^ (N + 1)) atTop (𝓝 0) := by
    convert (tendsto_self_mul_const_pow_of_lt_one hu.le hu1).mul_const u using 1
    · funext N
      rw [pow_succ]
      ring
    · simp
  have hlg : Tendsto (fun N : ℕ => Real.log N * u ^ (N + 1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N =>
      mul_nonneg (Real.log_natCast_nonneg N) (pow_nonneg hu.le _))) ?_ hn
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)
    exact mul_le_mul_of_nonneg_right (by linarith : Real.log N ≤ (N : ℝ)) (pow_nonneg hu.le _)
  have hlim : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * u +
      (Real.log N / ((N : ℝ) + 1)) * (2 * u / Real.log 2) +
      u ^ (N + 1) * 2 + (Real.log N * u ^ (N + 1)) * (4 / Real.log 2)) atTop (𝓝 0) := by
    simpa using (((hi.mul_const u).add (hl.mul_const (2 * u / Real.log 2))).add
      (hp.mul_const 2)).add (hlg.mul_const (4 / Real.log 2))
  convert hlim using 1
  funext N
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  ring

/-- The exact physical prime-prefix allowance tends to zero. Its
linear-length proof uses the actual integer floor, including at the scalar
contact which obstructed the older unrestricted smooth-cofactor bound. -/
theorem tendsto_physical_prime_prefix_allowance (P : Polynomial ℂ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ =>
      (9 * (∑ k ∈ P.support, ‖P.coeff k‖) / SquarefreeVaughanLogSource.length u N *
        (1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) * N) *
          (u / (N + 1) + 2 * u ^ (N + 1))) atTop (𝓝 0) := by
  obtain ⟨c, hc, hlength⟩ := eventually_linear_length_lower hu hu1
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hlim := (tendsto_prime_prefix_bracket hu hu1).const_mul (9 * S / c)
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hlim)
  · exact Filter.Eventually.of_forall (fun N => by
      have hL := (SquarefreeVaughanLogSource.length_pos u N).le
      have hlog := Real.log_natCast_nonneg (N ^ 2)
      positivity)
  · filter_upwards [hlength] with N hL
    have hratio : (N : ℝ) / SquarefreeVaughanLogSource.length u N ≤ 1 / c := by
      apply (div_le_div_iff₀ (SquarefreeVaughanLogSource.length_pos u N) hc).mpr
      simpa only [one_mul, mul_comm] using hL
    have hbr : 0 ≤ (1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) *
        (u / (N + 1) + 2 * u ^ (N + 1)) := by
      have hlog := Real.log_natCast_nonneg (N ^ 2)
      positivity
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (show 0 ≤ 9 * S by positivity)) hbr
    calc
      _ = (9 * S * ((N : ℝ) / SquarefreeVaughanLogSource.length u N)) *
          ((1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) *
            (u / (N + 1) + 2 * u ^ (N + 1))) := by
        change (9 * S / _ * _ * _) * _ = _
        ring
      _ ≤ (9 * S * (1 / c)) * ((1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) *
          (u / (N + 1) + 2 * u ^ (N + 1))) := h
      _ = _ := by ring

/-- Every dominated physical prime-pair prefix vanishes independently,
with arbitrary pair masks, all original factorial coefficients and no zero
hypothesis. Only its explicit pointwise coefficient bound is required. -/
theorem tendsto_physical_prime_prefix (S T : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ N ^ 2)
    (hT : ∀ N p, p ∈ T N → p.Prime ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (f : ℕ → ℕ → ℕ → ℂ)
    (hf : ∀ N a, a ∈ S N → ∀ p ∈ T N, ‖f N a p‖ ≤
      Real.log a * Real.log ((a * p : ℕ) : ℝ) / SquarefreeVaughanLogSource.length u N) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ a ∈ S N, ∑ p ∈ T N,
      f N a p * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)) atTop (𝓝 0) := by
  exact squeeze_zero_norm (fun N => norm_physical_prime_prefix_le (S N) (T N) P N y hu
    (hS N) (hT N) (f N) (hf N)) (tendsto_physical_prime_prefix_allowance P hu hu1)

/-- The coefficient of the genuinely completed prime/cofactor sum.
It agrees with the actual semiprime coefficient above the physical cutoff. -/
def completedPairCoefficient (L : ℝ) (a p : ℕ) : ℂ :=
  ((-Real.log ((a * p : ℕ) : ℝ) * Real.log a / L : ℝ) : ℂ)

/-- The completed mark has exactly the two logarithms needed for
the independent prime-prefix bound. -/
theorem norm_completedPairCoefficient {L : ℝ} (hL : 0 < L) (a p : ℕ) :
    ‖completedPairCoefficient L a p‖ = Real.log a * Real.log ((a * p : ℕ) : ℝ) / L := by
  simp only [completedPairCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_mul, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg _), abs_of_pos hL]
  ring

/-- The exact semiprime profile is its two-prime tent; both cutoff
boundaries and both prime logarithms remain explicit. -/
theorem riesz_semiprime_eq_tent (L : ℝ) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hne : a ≠ p) :
    VaughanLogAverage.riesz L (a * p) =
      ZetaSquarefreeRieszWindows.primePairTent (Real.log a) (Real.log p) L := by
  simpa using ZetaSquarefreeRieszWindows.riesz_two_primes_eq_tent L ha hp hne
    (show ¬ a ∣ 1 by simpa using ha.ne_one) (show ¬ p ∣ 1 by simpa using hp.ne_one)

/-- At every cutoff the distinct-prime profile is nonnegative and
bounded by the small prime's logarithm. No saturation assumption is needed. -/
theorem riesz_semiprime_bounds (L : ℝ) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hne : a ≠ p) :
    0 ≤ VaughanLogAverage.riesz L (a * p) ∧ VaughanLogAverage.riesz L (a * p) ≤ Real.log a := by
  rw [riesz_semiprime_eq_tent L ha hp hne]
  have h := ZetaSquarefreeRieszWindows.primePairTent_bounds
    (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg p) L
  exact ⟨h.1, h.2.trans (min_le_left _ _)⟩

/-- The actual Riesz semiprime coefficient obeys the prime-prefix
mark bound at every positive length; a repeated prime is deleted exactly. -/
theorem norm_actual_semiprime_coefficient_le {L : ℝ} (hL : 0 < L)
    {a p : ℕ} (ha : a.Prime) (hp : p.Prime) :
    ‖SquarefreeVaughanLogSource.coefficient L (a * p)‖ ≤
      Real.log a * Real.log ((a * p : ℕ) : ℝ) / L := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · have hne : a ≠ p := by
      intro h
      have hcop := Nat.coprime_of_squarefree_mul hn.1
      rw [h, Nat.coprime_self] at hcop
      exact hp.ne_one hcop
    have hr := riesz_semiprime_bounds L ha hp hne
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
      abs_of_nonneg (Real.log_natCast_nonneg _), abs_of_nonneg hr.1, abs_of_pos hL]
    exact div_le_div_of_nonneg_right
      (by nlinarith [Real.log_natCast_nonneg (a * p)]) hL.le
  · simp only [norm_zero]
    positivity

/-- The completion error also fits the same two-logarithm budget;
its signs are compared before a norm is taken. -/
theorem norm_semiprime_completion_error_le {L : ℝ} (hL : 0 < L)
    {a p : ℕ} (ha : a.Prime) (hp : p.Prime) :
    ‖SquarefreeVaughanLogSource.coefficient L (a * p) - completedPairCoefficient L a p‖ ≤
      Real.log a * Real.log ((a * p : ℕ) : ℝ) / L := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · have hne : a ≠ p := by
      intro h
      have hcop := Nat.coprime_of_squarefree_mul hn.1
      rw [h, Nat.coprime_self] at hcop
      exact hp.ne_one hcop
    have hr := riesz_semiprime_bounds L ha hp hne
    have he : ((-Real.log ((a * p : ℕ) : ℝ) * VaughanLogAverage.riesz L (a * p) / L : ℝ) : ℂ) -
        completedPairCoefficient L a p =
        ((Real.log ((a * p : ℕ) : ℝ) * (Real.log a - VaughanLogAverage.riesz L (a * p)) / L : ℝ) : ℂ) := by
      simp only [completedPairCoefficient, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_sub]
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (mul_nonneg (Real.log_natCast_nonneg (a * p))
        (sub_nonneg.mpr hr.2)) hL.le)]
    exact div_le_div_of_nonneg_right
      (by nlinarith [Real.log_natCast_nonneg (a * p)]) hL.le
  · simpa only [zero_sub, norm_neg, norm_completedPairCoefficient hL] using
      le_refl (Real.log a * Real.log ((a * p : ℕ) : ℝ) / L)

/-- The literal Riesz coefficient has independently vanishing physical
prime-prefix response at every scale below one. Every pair mask is allowed. -/
theorem tendsto_actual_semiprime_prefix (S T : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ N ^ 2)
    (hT : ∀ N p, p ∈ T N → p.Prime ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (keep : ℕ → ℕ → ℕ → Prop) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ a ∈ S N, ∑ p ∈ T N,
      (if keep N a p then SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) (a * p) else 0) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)) atTop (𝓝 0) := by
  apply tendsto_physical_prime_prefix S T P y hu hu1 hS hT
  intro N a ha p hp
  split_ifs
  · exact norm_actual_semiprime_coefficient_le (SquarefreeVaughanLogSource.length_pos u N)
      (hS N a ha).1 (hT N p hp).1
  · simp only [norm_zero]
    exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg (a * p)))
      (SquarefreeVaughanLogSource.length_pos u N).le

/-- The difference from the completed coefficient also vanishes on
the entire physical prime prefix, independently of zeros and of pair masks. -/
theorem tendsto_semiprime_completion_prefix_error (S T : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ N ^ 2)
    (hT : ∀ N p, p ∈ T N → p.Prime ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (keep : ℕ → ℕ → ℕ → Prop) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ a ∈ S N, ∑ p ∈ T N,
      (if keep N a p then SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) (a * p) -
          completedPairCoefficient (SquarefreeVaughanLogSource.length u N) a p else 0) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)) atTop (𝓝 0) := by
  apply tendsto_physical_prime_prefix S T P y hu hu1 hS hT
  intro N a ha p hp
  split_ifs
  · exact norm_semiprime_completion_error_le (SquarefreeVaughanLogSource.length_pos u N)
      (hS N a ha).1 (hT N p hp).1
  · simp only [norm_zero]
    exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg (a * p)))
      (SquarefreeVaughanLogSource.length_pos u N).le

end
end RiemannGaussian.ZetaRieszSemiprimePrefixDecay
