/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailMoments

/-!
# Finite complex Dirichlet multipliers and exact index dilation

Finite Dirichlet polynomials are entire and have their coefficient mass
as a bound on the closed right half-plane. Their genuine L-series values,
and the exact dilation of arbitrary convergent coefficients, retain the
zero-index conditions explicitly.
-/

open Complex
open scoped Classical LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- A finite coefficient family with its actual support retained. -/
def zetaFiniteCoefficient (S : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ S then a n else 0

/-- The full complex finite Dirichlet polynomial. -/
def zetaFiniteDirichletSeries (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * zetaPrimeFeature s n

/-- The finite polynomial is entire, with no restriction on its coefficients. -/
theorem differentiable_zetaFiniteDirichletSeries (S : Finset ℕ) (a : ℕ → ℂ) :
    Differentiable ℂ (zetaFiniteDirichletSeries S a) := by
  unfold zetaFiniteDirichletSeries zetaPrimeFeature
  fun_prop

/-- Every natural-index feature is at most one on the closed right half-plane. -/
theorem norm_zetaPrimeFeature_le_one {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖zetaPrimeFeature s n‖ ≤ 1 := by
  rw [norm_zetaPrimeFeature, zetaPrimeExpWeight]
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.log_natCast_nonneg n]

/-- The signed coefficients keep their exact finite mass until this
downstream bound, uniform on the whole closed right half-plane. -/
theorem norm_zetaFiniteDirichletSeries_le (S : Finset ℕ) (a : ℕ → ℂ)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaFiniteDirichletSeries S a s‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_zetaPrimeFeature_le_one hs n) (norm_nonneg _)).trans_eq
    (mul_one _)

/-- The actual Dirichlet term equals its exponential feature when
the exceptional zero coefficient has been discharged. -/
theorem LSeries_term_eq_zetaPrimeFeature (a : ℕ → ℂ) (ha0 : a 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term a s n = a n * zetaPrimeFeature s n := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · rw [LSeries.term_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log,
      div_eq_mul_inv, ← Complex.exp_neg, zetaPrimeFeature]
    congr 2
    ring

/-- The finite polynomial is a genuinely convergent L-series at every
complex argument. No singular zero-index term is introduced. -/
theorem LSeriesHasSum_zetaFiniteCoefficient (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : 0 ∉ S) (s : ℂ) :
    LSeriesHasSum (zetaFiniteCoefficient S a) s (zetaFiniteDirichletSeries S a s) := by
  have ha0 : zetaFiniteCoefficient S a 0 = 0 := if_neg hS
  have h : HasSum (LSeries.term (zetaFiniteCoefficient S a) s)
      (∑ n ∈ S, LSeries.term (zetaFiniteCoefficient S a) s n) :=
    hasSum_sum_of_ne_finset_zero (s := S)
    (f := LSeries.term (zetaFiniteCoefficient S a) s) (by
      intro n hn
      rw [LSeries_term_eq_zetaPrimeFeature _ ha0, zetaFiniteCoefficient, if_neg hn, zero_mul])
  have he : (∑ n ∈ S, LSeries.term (zetaFiniteCoefficient S a) s n) =
      zetaFiniteDirichletSeries S a s := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries_term_eq_zetaPrimeFeature _ ha0, zetaFiniteCoefficient, if_pos hn]
  exact he ▸ h

/-- A finitely supported coefficient is identified with its original
finite prefix, rather than merely with a totalized infinite sum. -/
theorem LSeriesHasSum_of_support_Icc (a : ℕ → ℂ) (D : ℕ) (ha0 : a 0 = 0)
    (hD : ∀ n, D < n → a n = 0) (s : ℂ) :
    LSeriesHasSum a s (zetaFiniteDirichletSeries (Finset.Icc 1 D) a s) := by
  have he : zetaFiniteCoefficient (Finset.Icc 1 D) a = a := by
    funext n
    by_cases hn : n ∈ Finset.Icc 1 D
    · exact if_pos hn
    · rw [zetaFiniteCoefficient, if_neg hn]
      by_cases hn0 : n = 0
      · simp [hn0, ha0]
      · exact (hD n (by have hn' := hn; simp only [Finset.mem_Icc] at hn'; omega)).symm
  have h := LSeriesHasSum_zetaFiniteCoefficient (Finset.Icc 1 D) a (by simp) s
  rwa [he] at h

/-- Logarithmic weights satisfy the exact convolution product rule,
retaining both signed terms before taking L-series or estimates. -/
theorem convolution_mul_natLog (a b : ℕ → ℂ) :
    (fun n ↦ (a ⍟ b) n * (Real.log n : ℂ)) =
      (fun n ↦ a n * (Real.log n : ℂ)) ⍟ b +
        a ⍟ (fun n ↦ b n * (Real.log n : ℂ)) := by
  funext n
  simp only [Pi.add_apply, LSeries.convolution_def, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hj
  rw [← (Nat.mem_divisorsAntidiagonal.mp hj).1, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hj0.1) (by exact_mod_cast hj0.2)]
  simp only [Complex.ofReal_add]
  ring

/-- The ordinary logarithmic sequence has its genuine derivative-zeta value. -/
theorem LSeriesHasSum_natLog {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (Real.log n : ℂ)) s (-deriv riemannZeta s) := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  have h := hm.convolution (LSeriesHasSum_one hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one,
    div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re hs)] at h
  simpa only [← Complex.natCast_log] using h

/-- Exact dilation of a coefficient sequence onto multiples of `P`. -/
def zetaDilationCoefficient (P : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if P ∣ n then a (n / P) else 0

/-- Dilation is convolution with one atom; at factor zero both sides
vanish because the zero coefficient is explicitly discharged. -/
theorem zetaDilationCoefficient_eq_convolution (P : ℕ)
    (a : ℕ → ℂ) (ha0 : a 0 = 0) :
    zetaDilationCoefficient P a = zetaFiniteCoefficient {P} (fun _ ↦ (1 : ℂ)) ⍟ a := by
  funext n
  by_cases hn : n = 0
  · simp [hn, zetaDilationCoefficient, ha0]
  · simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal
      (fun d r ↦ zetaFiniteCoefficient {P} (fun _ ↦ (1 : ℂ)) d * a r)]
    simp [zetaFiniteCoefficient, ite_mul, Finset.sum_ite_eq', Nat.mem_divisors, hn,
      zetaDilationCoefficient]

/-- Dilation preserves absolute convergence and the complete complex
Dirichlet phase, multiplying the value by the feature at `P`. -/
theorem LSeriesHasSum_zetaDilationCoefficient {P : ℕ} (hP : 0 < P)
    {a : ℕ → ℂ} (ha0 : a 0 = 0) {s v : ℂ} (ha : LSeriesHasSum a s v) :
    LSeriesHasSum (zetaDilationCoefficient P a) s (zetaPrimeFeature s P * v) := by
  rw [zetaDilationCoefficient_eq_convolution P a ha0]
  have hp := LSeriesHasSum_zetaFiniteCoefficient {P} (fun _ ↦ (1 : ℂ)) (by simpa using hP.ne) s
  simpa only [zetaFiniteDirichletSeries, Finset.sum_singleton, one_mul] using hp.convolution ha

end
end RiemannGaussian
