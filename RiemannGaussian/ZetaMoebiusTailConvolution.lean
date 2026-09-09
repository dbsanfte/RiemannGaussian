/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusPoleJetFilter
import RiemannGaussian.ZetaReciprocalDirichlet
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# The literal large-divisor Möbius convolution

The complement of the finite Möbius head is an absolutely convergent
Dirichlet convolution, with every divisor cutoff and complex phase kept.
Its coefficients vanish on primes and below twice the first retained
divisor. After the complete pole jet is cancelled, this moving composite
carrier retains the full selected-zero source.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The actual Möbius coefficients through the divisor cutoff, including
the harmless zero coefficient at index zero. -/
def zetaMoebiusHeadCoefficient (D n : ℕ) : ℂ :=
  if n ≤ D then (μ n : ℂ) else 0

/-- The complementary actual Möbius coefficients, with a strict cutoff. -/
def zetaMoebiusTailCoefficient (D n : ℕ) : ℂ :=
  if D < n then (μ n : ℂ) else 0

/-- The finite head and strict tail partition each signed coefficient. -/
theorem zetaMoebiusTailCoefficient_eq_sub (D : ℕ) :
    zetaMoebiusTailCoefficient D = (fun n ↦ (μ n : ℂ)) - zetaMoebiusHeadCoefficient D := by
  funext n
  by_cases hn : n ≤ D <;> simp [zetaMoebiusTailCoefficient, zetaMoebiusHeadCoefficient, hn]

private theorem head_term (D : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (zetaMoebiusHeadCoefficient D) s n =
      if n ≤ D then LSeries.term (fun m ↦ (μ m : ℂ)) s n else 0 := by
  by_cases hn : n ≤ D <;> simp [LSeries.term, zetaMoebiusHeadCoefficient, hn]

/-- The finite exponential prefix is precisely the convergent Dirichlet
series of the truncated Möbius coefficients, at every complex argument. -/
theorem LSeriesHasSum_zetaMoebiusHeadCoefficient (D : ℕ) (s : ℂ) :
    LSeriesHasSum (zetaMoebiusHeadCoefficient D) s (zetaMoebiusDirichletHead D s) := by
  have h : HasSum (LSeries.term (zetaMoebiusHeadCoefficient D) s)
      (∑ n ∈ Finset.range (D + 1), LSeries.term (zetaMoebiusHeadCoefficient D) s n) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range (D + 1))
    (f := LSeries.term (zetaMoebiusHeadCoefficient D) s) (by
      intro n hn
      rw [head_term, if_neg (by simpa using hn)])
  have he : (∑ n ∈ Finset.range (D + 1), LSeries.term (zetaMoebiusHeadCoefficient D) s n) =
      zetaMoebiusDirichletHead D s := by
    rw [Finset.sum_range_succ']
    simp only [LSeries.term_zero, add_zero, zetaMoebiusDirichletHead]
    apply Finset.sum_congr rfl
    intro n hn
    rw [head_term, if_pos (by simpa using hn), moebius_LSeries_term_eq_exp s (Nat.succ_ne_zero n)]
    congr 2
    ring
  exact he ▸ h

/-- The strict Möbius tail converges to the actual reciprocal minus
its finite prefix throughout the Euler half-plane. -/
theorem LSeriesHasSum_zetaMoebiusTailCoefficient (D : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMoebiusTailCoefficient D) s ((riemannZeta s)⁻¹ - zetaMoebiusDirichletHead D s) := by
  have hm : LSeriesHasSum (fun n ↦ (μ n : ℂ)) s (riemannZeta s)⁻¹ := by
    rw [← zetaReciprocalExtension_eq_inv (by intro h; simp [h] at hs),
      zetaReciprocalExtension_eq_moebius_LSeries hs]
    exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [zetaMoebiusTailCoefficient_eq_sub]
  exact hm.sub (LSeriesHasSum_zetaMoebiusHeadCoefficient D s)

private theorem LSeriesHasSum_log {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (Real.log n : ℂ)) s (-deriv riemannZeta s) := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  have h := hm.convolution (LSeriesHasSum_one hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one,
    div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re hs)] at h
  simpa only [← Complex.natCast_log] using h

/-- The literal coefficient of the large-divisor logarithmic convolution.
Its sign is retained; no norm or positive majorant enters this definition. -/
def zetaMoebiusLogTailCoefficient (D : ℕ) : ℕ → ℂ :=
  zetaMoebiusTailCoefficient D ⍟ (fun n : ℕ ↦ (Real.log n : ℂ))

/-- The coefficient is a finite sum over exact products, retaining the
strict cutoff on the Möbius divisor. -/
theorem zetaMoebiusLogTailCoefficient_eq (D n : ℕ) :
    zetaMoebiusLogTailCoefficient D n =
      ∑ a ∈ n.divisorsAntidiagonal, if D < a.1 then (μ a.1 : ℂ) * (Real.log a.2 : ℂ) else 0 := by
  simp only [zetaMoebiusLogTailCoefficient, LSeries.convolution_def, zetaMoebiusTailCoefficient,
    ite_mul, zero_mul]

/-- The actual meromorphic tail, identified below with its convergent
arithmetic convolution in the Euler half-plane. -/
def zetaMoebiusLogTail (D : ℕ) (s : ℂ) : ℂ :=
  ((riemannZeta s)⁻¹ - zetaMoebiusDirichletHead D s) * (-deriv riemannZeta s)

/-- Absolute convergence and the exact analytic value of the literal
large-divisor convolution; neither is a new arithmetic hypothesis. -/
theorem LSeriesHasSum_zetaMoebiusLogTail (D : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMoebiusLogTailCoefficient D) s (zetaMoebiusLogTail D s) :=
  (LSeriesHasSum_zetaMoebiusTailCoefficient D hs).convolution (LSeriesHasSum_log hs)

/-- The large-divisor convolution has no support below twice the first
retained divisor. The factor one contributes exactly zero through `log 1`. -/
theorem zetaMoebiusLogTailCoefficient_eq_zero_of_lt (D n : ℕ) (hn : n < 2 * (D + 1)) :
    zetaMoebiusLogTailCoefficient D n = 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hd : D < a.1
  · rw [if_pos hd]
    have hk : a.2 = 1 := by
      have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
      have hk0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal ha
      by_contra hk
      have hk2 : 2 ≤ a.2 := by omega
      nlinarith
    simp [hk]
  · rw [if_neg hd]

/-- Once divisor one is removed, this convolution vanishes on every
prime. Its surviving source is carried by composite products. -/
theorem zetaMoebiusLogTailCoefficient_prime (D : ℕ) (hD : 1 ≤ D) {p : ℕ} (hp : p.Prime) :
    zetaMoebiusLogTailCoefficient D p = 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq]
  apply Finset.sum_eq_zero
  intro a ha
  have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
  have hdvd : a.1 ∣ p := ⟨a.2, hprod.symm⟩
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp1
  · simp [h1, not_lt.mpr hD]
  · have hk : a.2 = 1 := by nlinarith [hp.two_le]
    simp [hk]

end

end RiemannGaussian
