/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFactorPrefix
import RiemannGaussian.ZetaFiniteDirichlet
import RiemannGaussian.EtaMoebiusCoprimeProduct

/-!
# The genuine zeta response of the fixed coprime factor sector

Finite Möbius inversion supplies the coprime Euler factor. The logarithmic
convolution rule retains its logarithmic companion as well. Combined with
the two actual finite prefixes and the original index dilation, this gives
an absolutely convergent series equal to entire multipliers of `zeta` and
`-zeta'` throughout the Euler half-plane.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The finite Euler factor with all Möbius intersections included. -/
def zetaCoprimeEulerFactor (P : ℕ) : ℂ → ℂ :=
  zetaFiniteDirichletSeries P.divisors (fun d ↦ (μ d : ℂ))

/-- The logarithmic companion of the same finite Euler factor. -/
def zetaCoprimeEulerLogFactor (P : ℕ) : ℂ → ℂ :=
  zetaFiniteDirichletSeries P.divisors (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ))

/-- Complete inclusion-exclusion recovers the positive-index coprime
indicator as a literal Dirichlet convolution. -/
theorem zetaCoprimeCoefficient_eq_convolution {P : ℕ} (hP : 0 < P) :
    zetaCoprimeCoefficient P =
      zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) ⍟ (fun _ ↦ (1 : ℂ)) := by
  funext n
  by_cases hn : n = 0
  · simp [hn, zetaCoprimeCoefficient]
  · simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal
      (fun d _ ↦ zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) d * 1)]
    simp only [mul_one, zetaFiniteCoefficient]
    rw [← Finset.sum_filter]
    have he : n.divisors.filter (fun d ↦ d ∈ P.divisors) = P.divisors.filter (fun d ↦ d ∣ n) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      tauto
    rw [he, sum_divisors_moebius_dvd_eq_coprime hP]
    simp [zetaCoprimeCoefficient, hn, Nat.coprime_comm]

/-- The coprime Dirichlet series converges genuinely beyond one and
equals zeta times its finite Euler factor. -/
theorem LSeriesHasSum_zetaCoprimeCoefficient {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaCoprimeCoefficient P) s (zetaCoprimeEulerFactor P s * riemannZeta s) := by
  rw [zetaCoprimeCoefficient_eq_convolution hP]
  exact (LSeriesHasSum_zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) (by simp) s).convolution
    (LSeriesHasSum_one hs)

/-- The logarithmic coprime sequence keeps both terms of the product
rule, including the logarithmic finite Euler factor. -/
theorem LSeriesHasSum_zetaCoprimeLogCoefficient {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaCoprimeLogCoefficient P) s
      (zetaCoprimeEulerLogFactor P s * riemannZeta s +
        zetaCoprimeEulerFactor P s * (-deriv riemannZeta s)) := by
  have he : (fun n ↦ zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) n *
      (Real.log n : ℂ)) =
      zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ)) := by
    funext n
    by_cases hn : n ∈ P.divisors <;> simp [zetaFiniteCoefficient, hn]
  have hc : zetaCoprimeLogCoefficient P =
      zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ)) ⍟ (fun _ ↦ 1) +
        zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) ⍟ (fun n ↦ (Real.log n : ℂ)) := by
    change (fun n ↦ zetaCoprimeCoefficient P n * (Real.log n : ℂ)) = _
    rw [zetaCoprimeCoefficient_eq_convolution hP, convolution_mul_natLog, he]
    simp only [one_mul]
  rw [hc]
  exact ((LSeriesHasSum_zetaFiniteCoefficient P.divisors
      (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ)) (by simp) s).convolution
        (LSeriesHasSum_one hs)).add
    ((LSeriesHasSum_zetaFiniteCoefficient P.divisors (fun d ↦ (μ d : ℂ)) (by simp) s).convolution
      (LSeriesHasSum_natLog hs))

/-- The actual finite slope polynomial after complete fibre cancellation. -/
def zetaMoebiusFactorSlopeSeries (D P : ℕ) : ℂ → ℂ :=
  zetaFiniteDirichletSeries (Finset.Icc 1 D) (zetaMoebiusFactorSlope D P)

/-- The actual finite intercept polynomial, with the same cutoff. -/
def zetaMoebiusFactorInterceptSeries (D P : ℕ) : ℂ → ℂ :=
  zetaFiniteDirichletSeries (Finset.Icc 1 D) (zetaMoebiusFactorIntercept D P)

/-- The full multiplier of `-zeta'`, including the physical factor dilation. -/
def zetaMoebiusFactorDerivativeMultiplier (D P : ℕ) (s : ℂ) : ℂ :=
  zetaPrimeFeature s P * (zetaMoebiusFactorSlopeSeries D P s * zetaCoprimeEulerFactor P s)

/-- The full multiplier of zeta, including both logarithmic channels. -/
def zetaMoebiusFactorValueMultiplier (D P : ℕ) (s : ℂ) : ℂ :=
  zetaPrimeFeature s P * (zetaMoebiusFactorSlopeSeries D P s * zetaCoprimeEulerLogFactor P s +
    zetaMoebiusFactorInterceptSeries D P s * zetaCoprimeEulerFactor P s)

/-- The response of the original arithmetic sector on its physical index. -/
def zetaMoebiusFactorResponse (D P : ℕ) (s : ℂ) : ℂ :=
  zetaMoebiusFactorDerivativeMultiplier D P s * (-deriv riemannZeta s) +
    zetaMoebiusFactorValueMultiplier D P s * riemannZeta s

/-- The literal coefficients on the physical multiples of the fixed factor. -/
def zetaMoebiusFactorSectorCoefficient (D P : ℕ) : ℕ → ℂ :=
  zetaDilationCoefficient P (zetaMoebiusFactorCoefficient D P)

/-- The sector is exactly the corresponding subset of the original
Möbius coefficients. In particular, no substitute arithmetic carrier is used. -/
theorem zetaMoebiusFactorSectorCoefficient_eq (D P m : ℕ) :
    zetaMoebiusFactorSectorCoefficient D P m =
      if P ∣ m ∧ P.Coprime (m / P) then zetaMoebiusLogTailCoefficient D m else 0 := by
  by_cases hdiv : P ∣ m
  · simp [zetaMoebiusFactorSectorCoefficient, zetaDilationCoefficient,
      zetaMoebiusFactorCoefficient, Nat.mul_div_cancel' hdiv, hdiv]
  · simp [zetaMoebiusFactorSectorCoefficient, zetaDilationCoefficient, hdiv]

/-- The undilated and physical sector coefficients both have zero
coefficient at index zero, as required by the exponential moment kernels. -/
theorem zetaMoebiusFactorCoefficient_zero (D P : ℕ) :
    zetaMoebiusFactorCoefficient D P 0 = 0 ∧ zetaMoebiusFactorSectorCoefficient D P 0 = 0 := by
  simp [zetaMoebiusFactorCoefficient, zetaMoebiusFactorSectorCoefficient, zetaDilationCoefficient,
    zetaMoebiusLogTailCoefficient]

/-- The response is identified with its genuinely convergent arithmetic
series on the Euler half-plane. Both prefix channels and all finite Euler
intersections are included in the identity. -/
theorem LSeriesHasSum_zetaMoebiusFactorResponse (D : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMoebiusFactorSectorCoefficient D P) s (zetaMoebiusFactorResponse D P s) := by
  have hG := LSeriesHasSum_of_support_Icc (zetaMoebiusFactorSlope D P) D
    (zetaMoebiusFactorPrefix_zero D P).1
    (fun n hn ↦ (zetaMoebiusFactorPrefix_support D P hn).1) s
  have hH := LSeriesHasSum_of_support_Icc (zetaMoebiusFactorIntercept D P) D
    (zetaMoebiusFactorPrefix_zero D P).2
    (fun n hn ↦ (zetaMoebiusFactorPrefix_support D P hn).2) s
  have h := (hG.convolution (LSeriesHasSum_zetaCoprimeLogCoefficient hP hs)).add
    (hH.convolution (LSeriesHasSum_zetaCoprimeCoefficient hP hs))
  rw [← zetaMoebiusFactorCoefficient_eq_convolutions D hP hP1 hmix] at h
  have hscaled := LSeriesHasSum_zetaDilationCoefficient hP (zetaMoebiusFactorCoefficient_zero D P).1 h
  convert hscaled using 1
  · rfl
  · unfold zetaMoebiusFactorResponse zetaMoebiusFactorDerivativeMultiplier
      zetaMoebiusFactorValueMultiplier zetaMoebiusFactorSlopeSeries zetaMoebiusFactorInterceptSeries
    ring

/-- Both response multipliers are entire finite exponential polynomials. -/
theorem differentiable_zetaMoebiusFactorMultipliers (D P : ℕ) :
    Differentiable ℂ (zetaMoebiusFactorDerivativeMultiplier D P) ∧
      Differentiable ℂ (zetaMoebiusFactorValueMultiplier D P) := by
  have he : Differentiable ℂ (fun s ↦ zetaPrimeFeature s P) := by
    unfold zetaPrimeFeature
    fun_prop
  have hG := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 D) (zetaMoebiusFactorSlope D P)
  have hH := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 D) (zetaMoebiusFactorIntercept D P)
  have hE := differentiable_zetaFiniteDirichletSeries P.divisors (fun d ↦ (μ d : ℂ))
  have hL := differentiable_zetaFiniteDirichletSeries P.divisors
    (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ))
  exact ⟨he.mul (hG.mul hE), he.mul ((hG.mul hL).add (hH.mul hE))⟩

end
end RiemannGaussian
