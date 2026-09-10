/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinBoundary

/-!
# Complete phase families at the Euler boundary

Every nonnegative summable family with a logarithmic frequency moment
admits the exact pole-removed identity and its complete arithmetic Abel
limit. No restriction on frequency count or separation is imposed.
The zero sum is formed first at each frequency; its original reflection
pairs and multiplicities are retained throughout.

This boundary passage does not provide an independent lower bound on the
regularized arithmetic. Subtracting the pole prevents transferring the
old prime-work positivity to that new signed quantity.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Set
open scoped Topology

variable {a ω : ℕ → ℝ}

/-- The signed pole-removed family converges absolutely even on the
boundary. Its domination permits infinite spectra accumulating at zero. -/
theorem summable_zetaPhase_stechkin_poleRemoved
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|)))
    {σ : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2) (y : ℝ) :
    Summable (fun n => a n * (zetaStechkinPoleRemoved σ (ω n * y)).re) := by
  obtain ⟨C, _, hb⟩ := exists_zetaStechkinPoleRemoved_euler_bound
  apply ((summable_zetaPhase_eulerHeight_of_logMoment ha hs hlog y).mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  have h := mul_le_mul_of_nonneg_left (hb σ hσ hσ2 (ω n * y)) (ha n)
  nlinarith only [h]

/-- The exact signed completion comparison is summable with the same
logarithmic moment, including at the boundary. -/
theorem summable_zetaPhase_stechkin_boundaryRegular
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|)))
    {σ : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2) (y : ℝ) :
    Summable (fun n => a n * (zetaStechkinRegularComparison σ (ω n * y)).re) := by
  apply ((summable_zetaPhase_eulerHeight_of_logMoment ha hs hlog y).mul_left 4).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  have h := mul_le_mul_of_nonneg_left
    (abs_re_zetaStechkinRegularComparison_euler_le hσ hσ2 (ω n * y)) (ha n)
  nlinarith only [h]

/-- The complete reflected zero masses are summable over the family
through the boundary, without interchanging the two infinite sums. -/
theorem summable_zetaPhase_stechkin_boundaryZeros
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|)))
    {σ : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2) (y : ℝ) :
    Summable (fun n => a n * ∑' rho : NontrivialZetaZero,
      zetaStechkinPoissonSummand σ (ω n * y) rho) := by
  apply ((summable_zetaPhase_stechkin_boundaryRegular ha hs hlog hσ hσ2 y).sub
    (summable_zetaPhase_stechkin_poleRemoved ha hs hlog hσ hσ2 y)).congr
  intro n
  have h := zetaStechkinPoleRemoved_add_zeroMass_eq hσ (ω n * y)
  linear_combination -a n * h

/-- The exact all-family identity includes every actual reflection
pair and the signed completion at `sigma=1`, including zero frequencies. -/
theorem zetaPhase_stechkin_boundary_identity
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|))) (y : ℝ) :
    (∑' n : ℕ, a n * (zetaStechkinPoleRemoved 1 (ω n * y)).re) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaStechkinPoissonSummand 1 (ω n * y) rho) =
      ∑' n : ℕ, a n * (zetaStechkinRegularComparison 1 (ω n * y)).re := by
  rw [← (summable_zetaPhase_stechkin_poleRemoved ha hs hlog le_rfl (by norm_num) y).tsum_add
    (summable_zetaPhase_stechkin_boundaryZeros ha hs hlog le_rfl (by norm_num) y)]
  apply tsum_congr
  intro n
  have h := zetaStechkinPoleRemoved_add_zeroMass_eq (σ := 1) le_rfl (ω n * y)
  linear_combination a n * h

/-- At the Euler boundary a selected right-half zero still supplies
its full multiplicity divided by its distance from one. No logarithmic
replacement of the exact completion is made. -/
theorem zetaPhase_stechkin_boundary_source_le
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|)))
    (r : ℕ) (hr : ω r = 1) (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) :
    a r * (analyticZetaZeroMultiplicity rho : ℝ) / (1 - rho.1.re) +
      (∑' n : ℕ, a n * (zetaStechkinPoleRemoved 1 (ω n * rho.1.im)).re) ≤
        ∑' n : ℕ, a n * (zetaStechkinRegularComparison 1 (ω n * rho.1.im)).re := by
  have he := zetaPhase_stechkin_boundary_identity ha hs hlog rho.1.im
  have hb := (summable_zetaPhase_stechkin_boundaryZeros ha hs hlog
    (σ := 1) le_rfl (by norm_num) rho.1.im).le_tsum r
      (fun n _ => mul_nonneg (ha n) (tsum_nonneg
        (zetaStechkinPoissonSummand_nonneg (σ := 1) le_rfl (ω n * rho.1.im))))
  rw [hr, one_mul] at hb
  have hsource := mul_le_mul_of_nonneg_left
    (zetaStechkin_source_le_total rho hρ (σ := 1) le_rfl) (ha r)
  rw [← mul_div_assoc] at hsource
  linarith

/-- For each fixed admissible family, the complete pole-removed
arithmetic response tends to its boundary series. Both the coefficient
sum and logarithmic frequency moment dominate the infinite-family limit. -/
theorem tendsto_zetaPhase_stechkin_poleRemoved_boundary
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|))) (y : ℝ) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, a n * (zetaStechkinPoleRemoved σ (ω n * y)).re)
      (𝓝[>] 1) (𝓝 (∑' n : ℕ, a n * (zetaStechkinPoleRemoved 1 (ω n * y)).re)) := by
  obtain ⟨C, _, hb⟩ := exists_zetaStechkinPoleRemoved_euler_bound
  have hsum := (summable_zetaPhase_eulerHeight_of_logMoment ha hs hlog y).mul_left C
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro n
    have h : ContinuousAt (fun σ => (zetaStechkinPoleRemoved σ (ω n * y)).re) 1 :=
      Complex.continuous_re.continuousAt.comp
        (continuousAt_zetaStechkinPoleRemoved (σ := 1) le_rfl (ω n * y))
    exact (h.const_mul (a n)).tendsto.mono_left nhdsWithin_le_nhds
  · have hnear : Iio (2 : ℝ) ∈ 𝓝[>] (1 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hnear] with σ hσ hσ2
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
    have h := mul_le_mul_of_nonneg_left (hb σ hσ.le hσ2.le (ω n * y)) (ha n)
    nlinarith only [h]

/-- The original complete prime series minus the entire exact pole
family is precisely the regularized response on every Euler-product line.
The subtraction is performed before taking the boundary limit. -/
theorem zetaPhase_stechkin_primeWork_sub_pole_eq
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) -
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) =
        ∑' n : ℕ, a n * (zetaStechkinPoleRemoved σ (ω n * y)).re := by
  rw [(hasSum_zetaPhase_stechkin_arithmetic (ω := ω) ha hs hσ y).tsum_eq]
  have hτ := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
  have hD : Summable (fun n : ℕ => a n *
      ((-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
        zetaStechkinWeight σ * (-logDeriv riemannZeta
          ((zetaStechkinAbscissa σ : ℝ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
    apply ((summable_zetaPhase_logDeriv (ω := ω) ha hs hσ y).sub
      ((summable_zetaPhase_logDeriv (ω := ω) ha hs hτ y).mul_left (zetaStechkinWeight σ))).congr
    intro n
    ring
  rw [← hD.tsum_sub (summable_zetaPhase_stechkin_pole (ω := ω) ha hs hσ y)]
  apply tsum_congr
  intro n
  rw [zetaStechkinPoleRemoved_eq_prime_sub_pole hσ]
  ring

/-- The exact Abel limit of complete prime work after subtracting its
full pole family. This includes the divergent zero-frequency cancellation
and does not require a frequency gap or a finite support. -/
theorem tendsto_zetaPhase_stechkin_primeWork_sub_pole_boundary
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n => a n * Real.log (1 + |ω n|))) (y : ℝ) :
    Tendsto (fun σ : ℝ =>
      (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) -
        (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)))
      (𝓝[>] 1) (𝓝 (∑' n : ℕ, a n * (zetaStechkinPoleRemoved 1 (ω n * y)).re)) := by
  apply (tendsto_zetaPhase_stechkin_poleRemoved_boundary ha hs hlog y).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (zetaPhase_stechkin_primeWork_sub_pole_eq ha hs hσ y).symm

end
end RiemannGaussian
