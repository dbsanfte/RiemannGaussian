/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeSquarePrefixResponse
import RiemannGaussian.ZetaMoebiusSievedPrimeTail
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Independent control of the actual repeated-prime survivor

The literal distinct-prime Möbius tail splits into the controlled signed
prefix and explicit prime-power leakage. That leakage has a fixed
summable majorant strictly past one half. The whole selected-square
deletion therefore has a bound independent of the size and cardinality
of the square family, with the original first-power sieve retained.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The original distinct-prime coefficient on the repeated-prime
terms surviving the complete first-power prime sieve. -/
def zetaPrimeSquareCoefficient (D : ℕ) (S Q : Finset ℕ) (n : ℕ) : ℂ :=
  primeSquareSurvivorMask S Q n * zetaMoebiusDistinctPrimeCoefficient D n

/-- The full prime-power correction, retained with its exact sign
before applying the independent proper-prime-power bound. -/
def zetaPrimeSquareLeakageCoefficient (D : ℕ) (S Q : Finset ℕ) (n : ℕ) : ℂ :=
  primeSquareSurvivorMask S Q n *
    ((ArithmeticFunction.vonMangoldt n : ℂ) - zetaMoebiusTailPrimePowerCoefficient D n)

/-- The actual repeated-prime coefficient is the controlled negative
prefix plus its entire explicit prime-power correction. -/
theorem zetaPrimeSquareCoefficient_eq_prefix_add_leakage (D : ℕ) (S Q : Finset ℕ) (n : ℕ) :
    zetaPrimeSquareCoefficient D S Q n = zetaPrimeSquarePrefixCoefficient D S Q n +
      zetaPrimeSquareLeakageCoefficient D S Q n := by
  have h := zetaMoebiusLogTailCoefficient_eq_primePower_add_distinct D n
  rw [zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix D n] at h
  unfold zetaPrimeSquareCoefficient zetaPrimeSquarePrefixCoefficient zetaPrimeSquareLeakageCoefficient
  linear_combination -(primeSquareSurvivorMask S Q n) * h

/-- The repeated-prime mask restricts exactly the original simultaneous
first-power sieve coefficient, so the source reconstruction uses the
unchanged literal arithmetic sequence. -/
theorem zetaPrimeSquareCoefficient_eq_sieved (D : ℕ) (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaPrimeSquareCoefficient D S Q n =
      if ∃ p ∈ Q, p ^ 2 ∣ n then zetaMoebiusSievedPrimeCoefficient D (primePairFactors S) n else 0 := by
  have he := primePairSieve_card_iff S hS n
  by_cases hq : ∃ p ∈ Q, p ^ 2 ∣ n
  · by_cases hc : (S.filter (fun p ↦ p ∣ n)).card ≤ 1
    · have hs : ¬∃ P ∈ primePairFactors S, P ∣ n := fun h ↦ (by omega : ¬2 ≤ (S.filter (fun p ↦ p ∣ n)).card) (he.mpr h)
      simp [zetaPrimeSquareCoefficient, primeSquareSurvivorMask, zetaMoebiusSievedPrimeCoefficient, hq, hc, hs]
    · have hs : ∃ P ∈ primePairFactors S, P ∣ n := he.mp (by omega)
      simp [zetaPrimeSquareCoefficient, primeSquareSurvivorMask, zetaMoebiusSievedPrimeCoefficient, hq, hc, hs]
  · simp [zetaPrimeSquareCoefficient, primeSquareSurvivorMask, hq]

/-- A fixed majorant pays both proper-prime-power channels of the
square deletion, independently of the divisor and prime cutoffs. -/
def zetaPrimeSquareLeakageMajorant (n : ℕ) : ℝ :=
  zetaProperPrimePowerCoefficient n + zetaMoebiusTailPrimePowerMajorant n

/-- The complete leakage majorant is nonnegative. -/
theorem zetaPrimeSquareLeakageMajorant_nonneg (n : ℕ) : 0 ≤ zetaPrimeSquareLeakageMajorant n :=
  add_nonneg (zetaProperPrimePowerCoefficient_nonneg n) (zetaMoebiusTailPrimePowerMajorant_nonneg n)

/-- The exact leakage has a cutoff-independent bound supported only
on proper prime powers. The selected square family may be arbitrary. -/
theorem norm_zetaPrimeSquareLeakageCoefficient_le (D : ℕ) (hD : 1 ≤ D) (S Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    ‖zetaPrimeSquareLeakageCoefficient D S Q n‖ ≤ zetaPrimeSquareLeakageMajorant n := by
  by_cases h : (S.filter (fun p ↦ p ∣ n)).card ≤ 1 ∧ (∃ p ∈ Q, p ^ 2 ∣ n)
  · have hn : ¬n.Prime := by
      intro hn
      obtain ⟨p, hp, hpn⟩ := h.2
      exact (Nat.squarefree_iff_prime_squarefree.mp hn.squarefree p (hQ p hp))
        (by simpa only [pow_two] using hpn)
    rw [zetaPrimeSquareLeakageCoefficient, primeSquareSurvivorMask, if_pos h, one_mul]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ (norm_zetaMoebiusTailPrimePowerCoefficient_le D hD n)
    rw [Complex.norm_real, Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg),
      zetaProperPrimePowerCoefficient, if_neg hn]
  · simpa only [zetaPrimeSquareLeakageCoefficient, primeSquareSurvivorMask, if_neg h,
      zero_mul, norm_zero] using zetaPrimeSquareLeakageMajorant_nonneg n

/-- The entire leakage majorant has genuine convergence strictly
past one half, uniformly over both selected-prime families. -/
theorem summable_zetaPrimeSquareLeakageMajorant {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n ↦ zetaPrimeSquareLeakageMajorant n * zetaPrimeExpWeight σ n) := by
  simpa only [zetaPrimeSquareLeakageMajorant, add_mul] using
    (summable_zetaProperPrimePowerExpMass hσ).add (summable_zetaMoebiusTailPrimePowerMajorant hσ)

/-- The finite real mass of the complete prime-power correction. -/
def zetaPrimeSquareLeakageMass (σ : ℝ) : ℝ :=
  ∑' n, zetaPrimeSquareLeakageMajorant n * zetaPrimeExpWeight σ n

/-- The complete leakage mass is nonnegative. -/
theorem zetaPrimeSquareLeakageMass_nonneg (σ : ℝ) : 0 ≤ zetaPrimeSquareLeakageMass σ :=
  tsum_nonneg (fun n ↦ mul_nonneg (zetaPrimeSquareLeakageMajorant_nonneg n) (Real.exp_pos _).le)

private theorem leakage_kernel_le (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S Q : Finset ℕ) (hQ : ∀ a ∈ Q, a.Prime) (y : ℝ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ‖zetaPrimeSquareLeakageCoefficient D S Q n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      (r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) *
        (zetaPrimeSquareLeakageMajorant n * zetaPrimeExpWeight (3 / 2 - r) n) := by
  have hc := norm_zetaPrimeSquareLeakageCoefficient_le D hD S Q hQ n
  by_cases hn : n = 0
  · have hz : zetaPrimeSquareLeakageCoefficient D S Q n = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa [hn, zetaPrimeSquareLeakageMajorant, zetaProperPrimePowerCoefficient,
        zetaMoebiusTailPrimePowerMajorant] using hc
    rw [hz, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (zetaPrimeSquareLeakageMajorant_nonneg n) (Real.exp_pos _).le)
  · have hk : ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
        r⁻¹ ^ N * zetaPrimeExpWeight (3 / 2 - r) n * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
      simpa only [show (3 / 2 + I * (y : ℂ)).re = 3 / 2 by simp, zetaPrimeExpWeight] using
        norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * y)
          (show (1 : ℝ) ≤ n by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hr
    rw [norm_mul]
    exact (mul_le_mul hc hk (norm_nonneg _) (zetaPrimeSquareLeakageMajorant_nonneg n)).trans_eq (by ring)

/-- The literal prime-power correction has a genuinely summable
full polynomial-kernel series at every real ordinate. -/
theorem summable_zetaPrimeSquareLeakageFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S Q : Finset ℕ) (hQ : ∀ a ∈ Q, a.Prime) (y : ℝ) :
    Summable (fun n ↦ zetaPrimeSquareLeakageCoefficient D S Q n *
      zetaPrimeFilterKernel p N (3 / 2 + I * y) n) := by
  apply ((summable_zetaPrimeSquareLeakageMajorant (by norm_num : (1 / 2 : ℝ) < 3 / 2 - 1 / 2)).mul_left
    ((1 / 2 : ℝ)⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (1 / 2 : ℝ)⁻¹ ^ k)).of_norm_bounded
  exact leakage_kernel_le p D N hD S Q hQ y (by norm_num)

/-- The full actual signed leakage response. -/
def zetaPrimeSquareLeakageFilter (p : Polynomial ℂ) (D : ℕ) (S Q : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaPrimeSquareLeakageCoefficient D S Q n * zetaPrimeFilterKernel p N s n

/-- All prime-power leakage has a uniform complete filter allowance
at every radius below one, independent of all three finite cutoffs. -/
theorem norm_zetaPrimeSquareLeakageFilter_le (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S Q : Finset ℕ) (hQ : ∀ a ∈ Q, a.Prime) (y : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖zetaPrimeSquareLeakageFilter p D S Q N (3 / 2 + I * y)‖ ≤
      r⁻¹ ^ N * zetaPrimeSquareLeakageMass (3 / 2 - r) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  have hs := summable_zetaPrimeSquareLeakageFilter p D N hD S Q hQ y
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  calc
    _ ≤ ∑' n, (r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) *
        (zetaPrimeSquareLeakageMajorant n * zetaPrimeExpWeight (3 / 2 - r) n) :=
      Summable.tsum_le_tsum (leakage_kernel_le p D N hD S Q hQ y hr) hs.norm
        ((summable_zetaPrimeSquareLeakageMajorant (by linarith)).mul_left _)
    _ = _ := by rw [tsum_mul_left, zetaPrimeSquareLeakageMass]; ring

/-- The actual full arithmetic series of the selected-square terms
within the surviving distinct-prime coefficient. -/
def zetaPrimeSquareFilter (p : Polynomial ℂ) (D : ℕ) (S Q : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaPrimeSquareCoefficient D S Q n * zetaPrimeFilterKernel p N s n

/-- The original repeated-prime sum is exactly its controlled prefix
plus the entire prime-power correction, with genuine convergence. -/
theorem hasSum_zetaPrimeSquareFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S Q : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (hQ : ∀ a ∈ Q, a.Prime) (y : ℝ) :
    HasSum (fun n ↦ zetaPrimeSquareCoefficient D S Q n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n)
      (zetaPrimeSquarePrefixFilter p D S Q N (3 / 2 + I * y) +
        zetaPrimeSquareLeakageFilter p D S Q N (3 / 2 + I * y)) := by
  have h := (hasSum_zetaPrimeSquarePrefixFilter p D N S Q hS hQ
    (s := 3 / 2 + I * y) (by norm_num)).summable.hasSum.add
    (summable_zetaPrimeSquareLeakageFilter p D N hD S Q hQ y).hasSum
  apply h.congr_fun
  intro n
  rw [zetaPrimeSquareCoefficient_eq_prefix_add_leakage, add_mul]

/-- The whole actual repeated-prime survivor has an independent bound
uniform over every selected square family. Every signed intersection
and prime-power correction is paid, with no remaining overlap premise. -/
theorem exists_zetaPrimeSquareFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S Q : Finset ℕ), 1 ≤ D →
      (∀ a ∈ S, a.Prime ∧ a ≤ R) → (∀ a ∈ Q, a.Prime) →
      ‖zetaPrimeSquareFilter p D S Q N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaPrimeSquarePrefixFilter_bound y hy hr hr1
  let M := zetaPrimeSquareLeakageMass (3 / 2 - r)
  have hM : 0 ≤ M := zetaPrimeSquareLeakageMass_nonneg _
  refine ⟨C + M + 1, by positivity, ?_⟩
  intro p D N R S Q hD hS hQ
  rw [zetaPrimeSquareFilter,
    (hasSum_zetaPrimeSquareFilter p D N hD S Q (fun a ha ↦ (hS a ha).1) hQ y).tsum_eq]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hb p D N R S Q hS hQ)
    (norm_zetaPrimeSquareLeakageFilter_le p D N hD S Q hQ y hr hr1)).trans
  have hDE : 1 ≤ (D : ℝ) * Real.exp (4 * Real.sqrt R) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
      (Real.one_le_exp_iff.mpr (by positivity))
  have hscale : M ≤ M * D * Real.exp (4 * Real.sqrt R) := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hDE hM
  have hstep := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) by positivity)
  have hpos : 0 ≤ (D : ℝ) * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
      (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by positivity
  dsimp [M] at *
  nlinarith

end
end RiemannGaussian
