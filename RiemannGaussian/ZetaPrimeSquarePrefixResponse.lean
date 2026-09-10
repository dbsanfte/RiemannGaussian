/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimeSquareTransform
import RiemannGaussian.ZetaDivisibilityPrefix

/-!
# Actual signed prefix control for every selected prime square

The literal negative divisor prefix is restricted to repeated-prime
terms surviving the complete first-power pattern sieve. Its full
convergent series is exactly the finite signed square transform. The
bound is uniform over the selected squares, including all overlaps
with the first-power prime family.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The original signed prefix on the literal repeated-prime
survivor, retaining every divisor cutoff and physical phase downstream. -/
def zetaPrimeSquarePrefixCoefficient (D : ℕ) (S Q : Finset ℕ) (n : ℕ) : ℂ :=
  primeSquareSurvivorMask S Q n * zetaDivisibilityPrefixCoefficient D 1 n

/-- The exact square transform acts on the genuine divisibility
prefix coefficients, with no change of arithmetic carrier. -/
theorem zetaPrimeSquarePrefixCoefficient_eq_transform (D : ℕ) (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    zetaPrimeSquarePrefixCoefficient D S Q n =
      primeSquareSurvivorTransform (fun P ↦ zetaDivisibilityPrefixCoefficient D P n) S Q := by
  have he : (fun P ↦ zetaDivisibilityPrefixCoefficient D P n) =
      (fun P ↦ if P ∣ n then zetaDivisibilityPrefixCoefficient D 1 n else 0) :=
    funext (fun P ↦ zetaDivisibilityPrefixCoefficient_eq_indicator D P n)
  rw [he]
  exact (primeSquareSurvivorTransform_indicator S Q hS hQ
    (zetaDivisibilityPrefixCoefficient D 1) n).symm

/-- The actual absolutely convergent prefix series on the complete
selected-square survivor. -/
def zetaPrimeSquarePrefixFilter (p : Polynomial ℂ) (D : ℕ) (S Q : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaPrimeSquarePrefixCoefficient D S Q n * zetaPrimeFilterKernel p N s n

/-- Every signed intersection and genuine kernel sum agrees with the
original analytic factor response after the exact finite transform. -/
theorem hasSum_zetaPrimeSquarePrefixFilter (p : Polynomial ℂ) (D N : ℕ) (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaPrimeSquarePrefixCoefficient D S Q n * zetaPrimeFilterKernel p N s n)
      (primeSquareSurvivorTransform (fun P ↦ zetaMoebiusMultipleFilter p D P N s) S Q) := by
  have h := hasSum_primeSquareSurvivorTransform
    (fun P n ↦ zetaDivisibilityPrefixCoefficient D P n * zetaPrimeFilterKernel p N s n)
    (fun P ↦ zetaMoebiusMultipleFilter p D P N s) S Q hS hQ
    (fun P hP ↦ hasSum_zetaDivisibilityPrefixFilter p D N hP hs)
  apply h.congr_fun
  intro n
  rw [primeSquareSurvivorTransform_mul_right, zetaPrimeSquarePrefixCoefficient_eq_transform D S Q hS hQ n]

/-- The complete prefix response has a uniform independent bound
over every finite square selection. The first-power prime cutoff is the
only growing combinatorial cost, and the exact Cauchy radius is retained. -/
theorem exists_zetaPrimeSquarePrefixFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S Q : Finset ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) → (∀ a ∈ Q, a.Prime) →
      ‖zetaPrimeSquarePrefixFilter p D S Q N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaDivisibilityPrefixFilter_expWeight_bound y hy hr hr1
  refine ⟨C * primeSquareSurvivorCost (zetaSquareSieveExponent r),
    mul_pos hC (primeSquareSurvivorCost_pos _), ?_⟩
  intro p D N R S Q hS hQ
  rw [zetaPrimeSquarePrefixFilter,
    (hasSum_zetaPrimeSquarePrefixFilter p D N S Q (fun a ha ↦ (hS a ha).1) hQ (by norm_num)).tsum_eq]
  have h := norm_primeSquareSurvivorTransform_le
    (fun P ↦ zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)) S Q R hS hQ
    (zetaSquareSieveExponent_gt_half hr1)
    (show 0 ≤ C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) by positivity)
    (fun P hP ↦ hb p D P N hP)
  exact h.trans_eq (by ring)

end
end RiemannGaussian
