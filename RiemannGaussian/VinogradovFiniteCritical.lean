/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLinearExponent

/-!
# Finite critical-moment iteration with the exact accumulated constant

Starting from the proved factorial elementary bound, finitely many
exponent improvements reach every positive critical defect. The actual
constant is A^n*k! at every positive integer endpoint, with a proved bound
on the stopping count in terms of the decrement. No moment estimate is
assumed at the terminal theorem. The full degree dependence of A and n
remains unevaluated; uniform VK growth and a larger zero-free region remain open.
-/

namespace RiemannGaussian.VinogradovFiniteCritical
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder
open VinogradovConstantPreservation
open VinogradovLinearProfile
open VinogradovLinearSaving
open VinogradovLinearExponent

/-- A fixed exponent decrement with linear constant cost reaches any positive
critical defect in finitely many steps, preserving the complete constant. -/
theorem finite_linear_exponent_descent (F : ℕ → ℝ) {c L d eps A C₀ : ℝ}
    (hcL : c ≤ L) (hd : 0 < d) (heps : 0 < eps) (hepsd : eps ≤ d / 2)
    (hA : 1 ≤ A) (hC₀ : 1 ≤ C₀)
    (hbase : ∀ X : ℕ, 1 ≤ X → F X ≤ C₀ * (X : ℝ) ^ L)
    (hstep : ∀ lam : ℝ, c + d ≤ lam → lam ≤ L → ∀ C : ℝ, 1 ≤ C →
      (∀ X : ℕ, 1 ≤ X → F X ≤ C * (X : ℝ) ^ lam) →
      ∀ X : ℕ, 1 ≤ X → F X ≤ (A * C) * (X : ℝ) ^ (lam - eps)) :
    ∃ n : ℕ, c ≤ L - (n : ℝ) * eps ∧ L - (n : ℝ) * eps < c + d ∧
      (n : ℝ) * eps ≤ max 0 (L - c - d) + eps ∧
      ∀ X : ℕ, 1 ≤ X → F X ≤ (A ^ n * C₀) * (X : ℝ) ^ (L - (n : ℝ) * eps) := by
  classical
  have hex : ∃ n : ℕ, L - (n : ℝ) * eps < c + d := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((L - c - d) / eps)
    refine ⟨n, ?_⟩
    have ht := (div_lt_iff₀ heps).mp hn
    linarith
  let n := Nat.find hex
  have hlast : L - (n : ℝ) * eps < c + d := Nat.find_spec hex
  have hprev (m : ℕ) (hm : m < n) : c + d ≤ L - (m : ℝ) * eps :=
    le_of_not_gt (Nat.find_min hex hm)
  have hwindow : c ≤ L - (n : ℝ) * eps ∧
      (n : ℝ) * eps ≤ max 0 (L - c - d) + eps := by
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, zero_mul, sub_zero]
      exact ⟨hcL, by linarith only [le_max_left (0 : ℝ) (L - c - d), heps]⟩
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hprevious := hprev (n - 1) (by omega)
      have hnm : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hnpos
      have hprod : (n : ℝ) * eps = ((n - 1 : ℕ) : ℝ) * eps + eps := by rw [← hnm]; ring
      constructor
      · linarith only [hprevious, hprod, hepsd, hd]
      · linarith only [hprevious, hprod, le_max_right (0 : ℝ) (L - c - d)]
  have hiter : ∀ m : ℕ, m ≤ n → ∀ X : ℕ, 1 ≤ X →
      F X ≤ (A ^ m * C₀) * (X : ℝ) ^ (L - (m : ℝ) * eps) := by
    intro m
    induction m with
    | zero => simpa only [pow_zero, one_mul, Nat.cast_zero, zero_mul, sub_zero] using fun _ => hbase
    | succ m ih =>
      intro hm
      have hml : m < n := by omega
      have hconstant : 1 ≤ A ^ m * C₀ := by
        calc
          1 ≤ A ^ m := one_le_pow₀ hA
          _ ≤ A ^ m * C₀ := le_mul_of_one_le_right (by positivity) hC₀
      have hlamlo := hprev m hml
      have hlamhi : L - (m : ℝ) * eps ≤ L :=
        sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) heps.le)
      have h := hstep (L - (m : ℝ) * eps) hlamlo hlamhi (A ^ m * C₀) hconstant (ih (by omega))
      convert h using 1
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring_nf
  exact ⟨n, hwindow.1, hlast, hwindow.2, hiter n le_rfl⟩

/-- Actual critical high moments follow by a finite iteration with the exact
constant A^n k!, valid at every positive integer endpoint. -/
theorem exists_finite_critical_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect : 0 < defect) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ n : ℕ,
      let c := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2
      let L := ((k * (2 * u + 1) : ℕ) : ℝ)
      c ≤ L - (n : ℝ) * eps ∧ L - (n : ℝ) * eps < c + defect ∧
      (n : ℝ) * eps ≤ max 0 (L - c - defect) + eps ∧
      ∀ X : ℕ, 1 ≤ X → meanValue ((u + 1) * k) k X ≤
        (A ^ n * (k.factorial : ℝ)) * (X : ℝ) ^ (c + defect) := by
  obtain ⟨eps, heps, hepsd, A, hA, hstep⟩ :=
    exists_linear_all_endpoint_improvement k u hk hu defect hdefect
  let c := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2
  let L := ((k * (2 * u + 1) : ℕ) : ℝ)
  have hcL : c ≤ L := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [c, L]
    push_cast
    nlinarith
  have hbase (X : ℕ) (_hX : 1 ≤ X) : meanValue ((u + 1) * k) k X ≤
      (k.factorial : ℝ) * (X : ℝ) ^ L := by
    simpa only [L, Real.rpow_natCast, mul_comm] using higher_meanValue_elementary k u X
  have hC₀ : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  obtain ⟨n, hnlo, hnhi, hncount, hnJ⟩ := finite_linear_exponent_descent
    (meanValue ((u + 1) * k) k) hcL hdefect heps hepsd hA hC₀ hbase (by
      intro lam hlo hhi C hC hJ
      apply hstep lam _ hhi C hC hJ
      dsimp only [c] at hlo
      linarith)
  refine ⟨eps, heps, hepsd, A, hA, n, hnlo, hnhi, hncount, ?_⟩
  intro X hX
  exact (hnJ X hX).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hnhi.le) (by positivity))

end
end RiemannGaussian.VinogradovFiniteCritical
