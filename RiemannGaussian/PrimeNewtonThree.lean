/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTriplePrime
import RiemannGaussian.ZetaExposedPrimeMoments

/-!
# Newton's third identity for complete ordinary-prime series

The elementary symmetric sum keeps the repeated-prime corrections with
their exact signs. These identities alone give no estimate on a masked
Riesz carrier.
-/

namespace RiemannGaussian.PrimeNewtonThree
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The two-element symmetric sum, counted once in increasing order. -/
def pairPrefix (f : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ q ∈ Finset.range M, ∑ p ∈ Finset.range q, f p * f q

/-- The three-element symmetric sum, counted once in increasing order. -/
def triplePrefix (f : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, ∑ q ∈ Finset.range r,
    ∑ p ∈ Finset.range q, f p * f q * f r

theorem pairPrefix_succ (f : ℕ → ℂ) (M : ℕ) :
    pairPrefix f (M+1) = pairPrefix f M + (∑ p ∈ Finset.range M, f p) * f M := by
  simp only [pairPrefix, Finset.sum_range_succ, Finset.sum_mul]

theorem triplePrefix_succ (f : ℕ → ℂ) (M : ℕ) :
    triplePrefix f (M+1) = triplePrefix f M + pairPrefix f M * f M := by
  simp only [triplePrefix, pairPrefix, Finset.sum_range_succ, Finset.sum_mul]

/-- The square identity includes its complete repeated-index diagonal. -/
theorem newton_two (f : ℕ → ℂ) (M : ℕ) :
    2 * pairPrefix f M = (∑ p ∈ Finset.range M, f p)^2 -
      ∑ p ∈ Finset.range M, (f p)^2 := by
  induction M with
  | zero => simp [pairPrefix]
  | succ M ih =>
    rw [pairPrefix_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination ih

/-- Newton's third identity, before passing to any infinite series. -/
theorem newton_three (f : ℕ → ℂ) (M : ℕ) :
    6 * triplePrefix f M = (∑ p ∈ Finset.range M, f p)^3 -
      3 * (∑ p ∈ Finset.range M, f p) * (∑ p ∈ Finset.range M, (f p)^2) +
      2 * ∑ p ∈ Finset.range M, (f p)^3 := by
  induction M with
  | zero => simp [triplePrefix]
  | succ M ih =>
    rw [triplePrefix_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    linear_combination ih + 3 * f M * newton_two f M

/-- Ordinary primes, with all composite and zero indices set to zero. -/
def primeAtom (s : ℂ) (p : ℕ) : ℂ := if p.Prime then zetaPrimeFeature s p else 0

theorem summable_primeAtom {s : ℂ} (hs : 1 < s.re) : Summable (primeAtom s) := by
  change Summable (fun p => if p.Prime then zetaPrimeFeature s p else 0)
  simpa [zetaPrimeLogKernel] using
    ZetaExposedPrimeMoments.summable_ordinaryPrimeMoment hs 0

/-- The complete prime zeta series, only used with proved summability. -/
def primeSeries (s : ℂ) : ℂ := ∑' p, primeAtom s p

theorem primeAtom_pow (s : ℂ) (p k : ℕ) (hk : k ≠ 0) :
    primeAtom s p ^ k = primeAtom ((k : ℂ)*s) p := by
  by_cases hp : p.Prime
  · simp only [primeAtom, if_pos hp, zetaPrimeFeature]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  · simp [primeAtom, hp, zero_pow hk]

private theorem pairPrefix_norm_le {f : ℕ → ℂ} (hf : Summable f) (M : ℕ) :
    ‖pairPrefix f M‖ ≤ (∑' p, ‖f p‖)^2 := by
  let B := ∑' p, ‖f p‖
  have hB : 0 ≤ B := tsum_nonneg (fun _ => norm_nonneg _)
  have hb (m : ℕ) : (∑ p ∈ Finset.range m, ‖f p‖) ≤ B :=
    hf.norm.sum_le_tsum _ (fun _ _ => norm_nonneg _)
  calc
    _ ≤ ∑ q ∈ Finset.range M, ∑ p ∈ Finset.range q, ‖f p‖ * ‖f q‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      simpa only [norm_mul] using norm_sum_le (Finset.range q) (fun p => f p * f q)
    _ ≤ ∑ q ∈ Finset.range M, B * ‖f q‖ := by
      apply Finset.sum_le_sum
      intro q _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _)
    _ = B * ∑ q ∈ Finset.range M, ‖f q‖ := (Finset.mul_sum ..).symm
    _ ≤ B*B := mul_le_mul_of_nonneg_left (hb M) hB
    _ = _ := by ring

/-- Absolute convergence justifies the infinite increasing-triple sum. -/
theorem summable_triple {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun r => pairPrefix f r * f r) := by
  apply (hf.norm.mul_left ((∑' p, ‖f p‖)^2)).of_norm_bounded
  intro r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (pairPrefix_norm_le hf r) (norm_nonneg _)

/-- Newton's identity for a genuinely convergent increasing-triple series. -/
theorem newton_three_tsum {f : ℕ → ℂ} (hf : Summable f)
    (h2 : Summable (fun p => f p^2)) (h3 : Summable (fun p => f p^3)) :
    6 * (∑' r, pairPrefix f r * f r) = (∑' p, f p)^3 -
      3 * (∑' p, f p) * (∑' p, f p^2) + 2 * ∑' p, f p^3 := by
  have ht := ((summable_triple hf).hasSum.tendsto_sum_nat).const_mul (6 : ℂ)
  have hr := ((hf.hasSum.tendsto_sum_nat.pow 3).sub
    ((hf.hasSum.tendsto_sum_nat.const_mul (3 : ℂ)).mul h2.hasSum.tendsto_sum_nat)).add
      (h3.hasSum.tendsto_sum_nat.const_mul (2 : ℂ))
  apply tendsto_nhds_unique ht
  convert hr using 1
  funext M
  rw [← newton_three f M]
  simp only [triplePrefix, pairPrefix, Finset.sum_mul]

/-- The complete squarefree three-prime series, counted once by p<q<r. -/
def threeSeries (s : ℂ) : ℂ := ∑' r, pairPrefix (primeAtom s) r * primeAtom s r

/-- The literal complete E₃(s), with both repeated-prime corrections. -/
theorem six_threeSeries {s : ℂ} (hs : 1 < s.re) :
    6 * threeSeries s = primeSeries s^3 -
      3 * primeSeries s * primeSeries (2*s) + 2 * primeSeries (3*s) := by
  have h2 : Summable (fun p => primeAtom s p^2) := by
    simpa only [primeAtom_pow s _ 2 (by decide), Nat.cast_ofNat] using
      summable_primeAtom (s := 2*s) (by norm_num; linarith)
  have h3 : Summable (fun p => primeAtom s p^3) := by
    simpa only [primeAtom_pow s _ 3 (by decide), Nat.cast_ofNat] using
      summable_primeAtom (s := 3*s) (by norm_num; linarith)
  simpa only [threeSeries, primeSeries, primeAtom_pow s _ 2 (by decide),
    primeAtom_pow s _ 3 (by decide), Nat.cast_ofNat] using
      newton_three_tsum (summable_primeAtom hs) h2 h3

end
end RiemannGaussian.PrimeNewtonThree
