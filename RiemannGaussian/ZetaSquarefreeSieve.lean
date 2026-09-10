/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeSquareDeletion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The complete squarefree sieve with every prime square included

The bounds for finite prime-square selections are uniform. Genuine
dominated convergence therefore includes every prime square in the
actual arithmetic sum. The full nonsquarefree contribution has an
independent bound, and the original first-power sieve and all signed
coefficients remain unchanged in the exact reconstruction.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- Every prime through an increasing integer cutoff, used solely
to exhaust all prime-square divisibility conditions in a genuine limit. -/
def zetaSquarePrimesThrough (K : ℕ) : Finset ℕ := (Finset.Icc 1 K).filter Nat.Prime

/-- Each finite square selection consists of actual primes. -/
theorem zetaSquarePrimesThrough_prime (K : ℕ) : ∀ p ∈ zetaSquarePrimesThrough K, p.Prime :=
  fun _ hp ↦ (Finset.mem_filter.mp hp).2

/-- The original sieved arithmetic coefficient on all nonsquarefree
indices, with no finite prime-square cutoff remaining. -/
def zetaNonsquarefreeCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if Squarefree n then 0 else zetaMoebiusSievedPrimeCoefficient D (primePairFactors S) n

/-- The complementary original coefficient on squarefree integers. -/
def zetaSquarefreeCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if Squarefree n then zetaMoebiusSievedPrimeCoefficient D (primePairFactors S) n else 0

/-- The full original first-power survivor is exactly its squarefree
and nonsquarefree parts, before any limit or absolute value. -/
theorem zetaMoebiusSievedPrimeCoefficient_eq_squarefree_add_nonsquarefree
    (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    zetaMoebiusSievedPrimeCoefficient D (primePairFactors S) n =
      zetaSquarefreeCoefficient D S n + zetaNonsquarefreeCoefficient D S n := by
  by_cases h : Squarefree n <;> simp [zetaSquarefreeCoefficient, zetaNonsquarefreeCoefficient, h]

/-- Every physical coefficient stabilizes at the exact nonsquarefree
mask when the selected prime-square cutoff tends to infinity. -/
theorem tendsto_zetaPrimeSquareCoefficient (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    Tendsto (fun K ↦ zetaPrimeSquareCoefficient D S (zetaSquarePrimesThrough K) n)
      atTop (𝓝 (zetaNonsquarefreeCoefficient D S n)) := by
  by_cases hn : Squarefree n
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with K
    simp [zetaPrimeSquareCoefficient,
      primeSquareSurvivorMask_eq_zero_of_squarefree S _ (zetaSquarePrimesThrough_prime K) hn,
      zetaNonsquarefreeCoefficient, hn]
  · have hex : ∃ p, p.Prime ∧ p ^ 2 ∣ n := by
      rw [Nat.squarefree_iff_prime_squarefree] at hn
      push Not at hn
      obtain ⟨p, hp, hpn⟩ := hn
      exact ⟨p, hp, by simpa only [pow_two] using hpn⟩
    obtain ⟨p, hp, hpn⟩ := hex
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop p] with K hK
    have hq : ∃ a ∈ zetaSquarePrimesThrough K, a ^ 2 ∣ n :=
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, hK⟩, hp⟩, hpn⟩
    rw [zetaPrimeSquareCoefficient_eq_sieved D S _ hS n, if_pos hq,
      zetaNonsquarefreeCoefficient, if_neg hn]

/-- The full nonsquarefree arithmetic response, including every
prime square and arbitrary further prime valuations. -/
def zetaNonsquarefreeFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaNonsquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The actual squarefree arithmetic response, with its original
signed divisor coefficients and complete complex kernel. -/
def zetaSquarefreeFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- Genuine dominated convergence exhausts every square in the full
arithmetic sum. The dominator is the original summable sieved series. -/
theorem tendsto_zetaPrimeSquareFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K ↦ zetaPrimeSquareFilter p D S (zetaSquarePrimesThrough K) N s)
      atTop (𝓝 (zetaNonsquarefreeFilter p D S N s)) := by
  have hsum := (hasSum_zetaMoebiusSievedPrimeFilter p D N hD (primePairFactors S)
    (primePairFactors_eligible S hS) hs).summable.norm
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro n
    exact (tendsto_zetaPrimeSquareCoefficient D S hS n).mul_const _
  · filter_upwards [] with K n
    rw [zetaPrimeSquareCoefficient_eq_sieved D S _ hS n]
    split_ifs
    · exact le_rfl
    · simpa only [zero_mul, norm_zero] using norm_nonneg
        (zetaMoebiusSievedPrimeCoefficient D (primePairFactors S) n * zetaPrimeFilterKernel p N s n)

/-- The full squarefree arithmetic sum is genuinely summable in the
Euler half-plane, with the original factor and cutoff conditions discharged. -/
theorem summable_zetaSquarefreeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaMoebiusSievedPrimeFilter p D N hD (primePairFactors S)
    (primePairFactors_eligible S hS) hs).summable.indicator {n | Squarefree n}
  apply h.congr
  intro n
  by_cases hn : Squarefree n <;> simp [Set.indicator, zetaSquarefreeCoefficient, hn]

/-- The complete repeated-prime arithmetic sum is also genuinely
summable, independently of its stronger analytic estimate. -/
theorem summable_zetaNonsquarefreeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaNonsquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaMoebiusSievedPrimeFilter p D N hD (primePairFactors S)
    (primePairFactors_eligible S hS) hs).summable.indicator {n | ¬Squarefree n}
  apply h.congr
  intro n
  by_cases hn : Squarefree n <;> simp [Set.indicator, zetaNonsquarefreeCoefficient, hn]

/-- The exact reconstruction of the whole original first-power
sieve commutes with both genuinely convergent infinite arithmetic sums. -/
theorem zetaMoebiusSievedPrimeFilter_eq_squarefree_add_nonsquarefree
    (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusSievedPrimeFilter p D (primePairFactors S) N s =
      zetaSquarefreeFilter p D S N s + zetaNonsquarefreeFilter p D S N s := by
  unfold zetaMoebiusSievedPrimeFilter zetaSquarefreeFilter zetaNonsquarefreeFilter
  simp_rw [zetaMoebiusSievedPrimeCoefficient_eq_squarefree_add_nonsquarefree D S, add_mul]
  exact (summable_zetaSquarefreeFilter p D N hD S hS hs).tsum_add
    (summable_zetaNonsquarefreeFilter p D N hD S hS hs)

/-- Every prime square is now included in the independent bound on
the full original nonsquarefree contribution. No square cutoff or
unproved summability or overlap assumption remains. -/
theorem exists_zetaNonsquarefreeFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ), 1 ≤ D →
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖zetaNonsquarefreeFilter p D S N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaPrimeSquareFilter_bound y hy hr hr1
  refine ⟨C, hC, fun p D N R S hD hS ↦ ?_⟩
  apply le_of_tendsto (tendsto_zetaPrimeSquareFilter p D N hD S
    (fun a ha ↦ (hS a ha).1) (s := 3 / 2 + I * y) (by norm_num)).norm
  exact Eventually.of_forall (fun K ↦ hb p D N R S (zetaSquarePrimesThrough K) hD hS
    (zetaSquarePrimesThrough_prime K))

end
end RiemannGaussian
