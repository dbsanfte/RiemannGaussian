/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeSieve

/-!
# The full squarefree divisor prefix on every prime intersection

Squarefree restriction commutes with the exact finite divisibility response.
The uniform square-intersection estimate passes through a genuine infinite
sum limit. Every first-power intersection keeps its shared-prime correction,
so a later finite prime-pattern sum can use the bound without losing overlaps.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- For each physical integer, finite square avoidance eventually
agrees with squarefreeness. This includes zero and every repeated valuation. -/
theorem eventually_no_primeSquareThrough_iff (n : ℕ) :
    ∀ᶠ K : ℕ in atTop, (¬∃ p ∈ zetaSquarePrimesThrough K, p ^ 2 ∣ n) ↔ Squarefree n := by
  by_cases hn : Squarefree n
  · filter_upwards [] with K
    simp only [hn, iff_true]
    rintro ⟨p, hp, hpn⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hn p (zetaSquarePrimesThrough_prime K p hp))
      (by simpa only [pow_two] using hpn)
  · have hex : ∃ p, p.Prime ∧ p ^ 2 ∣ n := by
      have h := hn
      rw [Nat.squarefree_iff_prime_squarefree] at h
      push Not at h
      obtain ⟨p, hp, hd⟩ := h
      exact ⟨p, hp, by simpa only [pow_two] using hd⟩
    obtain ⟨p, hp, hd⟩ := hex
    filter_upwards [eventually_ge_atTop p] with K hK
    have he : ∃ a ∈ zetaSquarePrimesThrough K, a ^ 2 ∣ n :=
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, hK⟩, hp⟩, hd⟩
    simp [he, hn]

/-- The actual negative divisor prefix on squarefree multiples of a
selected prime intersection, with the original cutoff unchanged. -/
def zetaSquarefreeDivisibilityPrefixCoefficient (D : ℕ) (W : Finset ℕ) (n : ℕ) : ℂ :=
  if Squarefree n then zetaDivisibilityPrefixCoefficient D (∏ p ∈ W, p) n else 0

/-- Squarefree restriction leaves the complete first-power divisibility
condition explicit, before any kernel or norm is applied. -/
theorem zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator (D : ℕ)
    (W : Finset ℕ) (n : ℕ) :
    zetaSquarefreeDivisibilityPrefixCoefficient D W n =
      if (∏ p ∈ W, p) ∣ n then zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n else 0 := by
  by_cases hn : Squarefree n
  · simp only [zetaSquarefreeDivisibilityPrefixCoefficient, hn, if_true, Finset.prod_empty]
    exact zetaDivisibilityPrefixCoefficient_eq_indicator D _ n
  · simp [zetaSquarefreeDivisibilityPrefixCoefficient, hn]

/-- The complete squarefree prefix response, as its original infinite
arithmetic series with the full complex polynomial kernel. -/
def zetaSquarefreeDivisibilityPrefixFilter (p : Polynomial ℂ) (D : ℕ)
    (W : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaSquarefreeDivisibilityPrefixCoefficient D W n * zetaPrimeFilterKernel p N s n

/-- The restricted prefix series is genuinely summable throughout
the Euler half-plane, for every selected prime intersection. -/
theorem summable_zetaSquarefreeDivisibilityPrefixFilter (p : Polynomial ℂ) (D N : ℕ)
    (W : Finset ℕ) (hW : ∀ a ∈ W, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaSquarefreeDivisibilityPrefixCoefficient D W n *
      zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaDivisibilityPrefixFilter p D N
    (Finset.prod_pos (fun a ha ↦ (hW a ha).pos)) hs).summable.indicator {n | Squarefree n}
  apply h.congr
  intro n
  by_cases hn : Squarefree n <;> simp [Set.indicator, zetaSquarefreeDivisibilityPrefixCoefficient, hn]

private theorem finite_square_avoidance_hasSum (p : Polynomial ℂ) (D N : ℕ)
    (W Q : Finset ℕ) (hW : ∀ a ∈ W, a.Prime) (hQ : ∀ a ∈ Q, a.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (if ∃ a ∈ Q, a ^ 2 ∣ n then 0
      else zetaDivisibilityPrefixCoefficient D (∏ a ∈ W, a) n) * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusMultipleFilter p D (∏ a ∈ W, a) N s -
        primeSquareMultipleTransform (fun P ↦ zetaMoebiusMultipleFilter p D P N s) W Q) := by
  have hm := hasSum_primeSquareMultipleTransform
    (fun P n ↦ zetaDivisibilityPrefixCoefficient D P n * zetaPrimeFilterKernel p N s n)
    (fun P ↦ zetaMoebiusMultipleFilter p D P N s) W Q hW hQ
    (fun P hP ↦ hasSum_zetaDivisibilityPrefixFilter p D N hP hs)
  have h := (hasSum_zetaDivisibilityPrefixFilter p D N
    (Finset.prod_pos (fun a ha ↦ (hW a ha).pos)) hs).sub hm
  apply h.congr_fun
  intro n
  have hi : (fun P ↦ zetaDivisibilityPrefixCoefficient D P n) =
      (fun P ↦ if P ∣ n then zetaDivisibilityPrefixCoefficient D 1 n else 0) :=
    funext (fun P ↦ zetaDivisibilityPrefixCoefficient_eq_indicator D P n)
  have ht : primeSquareMultipleTransform
      (fun P ↦ zetaDivisibilityPrefixCoefficient D P n * zetaPrimeFilterKernel p N s n) W Q =
      primeSquareMultipleMask W Q n * zetaDivisibilityPrefixCoefficient D 1 n *
        zetaPrimeFilterKernel p N s n := by
    have hlin := primeSquareMultipleTransform_add_mul
      (fun P ↦ zetaDivisibilityPrefixCoefficient D P n) (fun _ ↦ 0) W Q
      (zetaPrimeFilterKernel p N s n) 0
    simp only [mul_zero, add_zero] at hlin
    rw [hlin, hi, primeSquareMultipleTransform, ← primeSquareMultipleMask_mul_eq W Q hW hQ]
  rw [ht, zetaDivisibilityPrefixCoefficient_eq_indicator D (∏ a ∈ W, a) n]
  by_cases hw : (∏ a ∈ W, a) ∣ n <;> by_cases hq : ∃ a ∈ Q, a ^ 2 ∣ n <;>
    simp [primeSquareMultipleMask, hw, hq]

/-- The squarefree prefix is the limit of the actual finite signed
intersection responses. Dominated convergence keeps the full infinite series. -/
theorem tendsto_zetaSquarefreeDivisibilityPrefixFilter (p : Polynomial ℂ) (D N : ℕ)
    (W : Finset ℕ) (hW : ∀ a ∈ W, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun K ↦ zetaMoebiusMultipleFilter p D (∏ a ∈ W, a) N s -
      primeSquareMultipleTransform (fun P ↦ zetaMoebiusMultipleFilter p D P N s)
        W (zetaSquarePrimesThrough K)) atTop (𝓝 (zetaSquarefreeDivisibilityPrefixFilter p D W N s)) := by
  have hsum := (hasSum_zetaDivisibilityPrefixFilter p D N
    (Finset.prod_pos (fun a ha ↦ (hW a ha).pos)) hs).summable.norm
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hsum
    (f := fun K n ↦ (if ∃ a ∈ zetaSquarePrimesThrough K, a ^ 2 ∣ n then 0
      else zetaDivisibilityPrefixCoefficient D (∏ a ∈ W, a) n) * zetaPrimeFilterKernel p N s n)
    (g := fun n ↦ zetaSquarefreeDivisibilityPrefixCoefficient D W n * zetaPrimeFilterKernel p N s n)
    (fun n ↦ ?_) (Eventually.of_forall (fun K n ↦ ?_))
  · unfold zetaSquarefreeDivisibilityPrefixFilter
    convert ht using 1
    funext K
    exact (finite_square_avoidance_hasSum p D N W (zetaSquarePrimesThrough K) hW
      (zetaSquarePrimesThrough_prime K) hs).tsum_eq.symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_no_primeSquareThrough_iff n] with K hK
    by_cases hq : ∃ a ∈ zetaSquarePrimesThrough K, a ^ 2 ∣ n <;>
      simp_all [zetaSquarefreeDivisibilityPrefixCoefficient]
  · split_ifs
    · simpa only [zero_mul, norm_zero] using norm_nonneg
        (zetaDivisibilityPrefixCoefficient D (∏ a ∈ W, a) n * zetaPrimeFilterKernel p N s n)
    · exact le_rfl

/-- Every squarefree divisibility prefix has an independent factor
bound. Its complete shared-prime correction is multiplicative, so all
first-power intersections can still be summed together downstream. -/
theorem exists_zetaSquarefreeDivisibilityPrefixFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (W : Finset ℕ),
      (∀ a ∈ W, a.Prime) →
      ‖zetaSquarefreeDivisibilityPrefixFilter p D W N (3 / 2 + I * y)‖ ≤
        C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) *
          ∏ a ∈ W, primeSquareCorrectedWeight (zetaSquareSieveExponent r) a := by
  obtain ⟨C, hC, hb⟩ := exists_zetaDivisibilityPrefixFilter_expWeight_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  refine ⟨C * (2 + Real.exp (primeSquareWeightMass τ)), by positivity, ?_⟩
  intro p D N W hW
  let A := C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hτ := zetaSquareSieveExponent_gt_half hr1
  have hw : zetaPrimeExpWeight τ (∏ a ∈ W, a) ≤
      ∏ a ∈ W, primeSquareCorrectedWeight τ a := by
    rw [zetaPrimeExpWeight_prod W (fun a ha ↦ (hW a ha).pos)]
    apply Finset.prod_le_prod (fun a _ ↦ (Real.exp_pos _).le)
    intro a _
    change zetaPrimeExpWeight τ a ≤
      zetaPrimeExpWeight τ a * (1 + zetaPrimeExpWeight τ a)
    nlinarith [sq_nonneg (zetaPrimeExpWeight τ a)]
  apply le_of_tendsto (tendsto_zetaSquarefreeDivisibilityPrefixFilter p D N W hW
    (s := 3 / 2 + I * y) (by norm_num)).norm
  filter_upwards [] with K
  apply (norm_sub_le _ _).trans
  have hbase := (hb p D (∏ a ∈ W, a) N (Finset.prod_pos (fun a ha ↦ (hW a ha).pos))).trans
    (mul_le_mul_of_nonneg_left hw hA)
  have hsq := norm_primeSquareMultipleTransform_le
    (fun P ↦ zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)) W (zetaSquarePrimesThrough K)
    hW (zetaSquarePrimesThrough_prime K) hτ hA (fun P hP ↦ hb p D P N hP)
  exact (add_le_add hbase hsq).trans_eq (by dsimp [A, τ]; ring)

end
end RiemannGaussian
