import RiemannGaussian.FiniteDiscreteSobolev

/-!
# Disjoint finite sampling blocks

Separated integer sample points have disjoint forward blocks. The exact
block reindexing bounds their total nonnegative mass by a literal ambient
interval. Applying the discrete Sobolev estimate gives a sampling bound
with both the sequence energy and its difference energy explicit.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Ordered separation makes the complete arithmetic block coordinates
injective; both sample and within-block positions are retained. -/
theorem separated_sampling_blocks_injective (s : Finset ℕ) (h : ℕ)
    (hsep : ∀ n ∈ s, ∀ m ∈ s, n < m → n + h ≤ m) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) (s ×ˢ Finset.range h : Finset (ℕ × ℕ)) := by
  intro p hp q hq heq
  change p.1 + p.2 = q.1 + q.2 at heq
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  have hpj := Finset.mem_range.mp hp2
  have hqj := Finset.mem_range.mp hq2
  have hn : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with hlt | he | hgt
    · have hs := hsep p.1 hp1 q.1 hq1 hlt
      omega
    · exact he
    · have hs := hsep q.1 hq1 p.1 hp1 hgt
      omega
  apply Prod.ext hn
  omega

/-- Summing every separated block costs at most one ambient double
period, without dropping or duplicating an arithmetic sample. -/
theorem sum_separated_sampling_blocks_le (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (s : Finset ℕ) {h Q : ℕ} (hhQ : h ≤ Q)
    (hsQ : ∀ n ∈ s, n < Q)
    (hsep : ∀ n ∈ s, ∀ m ∈ s, n < m → n + h ≤ m) :
    (∑ n ∈ s, ∑ j ∈ Finset.range h, v (n + j)) ≤ ∑ k ∈ Finset.range (2 * Q), v k := by
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ ↦ v (p.1 + p.2))]
  have hi := separated_sampling_blocks_injective s h hsep
  rw [← Finset.sum_image hi]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun k _ _ ↦ hv k)
  intro k hk
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hps, hpj⟩ := Finset.mem_product.mp hp
  have hn := hsQ p.1 hps
  have hj := Finset.mem_range.mp hpj
  apply Finset.mem_range.mpr
  omega

/-- The square mass of a periodically extended sequence on two complete
periods is exactly twice its one-period mass. -/
theorem sum_range_two_mul_norm_sq_periodic (f : ℕ → ℂ) {Q : ℕ}
    (hf : Function.Periodic f Q) :
    (∑ k ∈ Finset.range (2 * Q), ‖f k‖ ^ 2) =
      2 * ∑ k ∈ Finset.range Q, ‖f k‖ ^ 2 := by
  have hp : Function.Periodic (fun k ↦ ‖f k‖ ^ 2) Q :=
    fun k ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (hf k)
  rw [show 2 * Q = Q * 2 by ring, sum_range_nat_periodic_mul hp]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- Forward differences inherit the exact original integer period. -/
theorem periodic_forward_difference (f : ℕ → ℂ) {Q : ℕ}
    (hf : Function.Periodic f Q) :
    Function.Periodic (fun k ↦ f (k + 1) - f k) Q := by
  intro k
  change f (k + Q + 1) - f (k + Q) = f (k + 1) - f k
  rw [show k + Q + 1 = k + 1 + Q by omega, hf (k + 1), hf k]

/-- A finite periodic sequence sampled at separated points has an
explicit energy bound with its exact forward-difference cost. -/
theorem sum_norm_sq_separated_sampling_le (f : ℕ → ℂ) (s : Finset ℕ)
    {h Q : ℕ} (hh : 0 < h) (hhQ : h ≤ Q) (hf : Function.Periodic f Q)
    (hsQ : ∀ n ∈ s, n < Q)
    (hsep : ∀ n ∈ s, ∀ m ∈ s, n < m → n + h ≤ m) :
    (∑ n ∈ s, ‖f n‖ ^ 2) ≤
      (4 / (h : ℝ)) * (∑ k ∈ Finset.range Q, ‖f k‖ ^ 2) +
        4 * h * ∑ k ∈ Finset.range Q, ‖f (k + 1) - f k‖ ^ 2 := by
  have hv := sum_separated_sampling_blocks_le (fun n ↦ ‖f n‖ ^ 2)
    (fun _ ↦ sq_nonneg _) s hhQ hsQ hsep
  have hd := sum_separated_sampling_blocks_le (fun n ↦ ‖f (n + 1) - f n‖ ^ 2)
    (fun _ ↦ sq_nonneg _) s hhQ hsQ hsep
  rw [sum_range_two_mul_norm_sq_periodic f hf] at hv
  rw [sum_range_two_mul_norm_sq_periodic _ (periodic_forward_difference f hf)] at hd
  have hs := Finset.sum_le_sum (s := s) (fun n _ ↦ norm_sq_le_discrete_block_sobolev f n hh)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  apply hs.trans
  have hv' := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 / (h : ℝ))
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * h)
  convert add_le_add hv' hd' using 1
  ring

end

end RiemannGaussian
