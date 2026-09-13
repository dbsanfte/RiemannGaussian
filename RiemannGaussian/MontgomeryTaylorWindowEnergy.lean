/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorInverseSampling
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Correlation budgets for every consecutive-window weight family

The coefficients at different positions in a window need not be equal.
Only their total at each separation enters the global energy budget. This
keeps position-dependent correlation weights available to a numerical
certificate, without charging any pair of zeros more than once.

The statements below are finite identities and inequalities. A numerical
zero-proportion claim additionally requires a proved uniform kernel floor
and the analytic transfer to the literal zeta counting functions.
-/

namespace RiemannGaussian.MontgomeryTaylorWindowEnergy
noncomputable section
open scoped BigOperators

/-- Nonnegative entries in any translated subinterval are paid by the full
interval. Both endpoints are expressed as counts, so the empty case is kept. -/
theorem sum_shift_le_sum_range {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    {n k offset : ℕ} (h : k + offset ≤ n) :
    (∑ j ∈ Finset.range k, f (j + offset)) ≤ ∑ j ∈ Finset.range n, f j := by
  have hinj : Function.Injective (fun j : ℕ => j + offset) := by
    intro i j hij
    exact Nat.add_right_cancel hij
  rw [← Finset.sum_image (fun i _ j _ hij => hinj hij)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro i _ _
    exact hf i

/-- All translates of a position-weighted local sum cost only the sum of
its weights. The weights may be nonuniform. -/
theorem weighted_translates_le {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (c : ℕ → ℝ) {q k n : ℕ} (hc : ∀ i < q, 0 ≤ c i)
    (hfit : ∀ i < q, k + i ≤ n) :
    (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range q, c i * f (j + i)) ≤
      (∑ i ∈ Finset.range q, c i) * ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_shift_le_sum_range hf (hfit i (Finset.mem_range.mp hi)))
    (hc i (Finset.mem_range.mp hi))

/-- Squared correlations indexed by their positive separation. -/
def lagEnergy (w : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.range n, 2 *
    ∑ i ∈ Finset.range (n - (s + 1)), w (x (i + s + 1) - x i)

/-- A window of `q + 1` points with an independent nonnegative weight at
every pair position. The first argument of `c` is the separation minus one. -/
def windowEnergy (w : ℝ → ℝ) (c : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) (q start : ℕ) : ℝ :=
  ∑ s ∈ Finset.range q, ∑ i ∈ Finset.range (q - s),
    c s i * w (x (start + i + s + 1) - x (start + i))

/-- The pressure on each gap also has independent position weights. -/
def windowPressure (p : ℕ → ℝ) (x : ℕ → ℝ) (q start : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q, p i * (x (start + i + 1) - x (start + i))

/-- Averaging arbitrary window weights preserves the full correlation
budget when the weights at each separation sum to at most two. -/
theorem sum_windowEnergy_le_lagEnergy (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) {q n : ℕ} (hqn : q ≤ n)
    (hc : ∀ s < q, ∀ i < q - s, 0 ≤ c s i)
    (hbudget : ∀ s < q, (∑ i ∈ Finset.range (q - s), c s i) ≤ 2) :
    (∑ j ∈ Finset.range (n - q), windowEnergy w c x q j) ≤
      lagEnergy w x n := by
  unfold windowEnergy lagEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ s ∈ Finset.range q, 2 *
        ∑ i ∈ Finset.range (n - (s + 1)), w (x (i + s + 1) - x i) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsq := Finset.mem_range.mp hs
      have htrans := weighted_translates_le
        (f := fun i => w (x (i + s + 1) - x i)) (fun i => hw _)
        (c s) (k := n - q) (n := n - (s + 1))
        (hc s hsq) (by intro i hi; omega)
      have hsum : 0 ≤ ∑ i ∈ Finset.range (n - (s + 1)),
          w (x (i + s + 1) - x i) := Finset.sum_nonneg fun i _ => hw _
      exact htrans.trans (mul_le_mul_of_nonneg_right (hbudget s hsq) hsum)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hqn)
      intro i _ _
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hw _)

/-- The sum of consecutive gaps telescopes exactly, including an empty
interval. -/
theorem sum_gaps (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i)) = x n - x 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Every pressure family pays only its total weight times the full span. -/
theorem sum_windowPressure_le (p : ℕ → ℝ) (x : ℕ → ℝ)
    (hx : Monotone x) {q n : ℕ} (hqn : q ≤ n)
    (hp : ∀ i < q, 0 ≤ p i) :
    (∑ j ∈ Finset.range (n - q), windowPressure p x q j) ≤
      (∑ i ∈ Finset.range q, p i) * (x (n - 1) - x 0) := by
  have h := weighted_translates_le
    (f := fun i => x (i + 1) - x i)
    (fun i => sub_nonneg.mpr (hx (by omega))) p
    (k := n - q) (n := n - 1) hp (by intro i hi; omega)
  simpa only [windowPressure, sum_gaps] using h

/-- A uniform window floor produces a global energy-versus-span inequality
for every admissible position-weight family. No numerical floor is assumed
to have been verified by this transport theorem. -/
theorem floor_transport (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t)
    (c : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (x : ℕ → ℝ) (hx : Monotone x)
    {q n : ℕ} (hqn : q ≤ n) {A : ℝ}
    (hc : ∀ s < q, ∀ i < q - s, 0 ≤ c s i)
    (hbudget : ∀ s < q, (∑ i ∈ Finset.range (q - s), c s i) ≤ 2)
    (hp : ∀ i < q, 0 ≤ p i)
    (hfloor : ∀ start < n - q,
      A ≤ windowEnergy w c x q start + windowPressure p x q start) :
    A * (n - q : ℕ) ≤ lagEnergy w x n +
      (∑ i ∈ Finset.range q, p i) * (x (n - 1) - x 0) := by
  have hsum := Finset.sum_le_sum (s := Finset.range (n - q))
    (fun start hstart => hfloor start (Finset.mem_range.mp hstart))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_add_distrib] at hsum
  have he := sum_windowEnergy_le_lagEnergy w hw c x hqn hc hbudget
  have hp' := sum_windowPressure_le p x hx hqn hp
  nlinarith

/-- Reindex all strictly increasing pairs by their positive separation.
The empty list and the last, empty separation are included. -/
theorem upperTriangle_sum_by_separation (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ s ∈ Finset.range n, ∑ i ∈ Finset.range (n - (s + 1)),
      f i (i + s + 1)) =
      ∑ p ∈ (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2),
        f p.1 p.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => (p.2, p.2 + p.1 + 1)) ?_ ?_ ?_ ?_
  · rintro ⟨s, i⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range] at h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨s, i⟩ ha ⟨t, j⟩ hb hij
    simp only [Prod.mk.injEq] at hij
    have hi : i = j := hij.1
    have hs : s = t := by omega
    subst j
    subst t
    rfl
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    refine ⟨⟨j - i - 1, i⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · change (i, i + (j - i - 1) + 1) = (i, j)
      exact Prod.ext rfl (by omega)
  · intro p _
    rfl

/-- An even correlation function counts the two orientations of each
distinct pair equally. This identifies the separation ledger with the
complete ordered-pair energy. -/
theorem lagEnergy_eq_orderedPairs (w : ℝ → ℝ) (hw : ∀ t, w (-t) = w t)
    (x : ℕ → ℝ) (n : ℕ) :
    lagEnergy w x n =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i = j then 0 else w (x j - x i) := by
  have hsym : ∀ i j, w (x i - x j) = w (x j - x i) := by
    intro i j
    rw [show x i - x j = -(x j - x i) by ring, hw]
  have hsplit : ∀ i j : ℕ,
      (if i = j then 0 else w (x j - x i)) =
        (if i < j then w (x j - x i) else 0) +
          (if j < i then w (x i - x j) else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt_of_ge hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt_of_ge hij.le, hsym]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hswap :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if j < i then w (x i - x j) else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i < j then w (x j - x i) else 0 := Finset.sum_comm
  rw [hswap, ← two_mul]
  unfold lagEnergy
  rw [← Finset.mul_sum,
    upperTriangle_sum_by_separation (fun i j => w (x j - x i)) n]
  congr 1
  rw [Finset.sum_filter, Finset.sum_product]

end
end RiemannGaussian.MontgomeryTaylorWindowEnergy
