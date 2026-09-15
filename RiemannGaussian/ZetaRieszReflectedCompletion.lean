/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompletionProduct
import RiemannGaussian.ZetaRieszEndpointTaper

/-!
# Summed reflected prime completion errors

The original reflected order selections are disjoint. Their full summed completion error has an independent polynomial-times-exponential allowance, while the signed tapered core remains intact.
-/

namespace RiemannGaussian.ZetaRieszReflectedCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCompletionProduct ZetaRieszPrimePairConvolution
open ZetaRieszAnnulusJoint ZetaExposedPrimeMoments ZetaRieszMatchedMiddle
open ZetaRieszEndpointTaper

/-- The actual lower complementary orders in the original middle pair
range, including the integer margin needed by its derivative successor. -/
def lowerWing (N : ℕ) : Finset ℕ :=
  (ZetaRieszPairOrders.middleOrders (N + 1)).filter (fun k => 32 * k ≤ 15 * N + 64)

/-- Every selected order obeys the actual product-completion cuts. -/
theorem lowerWing_bounds {N k : ℕ} (hk : k ∈ lowerWing N) :
    N ≤ 8 * k ∧ 32 * k ≤ 15 * N + 64 ∧ k ≤ N + 1 := by
  obtain ⟨hk, hhi⟩ := Finset.mem_filter.mp hk
  obtain ⟨hkM, hlo, _⟩ := Finset.mem_filter.mp hk
  have hkM' := Finset.mem_range.mp hkM
  omega

/-- The selected side stays strictly below the reflection midpoint. -/
theorem lowerWing_below_half {N k : ℕ} (hN : 256 ≤ N) (hk : k ∈ lowerWing N) :
    2 * k < N + 1 := by
  have h := lowerWing_bounds hk
  omega

/-- Every reflected order remains in the literal original middle range. -/
theorem reflected_mem_middle {N k : ℕ} (hk : k ∈ lowerWing N) :
    N + 1 - k ∈ ZetaRieszPairOrders.middleOrders (N + 1) := by
  obtain ⟨hk, _⟩ := Finset.mem_filter.mp hk
  obtain ⟨hkM, hlo, hhi⟩ := Finset.mem_filter.mp hk
  have hkM' := Finset.mem_range.mp hkM
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩

/-- The two reflected sides do not double-count a factorial order. -/
theorem lowerWing_disjoint_reflection (N : ℕ) (hN : 256 ≤ N) :
    Disjoint (lowerWing N) ((lowerWing N).image (fun k => N + 1 - k)) := by
  apply Finset.disjoint_left.mpr
  intro j hj himage
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp himage
  have ha := lowerWing_below_half hN hj
  have hb := lowerWing_below_half hN hk
  have hc := (lowerWing_bounds hk).2.2
  omega

/-- The selected range contains an actual order at the structural threshold. -/
theorem quarter_mem_lowerWing (N : ℕ) (hN : 256 ≤ N) : N / 4 ∈ lowerWing N := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
  · omega

/-- The number of selected orders has the original finite-range budget. -/
theorem lowerWing_card_le (N : ℕ) : (lowerWing N).card ≤ N + 2 := by
  have hsub : lowerWing N ⊆ Finset.range (N + 2) := by
    intro k hk
    exact Finset.mem_range.mpr (by have h := (lowerWing_bounds hk).2.2; omega)
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

/-- Both actual low-leg completion errors, including the original head
coefficient, are retained as one signed correction. -/
def reflectedError (u y : ℝ) (N k : ℕ) : ℂ :=
  (finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
    ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) *
      finiteMoment (intermediatePrimes u N) (N + 1 - k) (3 / 2 + Complex.I * y) -
  ((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    (finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) -
      ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y)) *
        ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)

/-- The tapered high leg and negative complete head product that remain
after the exact low-leg completion errors are separated. -/
def reflectedCore (u y : ℝ) (N k : ℕ) : ℂ :=
  ordinaryPrimeMoment k (3 / 2 + Complex.I * y) *
    taperedMoment (intermediatePrimes u N) (N + 1 - k) (3 / 2 + Complex.I * y)
      (SquarefreeVaughanLogSource.length u N) -
  ((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)

/-- The full reflected head/pair atom retains its core and both errors. -/
theorem reflected_eq_core_add_error (u y : ℝ) (N k : ℕ) :
    sharedAtom u y N k (N + 1 - k) + sharedAtom u y N (N + 1 - k) k =
      reflectedCore u y N k + reflectedError u y N k := by
  rw [reflected_sharedAtom_eq]
  unfold reflectedCore reflectedError
  ring

/-- The whole selected reflected source, with the original product-log
prefactor and both complementary orders kept at each summand. -/
def wingSource (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ lowerWing N,
    (sharedAtom u y N k (N + 1 - k) + sharedAtom u y N (N + 1 - k) k)

/-- The reflected source is exactly a subset of the original middle
order sum, with every selected order counted once. -/
theorem wingSource_eq_union (u y : ℝ) (N : ℕ) (hN : 256 ≤ N) :
    wingSource u y N = ((N + 1 : ℕ) : ℂ) *
      ∑ k ∈ lowerWing N ∪ (lowerWing N).image (fun k => N + 1 - k),
        sharedAtom u y N k (N + 1 - k) := by
  have href : (∑ j ∈ (lowerWing N).image (fun k => N + 1 - k),
      sharedAtom u y N j (N + 1 - j)) =
      ∑ k ∈ lowerWing N, sharedAtom u y N (N + 1 - k) k := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.sub_sub_self (lowerWing_bounds hk).2.2]
    · intro a ha b hb he
      have hA := (lowerWing_bounds ha).2.2
      have hB := (lowerWing_bounds hb).2.2
      dsimp only at he
      omega
  rw [wingSource, Finset.sum_union (lowerWing_disjoint_reflection N hN),
    href, Finset.sum_add_distrib]

/-- The entire retained tapered-minus-complete core on the selected range. -/
def wingCore (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ lowerWing N, reflectedCore u y N k

/-- The complete correction, including all original order and head weights. -/
def wingError (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ lowerWing N, reflectedError u y N k

/-- Summing the exact identities preserves every sign and source factor. -/
theorem wingSource_eq_core_add_error (u y : ℝ) (N : ℕ) :
    wingSource u y N = wingCore u y N + wingError u y N := by
  simp only [wingSource, wingCore, wingError, reflected_eq_core_add_error,
    Finset.sum_add_distrib, mul_add]

/-- Both completion-error products and the actual head coefficient are
uniformly controlled before the selected orders are summed. -/
theorem eventually_norm_reflectedError {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ lowerWing N, ∀ y : ℝ,
      ‖(u : ℂ) ^ (N + 1) * reflectedError u y N k‖ ≤
        4 * Real.exp 2 * (N + 1 : ℝ) ^ 2 * Real.exp (-(5 / 4096 : ℝ) * N) *
          (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by
  filter_upwards [eventually_norm_finite_completion_product hu huh,
    eventually_norm_complete_completion_product hu huh,
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
      (by norm_num : (0 : ℝ) ≤ 2 / 3) huh,
    eventually_ge_atTop 256] with N hfinite hcomplete hLN hN
  intro k hk y
  obtain ⟨hklo, hkhi, hkM⟩ := lowerWing_bounds hk
  have hf := hfinite k (N + 1 - k) hklo (by omega) (by omega) y (intermediatePrimes u N)
  have hb := hcomplete (k + 1) (N + 1 - k) (by omega) (by omega) (by omega) y
  have hc : ‖((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (SquarefreeVaughanLogSource.length_pos u N).le]
    apply (div_le_one (SquarefreeVaughanLogSource.length_pos u N)).mpr
    have hkn : (k + 1 : ℕ) ≤ N := by omega
    have hkc : (k + 1 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hkn
    nlinarith [hLN, Nat.cast_nonneg (α := ℝ) N]
  let A : ℂ := (finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
    ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) *
      finiteMoment (intermediatePrimes u N) (N + 1 - k) (3 / 2 + Complex.I * y)
  let B : ℂ := (finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) -
    ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y)) *
      ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)
  have he : (u : ℂ) ^ (N + 1) * reflectedError u y N k = (u : ℂ) ^ (N + 1) * A -
      (((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ((u : ℂ) ^ (N + 1) * B) := by
    dsimp [reflectedError, A, B]
    ring
  rw [he]
  calc
    _ ≤ ‖(u : ℂ) ^ (N + 1) * A‖ +
        ‖(((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          ((u : ℂ) ^ (N + 1) * B)‖ := norm_sub_le _ _
    _ ≤ ‖(u : ℂ) ^ (N + 1) * A‖ + ‖(u : ℂ) ^ (N + 1) * B‖ := by
      apply add_le_add le_rfl
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := by dsimp only [A, B]; nlinarith only [hf, hb]

/-- The complete selected correction has a geometric allowance after
every summation, derivative and product-logarithm factor is included. -/
theorem eventually_norm_wingError {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ,
      ‖(u : ℂ) ^ (N + 1) * wingError u y N‖ ≤
        8 * Real.exp 2 * (N + 1 : ℝ) ^ 4 * Real.exp (-(5 / 4096 : ℝ) * N) *
          (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by
  filter_upwards [eventually_norm_reflectedError hu huh] with N hN
  intro y
  let B : ℝ := 4 * Real.exp 2 * (N + 1 : ℝ) ^ 2 * Real.exp (-(5 / 4096 : ℝ) * N) *
    (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcard : ((lowerWing N).card : ℝ) ≤ N + 2 := by exact_mod_cast lowerWing_card_le N
  have hcost : (N + 1 : ℝ) * (lowerWing N).card ≤ 2 * (N + 1 : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ N + 1),
      Nat.cast_nonneg (α := ℝ) N]
  have he : (u : ℂ) ^ (N + 1) * wingError u y N = ((N + 1 : ℕ) : ℂ) *
      ∑ k ∈ lowerWing N, (u : ℂ) ^ (N + 1) * reflectedError u y N k := by
    rw [wingError, ← Finset.mul_sum]
    ring
  rw [he, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ) * ∑ k ∈ lowerWing N,
        ‖(u : ℂ) ^ (N + 1) * reflectedError u y N k‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ ≤ ((N + 1 : ℕ) : ℝ) * ∑ _k ∈ lowerWing N, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => hN k hk y)) (Nat.cast_nonneg _)
    _ = ((N + 1 : ℝ) * (lowerWing N).card) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ (2 * (N + 1 : ℝ) ^ 2) * B := mul_le_mul_of_nonneg_right hcost hB
    _ = _ := by dsimp only [B]; ring

/-- The full correction vanishes for every moving height, independently
of hypothetical zeros or cancellation in the remaining tapered core. -/
theorem tendsto_wingError (y : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * wingError u (y N) N) atTop (nhds 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_norm_wingError hu huh] with N hN
    exact hN (y N))
  let r : ℝ := Real.exp (-(5 / 8192 : ℝ))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he (N : ℕ) : Real.exp (-(5 / 4096 : ℝ) * N) = r ^ N * r ^ N := by
    dsimp only [r]
    rw [← mul_pow, ← Real.exp_add,
      show -(5 / 8192 : ℝ) + -(5 / 8192 : ℝ) = -(5 / 4096 : ℝ) by norm_num,
      ← Real.exp_nat_mul]
    congr 1
    ring
  have hq := ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric hr0 hr1
  have h := (hq.mul hq).const_mul
    (8 * Real.exp 2 * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [he]
  ring

/-- Replacing the whole selected reflected source by its tapered core
has independently vanishing error, with the original normalization. -/
theorem tendsto_wingSource_sub_core (y : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * (wingSource u (y N) N - wingCore u (y N) N))
      atTop (nhds 0) := by
  simpa only [wingSource_eq_core_add_error, add_sub_cancel_left] using tendsto_wingError y hu huh

end
end RiemannGaussian.ZetaRieszReflectedCompletion
