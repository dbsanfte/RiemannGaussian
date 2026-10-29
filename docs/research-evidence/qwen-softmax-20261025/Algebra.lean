import RiemannGaussian.EtaInverseProductCoefficients
import RiemannGaussian.FiniteAbelVariation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

namespace SoftmaxAlgebraAudit
noncomputable section
open Classical

/-- Exact pushforward of exponential mass to distinct original logits.
No rounding or replacement of an original logit is permitted. -/
theorem partition_by_equal_logits {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (g : ι → κ) (v : κ → ℝ) (m : ℝ) :
    (∑ i ∈ s, Real.exp (v (g i) - m)) =
      ∑ u ∈ s.image g,
        (((s.filter fun i => g i = u).card : ℝ) * Real.exp (v u - m)) := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image g) (g := g)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i => Real.exp (v (g i) - m))
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    _ = ∑ _i ∈ s.filter (fun i => g i = u), Real.exp (v u - m) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp

/-- A consumer can aggregate original values within each equal-logit fibre
before multiplication by that fibre's exponential. -/
theorem numerator_by_equal_logits {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (g : ι → κ) (v : κ → ℝ) (a : ι → ℝ) (m : ℝ) :
    (∑ i ∈ s, Real.exp (v (g i) - m) * a i) =
      ∑ u ∈ s.image g,
        Real.exp (v u - m) * (∑ i ∈ s.filter (fun i => g i = u), a i) := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image g) (g := g)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i => Real.exp (v (g i) - m) * a i)
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Normalize an unnormalized weighted consumer once at its output. -/
theorem deferred_normalization {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (Z : ℝ) :
    (∑ i ∈ s, (w i / Z) * a i) =
      (∑ i ∈ s, w i * a i) / Z := by
  simp_rw [div_mul_eq_mul_div]
  exact (Finset.sum_div s _ Z).symm

/-- A sparse exact logit update only changes the partition on its support. -/
theorem sparse_partition_update {ι : Type*} (s t : Finset ι)
    (w w' : ι → ℝ) (ht : t ⊆ s) (h : ∀ i ∈ s, i ∉ t → w' i = w i) :
    (∑ i ∈ s, w' i) =
      (∑ i ∈ s, w i) + ∑ i ∈ t, (w' i - w i) := by
  have he : (∑ i ∈ s, (w' i - w i)) = ∑ i ∈ t, (w' i - w i) := by
    symm
    apply Finset.sum_subset ht
    intro i hi hit
    rw [h i hi hit, sub_self]
  rw [Finset.sum_sub_distrib] at he
  linarith

/-- Softmax logits are identifiable up to one common additive constant.
This prohibits arbitrary exact quantization of all real softmax outputs. -/
theorem same_softmax_implies_common_shift {ι : Type*}
    (x y : ι → ℝ) (Z W : ℝ) (hZ : Z ≠ 0) (hW : W ≠ 0)
    (h : ∀ i, Real.exp (x i) / Z = Real.exp (y i) / W)
    (i j : ι) : x i - y i = x j - y j := by
  apply Real.exp_injective
  simp only [Real.exp_sub]
  have hi := h i
  have hj := h j
  have hxi : Real.exp (y i) ≠ 0 := Real.exp_ne_zero _
  have hxj : Real.exp (y j) ≠ 0 := Real.exp_ne_zero _
  field_simp at hi hj ⊢
  apply (mul_right_cancel₀ hW)
  calc
    (Real.exp (x i) * Real.exp (y j)) * W =
        (Real.exp (x i) * W) * Real.exp (y j) := by ring
    _ = (Z * Real.exp (y i)) * Real.exp (y j) := by rw [hi]
    _ = Real.exp (y i) * (W * Real.exp (x j)) := by rw [hj]; ring
    _ = (Real.exp (y i) * Real.exp (x j)) * W := by ring

theorem common_shift_preserves_softmax {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (c : ℝ) (i : ι) :
    Real.exp (x i + c) / (∑ j ∈ s, Real.exp (x j + c)) =
      Real.exp (x i) / (∑ j ∈ s, Real.exp (x j)) := by
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero c)

theorem full_softmax_rigidity {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) :
    (∀ i, Real.exp (x i) / (∑ j, Real.exp (x j)) =
      Real.exp (y i) / (∑ j, Real.exp (y j))) ↔
      ∃ c, ∀ i, x i = y i + c := by
  constructor
  · intro h
    let j : ι := Classical.choice inferInstance
    refine ⟨x j - y j, ?_⟩
    intro i
    have hZ : (∑ j, Real.exp (x j)) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun j _ => Real.exp_pos (x j)) Finset.univ_nonempty)
    have hW : (∑ j, Real.exp (y j)) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun j _ => Real.exp_pos (y j)) Finset.univ_nonempty)
    have hr := same_softmax_implies_common_shift x y _ _ hZ hW h i j
    linarith
  · rintro ⟨c, hc⟩ i
    simp_rw [hc]
    exact common_shift_preserves_softmax Finset.univ y c i

/-- This deliberately leaves the scalar evaluator and ordered consumer
opaque. They may be deterministic machine operations on finite bitstrings.
It proves a value-transport contract, not a GPU cache implementation. -/
theorem memoized_evaluation_preserves_ordered_consumer
    {α β κ γ : Type*} (xs : List α) (key : α → κ) (representative : κ → α)
    (evaluate : α → β) (consume : List β → γ)
    (h : ∀ a ∈ xs, representative (key a) = a) :
    consume (xs.map evaluate) =
      consume (xs.map (fun a => evaluate (representative (key a)))) := by
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [h a ha]

/-- Specialize the repository's exact Abel identity to real-valued
softmax numerators, retaining every original prefix. -/
theorem numerator_via_value_prefixes (w a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * a n) =
      w N * (∑ n ∈ Finset.range (N + 1), a n) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), a k) := by
  have h := RiemannGaussian.FiniteAbelVariation.weighted_sum_eq
    (fun n => (w n : ℂ)) (fun n => (a n : ℂ)) N
  have hr := congrArg Complex.re h
  simpa using hr

#print axioms partition_by_equal_logits
#print axioms numerator_by_equal_logits
#print axioms deferred_normalization
#print axioms sparse_partition_update
#print axioms same_softmax_implies_common_shift
#print axioms common_shift_preserves_softmax
#print axioms full_softmax_rigidity
#print axioms memoized_evaluation_preserves_ordered_consumer
#print axioms numerator_via_value_prefixes

end
end SoftmaxAlgebraAudit
