import RiemannGaussian.NatRectangleEnergy
import RiemannGaussian.EtaMomentInverseReduction

/-!
# The signed product fibers of the actual moment inverse

The outer inverse weight and inner Möbius weight meet at their exact
integer product. The coefficient on a product is the signed sum of its
actual rectangular factor pairs. The full complex grouping identity
precedes the coefficient mass and collision-energy estimates.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact signed multiplicity of one product in the original
outer-inverse and inner-Möbius rectangle. -/
def pairedEtaInverseProductCoefficient (E D n : ℕ) : ℤ :=
  ∑ p ∈ ((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
    (fun p : ℕ × ℕ ↦ p.1 * p.2 = n), μ p.2

/-- Every actual factor pair lies in the full positive product range. -/
theorem mul_mem_Icc_product {E D : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)) :
    p.1 * p.2 ∈ Finset.Icc 1 (E * D) := by
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨ha1, haE⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hb1, hbD⟩ := Finset.mem_Icc.mp hp2
  exact Finset.mem_Icc.mpr ⟨by nlinarith, Nat.mul_le_mul haE hbD⟩

/-- Exact product grouping retains every inner Möbius sign and all
complex data carried by the original divided cutoff and translated center. -/
theorem sum_pairedEtaInverseProductCoefficient_mul (E D : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (E * D), (pairedEtaInverseProductCoefficient E D n : ℂ) * f n) =
      ∑ d ∈ Finset.Icc 1 E, ∑ e ∈ Finset.Icc 1 D, (μ e : ℂ) * f (d * e) := by
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ ↦ (μ p.2 : ℂ) * f (p.1 * p.2))]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)) (t := Finset.Icc 1 (E * D))
    (g := fun p : ℕ × ℕ ↦ p.1 * p.2) (fun p hp ↦ mul_mem_Icc_product hp)
    (fun p : ℕ × ℕ ↦ (μ p.2 : ℂ) * f (p.1 * p.2))
  calc
    _ = ∑ n ∈ Finset.Icc 1 (E * D),
        ∑ p ∈ ((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
          (fun p : ℕ × ℕ ↦ p.1 * p.2 = n), (μ p.2 : ℂ) * f (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairedEtaInverseProductCoefficient, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := h

/-- The signed product coefficient is bounded only after its entire
fiber is summed; its absolute value is at most the true fiber cardinality. -/
theorem abs_pairedEtaInverseProductCoefficient_le_card (E D n : ℕ) :
    |pairedEtaInverseProductCoefficient E D n| ≤
      (((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
        (fun p : ℕ × ℕ ↦ p.1 * p.2 = n)).card := by
  unfold pairedEtaInverseProductCoefficient
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ ((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
        (fun p : ℕ × ℕ ↦ p.1 * p.2 = n), (1 : ℤ) :=
      Finset.sum_le_sum (fun p _ ↦ ArithmeticFunction.abs_moebius_le_one)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The absolute mass of all signed inverse product coefficients is
bounded by the actual rectangular area, without a divisor-function loss. -/
theorem sum_abs_pairedEtaInverseProductCoefficient_le (E D : ℕ) :
    (∑ n ∈ Finset.Icc 1 (E * D), |(pairedEtaInverseProductCoefficient E D n : ℝ)|) ≤
      (E : ℝ) * D := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (E * D),
        ((((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
          (fun p : ℕ × ℕ ↦ p.1 * p.2 = n)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact_mod_cast abs_pairedEtaInverseProductCoefficient_le_card E D n
    _ = _ := by
      rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
      have he : (((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
          (fun p : ℕ × ℕ ↦ p.1 * p.2 ∈ Finset.Icc 1 (E * D))) =
          (Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D) := by
        exact Finset.filter_eq_self.mpr (fun p hp ↦ mul_mem_Icc_product hp)
      rw [he, Finset.card_product]
      simp only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul]

/-- The coefficient energy is bounded by the complete rectangular
product-collision count, with coincident factorizations accounted for. -/
theorem sum_sq_pairedEtaInverseProductCoefficient_le_energy (E D : ℕ) :
    (∑ n ∈ Finset.Icc 1 (E * D), (pairedEtaInverseProductCoefficient E D n : ℝ) ^ 2) ≤
      (Finset.mulEnergy (Finset.Icc 1 E) (Finset.Icc 1 D) : ℝ) := by
  classical
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (E * D),
        ((((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
          (fun p : ℕ × ℕ ↦ p.1 * p.2 = n)).card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have h : |(pairedEtaInverseProductCoefficient E D n : ℝ)| ≤
          ((((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
            (fun p : ℕ × ℕ ↦ p.1 * p.2 = n)).card : ℝ) := by
        exact_mod_cast abs_pairedEtaInverseProductCoefficient_le_card E D n
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr h
    _ = _ := by
      rw [Finset.mulEnergy_eq_sum_sq']
      push_cast
      symm
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hn
        exact mul_mem_Icc_product (E := E) (D := D) (p := (a, b))
          (Finset.mem_product.mpr ⟨ha, hb⟩)
      · intro n hn hnnot
        have he : (((Finset.Icc 1 E) ×ˢ (Finset.Icc 1 D)).filter
            (fun p : ℕ × ℕ ↦ p.1 * p.2 = n)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp heq
          apply hnnot
          rw [← heq]
          exact Finset.mul_mem_mul (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
        rw [he, Finset.card_empty, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The actual signed inverse product coefficients have area times
squared-logarithmic energy, retaining both original divisor ranges. -/
theorem sum_sq_pairedEtaInverseProductCoefficient_le_log_sq {E : ℕ}
    (hE : 1 ≤ E) (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 (E * D), (pairedEtaInverseProductCoefficient E D n : ℝ) ^ 2) ≤
      (E : ℝ) * D * (1 + Real.log E) ^ 2 :=
  (sum_sq_pairedEtaInverseProductCoefficient_le_energy E D).trans
    (mulEnergy_Icc_le_log_sq hE D)

end

end RiemannGaussian
