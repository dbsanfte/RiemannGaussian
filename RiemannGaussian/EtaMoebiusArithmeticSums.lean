import RiemannGaussian.EtaMoebiusContinuumEnergy
import RiemannGaussian.EtaMoebiusFinitePrefix

/-!
# Exact finite divisor sums behind the continuum Möbius arithmetic

The actual odd/even signs are retained while finite rectangular sums are
regrouped on their product fibers. The arithmetic cutoff survives as a
condition on the first divisor. This applies on every physical cell,
including cells beyond the arithmetic cutoff.
-/

open Complex
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The signed eta harmonic prefix at an exact integer endpoint. -/
def pairedEtaArithmeticHarmonicPrefix (L : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 L, (pairedEtaDirichletSign m : ℝ) / m

/-- The complete weighted harmonic correction of the actual balanced Möbius primitive. -/
def pairedEtaMoebiusArithmeticHarmonic (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n / n

/-- The signed divisor coefficient of the complete arithmetic candidate, retaining the original cutoff on the Möbius divisor. -/
def pairedEtaMoebiusArithmeticDivisor (M : ℕ) (w : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ p ∈ l.divisorsAntidiagonal,
    if p.1 ≤ M then (μ p.1 : ℝ) * w p.1 * (pairedEtaDirichletSign p.2 : ℝ) else 0

/-- Consecutive odd/even pairs are exactly the original signed eta prefix for every real-valued summand. -/
theorem sum_pairedEtaDirichletSign_mul_eq_pairs (N : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (2 * N), (pairedEtaDirichletSign m : ℝ) * f m) =
      ∑ n ∈ Finset.range N, (f (2 * n + 1) - f (2 * n + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      ih, Finset.sum_range_succ]
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod]
    ring

private theorem real_divisor_prefix (L : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ l ∈ Finset.Icc 1 L, ∑ p ∈ l.divisorsAntidiagonal, f p.1 p.2) =
      ∑ d ∈ Finset.Icc 1 L, ∑ m ∈ Finset.Icc 1 (L / d), f d m := by
  have h := sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix L (fun d m ↦ (f d m : ℂ))
  exact_mod_cast h

private theorem sum_product_cutoff {d : ℕ} (hd : 1 ≤ d) (L : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 L, if d * m ≤ L then f m else 0) =
      ∑ m ∈ Finset.Icc 1 (L / d), f m := by
  have hs : Finset.Icc 1 (L / d) ⊆ Finset.Icc 1 L :=
    Finset.Icc_subset_Icc le_rfl (Nat.div_le_self _ _)
  calc
    _ = ∑ m ∈ Finset.Icc 1 (L / d), if d * m ≤ L then f m else 0 := by
      symm
      apply Finset.sum_subset hs
      intro m hm hnot
      have hml : ¬ m ≤ L / d := by
        intro h
        exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, h⟩)
      have hprod : ¬ d * m ≤ L := by
        intro h
        exact hml ((Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using h))
      simp [hprod]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      have hp := (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp hm).2
      simp only [if_pos (show d * m ≤ L by simpa only [mul_comm] using hp)]

/-- The whole finite rectangular product sum is exactly the divisor-fiber sum with its original Möbius cutoff retained, on either side of that cutoff. -/
theorem sum_rectangle_product_cutoff_eq_divisors (M L : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 L, if d * m ≤ L then f d m else 0) =
      ∑ l ∈ Finset.Icc 1 L, ∑ p ∈ l.divisorsAntidiagonal,
        if p.1 ≤ M then f p.1 p.2 else 0 := by
  rw [real_divisor_prefix L (fun d m ↦ if d ≤ M then f d m else 0)]
  have hleft : (∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 L,
      if d * m ≤ L then f d m else 0) =
      ∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 (L / d), f d m := by
    apply Finset.sum_congr rfl
    intro d hd
    exact sum_product_cutoff (Finset.mem_Icc.mp hd).1 L (f d)
  rw [hleft]
  rcases le_total M L with hML | hLM
  · calc
      _ = ∑ d ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 (L / d), if d ≤ M then f d m else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [if_pos (Finset.mem_Icc.mp hd).2]
      _ = _ := by
        apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hML)
        intro d hd hnot
        have h : ¬ d ≤ M := fun h ↦ hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, h⟩)
        simp [h]
  · calc
      _ = ∑ d ∈ Finset.Icc 1 L, ∑ m ∈ Finset.Icc 1 (L / d), f d m := by
        symm
        apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hLM)
        intro d hd hnot
        have h : L < d := by
          by_contra! h
          exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, h⟩)
        simp [Nat.div_eq_of_lt h]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [if_pos ((Finset.mem_Icc.mp hd).2.trans hLM)]

/-- The full signed harmonic divisor prefix is exactly the product-cutoff harmonic rectangle; both arithmetic signs and the truncated divisor are retained. -/
theorem sum_pairedEtaMoebiusArithmeticDivisor_div_eq_rectangle (M L : ℕ) (w : ℕ → ℝ) :
    (∑ l ∈ Finset.Icc 1 L, pairedEtaMoebiusArithmeticDivisor M w l / l) =
      ∑ m ∈ Finset.Icc 1 L, (pairedEtaDirichletSign m : ℝ) / m *
        ∑ n ∈ Finset.Icc 1 M, if n * m ≤ L then (μ n : ℝ) * w n / n else 0 := by
  calc
    _ = ∑ l ∈ Finset.Icc 1 L, ∑ p ∈ l.divisorsAntidiagonal,
        if p.1 ≤ M then (μ p.1 : ℝ) * w p.1 * (pairedEtaDirichletSign p.2 : ℝ) /
          ((p.1 : ℝ) * p.2) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [pairedEtaMoebiusArithmeticDivisor, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← he, Nat.cast_mul]
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 L,
        if n * m ≤ L then (μ n : ℝ) * w n * (pairedEtaDirichletSign m : ℝ) /
          ((n : ℝ) * m) else 0 :=
      (sum_rectangle_product_cutoff_eq_divisors M L (fun n m ↦
        (μ n : ℝ) * w n * (pairedEtaDirichletSign m : ℝ) / ((n : ℝ) * m))).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs
      · simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [mul_zero]

end

end RiemannGaussian
