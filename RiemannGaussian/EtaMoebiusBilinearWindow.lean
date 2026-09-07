import RiemannGaussian.EtaMoebiusBilinearEnergy

/-!
# The explicit physical-window matrix of alternating Möbius prefixes

The coefficients are fixed throughout each averaging window. Counting
the physical cutoffs that contain both products evaluates the remaining
matrix exactly. Its initial square is an all-ones block, so coefficient
energy cannot replace the coherent arithmetic quadratic form.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The exact proportion of physical cutoffs containing both product indices; both subtractions are natural-number truncations. -/
def pairedEtaBilinearPrefixWindowKernel (A L n m : ℕ) : ℝ :=
  ((L - (max n m - A) : ℕ) : ℝ) / L

/-- The physical overlap count is exact even for empty windows or product indices beyond the entire window. -/
theorem card_pairedEtaBilinearPrefixWindow (A L n m : ℕ) :
    ((Finset.range L).filter (fun t ↦ n ≤ A + t ∧ m ≤ A + t)).card = L - (max n m - A) := by
  have he : (Finset.range L).filter (fun t ↦ n ≤ A + t ∧ m ≤ A + t) =
      Finset.Ico (max n m - A) L := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Nat.card_Ico]

/-- Every exact physical overlap weight lies between zero and one, including the empty-window convention inherited from the actual mean square. -/
theorem pairedEtaBilinearPrefixWindowKernel_bounds (A L n m : ℕ) :
    0 ≤ pairedEtaBilinearPrefixWindowKernel A L n m ∧
      pairedEtaBilinearPrefixWindowKernel A L n m ≤ 1 := by
  unfold pairedEtaBilinearPrefixWindowKernel
  constructor
  · positivity
  · by_cases hL : L = 0
    · simp [hL]
    · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hL : (0 : ℝ) < L)).mpr
      simpa only [one_mul] using (show ((L - (max n m - A) : ℕ) : ℝ) ≤ L by
        exact_mod_cast Nat.sub_le L (max n m - A))

/-- The entire initial product square has overlap weight one. It retains all coherent cross terms and cannot be replaced by its diagonal. -/
theorem pairedEtaBilinearPrefixWindowKernel_eq_one {A L n m : ℕ}
    (hL : 0 < L) (hn : n ≤ A) (hm : m ≤ A) :
    pairedEtaBilinearPrefixWindowKernel A L n m = 1 := by
  have hmax : max n m ≤ A := max_le hn hm
  simp only [pairedEtaBilinearPrefixWindowKernel, Nat.sub_eq_zero_of_le hmax, Nat.sub_zero]
  exact div_self (by exact_mod_cast hL.ne')

private theorem sum_window_prefix_pairs (A L : ℕ) (g : ℕ → ℕ → ℂ) :
    (∑ t ∈ Finset.range L, ∑ n ∈ Finset.Icc 1 (A + t), ∑ m ∈ Finset.Icc 1 (A + t), g n m) =
      ∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ Finset.Icc 1 (A + L),
        ((L - (max n m - A) : ℕ) : ℂ) * g n m := by
  have hp (t : ℕ) (ht : t ∈ Finset.range L) :
      (∑ n ∈ Finset.Icc 1 (A + t), ∑ m ∈ Finset.Icc 1 (A + t), g n m) =
        ∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ Finset.Icc 1 (A + L),
          if n ≤ A + t ∧ m ≤ A + t then g n m else 0 := by
    have he : (Finset.Icc 1 (A + L)).filter (fun n ↦ n ≤ A + t) = Finset.Icc 1 (A + t) := by
      ext n
      have htL := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    simp only [← he, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ≤ A + t
    · simp only [hn, true_and, if_true]
    · simp only [hn, false_and, if_false, Finset.sum_const_zero]
  calc
    _ = ∑ t ∈ Finset.range L, ∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ Finset.Icc 1 (A + L),
        if n ≤ A + t ∧ m ≤ A + t then g n m else 0 := Finset.sum_congr rfl hp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_pairedEtaBilinearPrefixWindow]

/-- The original full high-divisor mean square is the explicit finite window matrix acting on the fixed alternating Möbius coefficients, with all phases, products, and cross terms retained. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_window
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho A L D : ℂ) =
      (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
        (∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ Finset.Icc 1 (A + L),
          (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
            (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))) := by
  rw [pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_pairs, sum_window_prefix_pairs]
  apply congrArg (fun z : ℂ ↦ (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 * z)
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  simp only [pairedEtaBilinearPrefixWindowKernel, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

end

end RiemannGaussian
