import RiemannGaussian.EtaMomentDivisorAtomPhysical
import RiemannGaussian.EtaInverseRectanglePhase

/-!
# The actual completed moment inverse on a divisor rectangle

The outer inverse sum and inner Möbius sum are the existing original
terms. Exact product grouping keeps their full complex phase, divided
cutoffs, and translated centers. Only then is the common physical
parity error estimated over the entire rectangle.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The original inverse sum with both actual divisor ranges retained. -/
def pairedEtaCompletedMomentInverseRectangle (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M E D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 E, pairedEtaCompletedMomentInversePartialTerm rho k a M d D

/-- The physical product-range condition places every inner rectangle
cutoff inside its original divided inverse cutoff. -/
theorem pairedEtaCompletedMomentInverseRectangle_inner_cutoff {M E D d : ℕ}
    (hED : E * D ≤ M) (hd : d ∈ Finset.Icc 1 E) : D ≤ M / d := by
  apply (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hd).1).mpr
  calc
    D * d = d * D := Nat.mul_comm D d
    _ ≤ E * D := Nat.mul_le_mul_right D (Finset.mem_Icc.mp hd).2
    _ ≤ M := hED

/-- Grouping the complete original inverse rectangle at exact
products preserves every inner Möbius sign and full moment atom. -/
theorem pairedEtaCompletedMomentInverseRectangle_eq_atoms
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M E D : ℕ) :
    pairedEtaCompletedMomentInverseRectangle rho k a M E D =
      ∑ n ∈ Finset.Icc 1 (E * D), (pairedEtaInverseProductCoefficient E D n : ℂ) *
        pairedEtaMomentDivisorAtom rho k a M n := by
  rw [sum_pairedEtaInverseProductCoefficient_mul]
  unfold pairedEtaCompletedMomentInverseRectangle pairedEtaCompletedMomentInversePartialTerm
    pairedEtaCompletedMomentOriginalFamily
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  exact pairedEtaMomentInverseCell_eq_atom rho k a M
    (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1

/-- The original complex rectangle square keeps every pair of outer
inverse features, with their complete inner divisor sums retained. -/
theorem pairedEtaCompletedMomentInverseRectangle_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M E D : ℕ) :
    (‖pairedEtaCompletedMomentInverseRectangle rho k a M E D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 E, ∑ e ∈ Finset.Icc 1 E,
        pairedEtaCompletedMomentInversePartialTerm rho k a M d D *
          starRingEnd ℂ (pairedEtaCompletedMomentInversePartialTerm rho k a M e D) := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaCompletedMomentInverseRectangle, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The full physical rectangle error is the signed product sum
of the original atom errors, before any norm or channel sum is taken. -/
theorem pairedEtaCompletedMomentInverseRectangle_physical_sub_parity
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M E D : ℕ) :
    (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D -
        pairedEtaMomentDivisorAmplitude rho k * pairedEtaInverseRectangleParityFamily M E D =
      ∑ n ∈ Finset.Icc 1 (E * D), (pairedEtaInverseProductCoefficient E D n : ℂ) *
        ((M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M n -
          pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / n) : ℂ)) := by
  rw [pairedEtaCompletedMomentInverseRectangle_eq_atoms]
  unfold pairedEtaInverseRectangleParityFamily pairedEtaWeightedDivisorParityFamily
  simp only [Complex.ofReal_intCast, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn <;> ring

/-- The complete inverse rectangle has a quantitative physical phase
error depending on its area squared, with every actual product divisor
and moving-center condition discharged inside that physical range. -/
theorem norm_pairedEtaCompletedMomentInverseRectangle_physical_sub_parity_le
    (rho : NontrivialZetaZero) {k M E D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hED : E * D ≤ M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D -
        pairedEtaMomentDivisorAmplitude rho k * pairedEtaInverseRectangleParityFamily M E D‖ ≤
      pairedEtaMomentDivisorAtomPhysicalConstant rho k * ((E : ℝ) * D) ^ 2 / M := by
  let C := pairedEtaMomentDivisorAtomPhysicalConstant rho k
  have hC : 0 ≤ C := pairedEtaMomentDivisorAtomPhysicalConstant_nonneg rho k
  have hnorm (n : ℕ) : ‖(pairedEtaInverseProductCoefficient E D n : ℂ)‖ =
      |(pairedEtaInverseProductCoefficient E D n : ℝ)| := by
    rw [Complex.norm_intCast]
  rw [pairedEtaCompletedMomentInverseRectangle_physical_sub_parity]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (E * D), |(pairedEtaInverseProductCoefficient E D n : ℝ)| *
        ‖(M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M n -
          pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / n) : ℂ)‖ := by
      simpa only [norm_mul, hnorm] using norm_sum_le (Finset.Icc 1 (E * D))
        (fun n ↦ (pairedEtaInverseProductCoefficient E D n : ℂ) *
          ((M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M n -
            pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / n) : ℂ)))
    _ ≤ ∑ n ∈ Finset.Icc 1 (E * D), |(pairedEtaInverseProductCoefficient E D n : ℝ)| *
        (C * ((E : ℝ) * D) / M) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hnM : n ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hED⟩
      apply (norm_pairedEtaMomentDivisorAtom_physical_sub_parity_le rho hk hnM ha).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      apply mul_le_mul_of_nonneg_left _ hC
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    _ = (∑ n ∈ Finset.Icc 1 (E * D), |(pairedEtaInverseProductCoefficient E D n : ℝ)|) *
        (C * ((E : ℝ) * D) / M) := by rw [Finset.sum_mul]
    _ ≤ ((E : ℝ) * D) * (C * ((E : ℝ) * D) / M) :=
      mul_le_mul_of_nonneg_right (sum_abs_pairedEtaInverseProductCoefficient_le E D) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Removing the common physical power keeps the exact horizontal
decay on the unmodified original inverse rectangle. -/
theorem pairedEtaCompletedMomentInverseRectangle_norm_sq_eq_physical
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M : ℕ} (hM : 1 ≤ M) (E D : ℕ) :
    ‖pairedEtaCompletedMomentInverseRectangle rho k a M E D‖ ^ 2 =
      (M : ℝ) ^ (-2 * rho.1.re) *
        ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : ‖(M : ℂ) ^ rho.1‖ = (M : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hMR rho.1
  have hs : ((M : ℝ) ^ rho.1.re) ^ 2 = (M : ℝ) ^ (rho.1.re * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMR.le]
    norm_num
  rw [norm_mul, hp, mul_pow, hs, ← mul_assoc, ← Real.rpow_add hMR,
    show -2 * rho.1.re + rho.1.re * 2 = 0 by ring, Real.rpow_zero, one_mul]

end

end RiemannGaussian
