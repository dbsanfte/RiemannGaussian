import RiemannGaussian.EtaMoebiusArithmeticSums

/-!
# Exact divisor arithmetic on every original logarithmic cell

The continuum carrier is evaluated on each original open-left, closed-right
integer-log cell. Its normalized value is a finite signed divisor sum with
the original arithmetic cutoff and complete harmonic correction. Cells
beyond the arithmetic cutoff remain part of the same identity.
-/

open Complex Set
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The complete normalized arithmetic value on the cell from `log L` to `log (L+1)`, with the original truncated divisor sum and harmonic correction. -/
def pairedEtaMoebiusArithmeticCellValue (M : ℕ) (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (∑ l ∈ Finset.Icc 1 L, pairedEtaMoebiusArithmeticDivisor M w l / l) -
    pairedEtaMoebiusArithmeticHarmonic M w * pairedEtaArithmeticHarmonicPrefix L

/-- The exact normalized target residual on an original arithmetic cell, before taking its square. -/
def pairedEtaMoebiusArithmeticCellResidual (M : ℕ) (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (if L = 1 then 1 else 0) - pairedEtaMoebiusArithmeticCellValue M w L

private theorem nat_lt_on_cell {L : ℕ} {x : ℝ} (hlo : (L : ℝ) < x)
    (hhi : x ≤ (L : ℝ) + 1) (n : ℕ) : (n : ℝ) < x ↔ n ≤ L := by
  constructor
  · intro hn
    by_contra! h
    have hh : (L : ℝ) + 1 ≤ n := by exact_mod_cast (show L + 1 ≤ n by omega)
    linarith
  · intro hn
    exact (show (n : ℝ) ≤ L by exact_mod_cast hn).trans_lt hlo

private theorem primitive_div_on_cell (M : ℕ) (w : ℕ → ℝ) {L m : ℕ}
    (hm : m ∈ Finset.Icc 1 L) {x : ℝ} (hlo : (L : ℝ) < x) (hhi : x ≤ (L : ℝ) + 1) :
    pairedEtaMoebiusContinuumPrimitive M w (x / m) = x / m *
      ((∑ n ∈ Finset.Icc 1 M, if n * m ≤ L then (μ n : ℝ) * w n / n else 0) -
        pairedEtaMoebiusArithmeticHarmonic M w) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hx : 1 < x / m := (lt_div_iff₀ hmp).mpr (by
    have hh : (m : ℝ) ≤ L := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    linarith)
  have htest (n : ℕ) : (n : ℝ) < x / m ↔ n * m ≤ L := by
    rw [lt_div_iff₀ hmp]
    simpa only [Nat.cast_mul] using nat_lt_on_cell hlo hhi (n * m)
  unfold pairedEtaMoebiusContinuumPrimitive pairedEtaMoebiusArithmeticHarmonic
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold pairedEtaMoebiusContinuumAtom
  rw [if_pos hx]
  simp only [htest]
  split_ifs <;> ring

/-- On every original positive arithmetic cell the full continuum combination is exactly its complete signed harmonic prefix of primitive values. -/
theorem pairedEtaMoebiusContinuumCombination_eq_signed_cell_prefix (M : ℕ) (w : ℕ → ℝ)
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht : t ∈ Ioc (Real.log L) (Real.log (L + 1 : ℝ))) :
    pairedEtaMoebiusContinuumCombination M w t =
      ((∑ m ∈ Finset.Icc 1 L, (pairedEtaDirichletSign m : ℝ) *
        pairedEtaMoebiusContinuumPrimitive M w (Real.exp t / m)) : ℝ) := by
  have htN : t ≤ Real.log (2 * L + 1 : ℝ) := ht.2.trans
    (Real.log_le_log (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) L]))
  have hprefix : pairedEtaMoebiusContinuumCombination M w t =
      ((∑ m ∈ Finset.Icc 1 (2 * L), (pairedEtaDirichletSign m : ℝ) *
        pairedEtaMoebiusContinuumPrimitive M w (Real.exp t / m)) : ℝ) := by
    rw [pairedEtaMoebiusContinuumCombination_eq_prefix L M w htN]
    congr 1
    rw [sum_pairedEtaDirichletSign_mul_eq_pairs]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    simp_rw [Real.exp_sub]
    rw [Real.exp_log (by positivity : 0 < (2 * n + 1 : ℝ)),
      Real.exp_log (by positivity : 0 < (2 * n + 2 : ℝ))]
  rw [hprefix]
  congr 1
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
  intro m hm hnot
  have hmp : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hLm : L + 1 ≤ m := by
    by_contra! h
    exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, by omega⟩)
  have hx : Real.exp t ≤ (L : ℝ) + 1 :=
    (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by positivity))
  have hxm : Real.exp t / m ≤ 1 := (div_le_one hmp).mpr
    (hx.trans (by exact_mod_cast hLm))
  rw [pairedEtaMoebiusContinuumPrimitive_eq_zero_of_le_one M w hxm, mul_zero]

/-- The complete signed continuum combination has its exact divisor-cell value on every positive cell, including all cells beyond the original arithmetic cutoff. -/
theorem pairedEtaMoebiusContinuumCombination_eq_arithmetic_cell (M : ℕ) (w : ℕ → ℝ)
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht : t ∈ Ioc (Real.log L) (Real.log (L + 1 : ℝ))) :
    pairedEtaMoebiusContinuumCombination M w t =
      (Real.exp t * pairedEtaMoebiusArithmeticCellValue M w L : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hlo : (L : ℝ) < Real.exp t := (Real.log_lt_iff_lt_exp hLp).mp ht.1
  have hhi : Real.exp t ≤ (L : ℝ) + 1 :=
    (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by positivity))
  rw [pairedEtaMoebiusContinuumCombination_eq_signed_cell_prefix M w hL ht]
  congr 1
  calc
    _ = ∑ m ∈ Finset.Icc 1 L, Real.exp t * ((pairedEtaDirichletSign m : ℝ) / m *
        ((∑ n ∈ Finset.Icc 1 M, if n * m ≤ L then (μ n : ℝ) * w n / n else 0) -
          pairedEtaMoebiusArithmeticHarmonic M w)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [primitive_div_on_cell M w hm hlo hhi]
      ring
    _ = Real.exp t * (∑ m ∈ Finset.Icc 1 L, (pairedEtaDirichletSign m : ℝ) / m *
        ((∑ n ∈ Finset.Icc 1 M, if n * m ≤ L then (μ n : ℝ) * w n / n else 0) -
          pairedEtaMoebiusArithmeticHarmonic M w)) := by rw [Finset.mul_sum]
    _ = _ := by
      unfold pairedEtaMoebiusArithmeticCellValue pairedEtaArithmeticHarmonicPrefix
      rw [sum_pairedEtaMoebiusArithmeticDivisor_div_eq_rectangle]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring

/-- The actual complete continuum target residual equals its signed divisor-cell coefficient times the physical coordinate, with the original target and all endpoint conventions preserved. -/
theorem pairedEtaMoebiusContinuumResidual_eq_arithmetic_cell (M : ℕ) (w : ℕ → ℝ)
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht : t ∈ Ioc (Real.log L) (Real.log (L + 1 : ℝ))) :
    pairedEtaProjectionHead t - pairedEtaMoebiusContinuumCombination M w t =
      (Real.exp t * pairedEtaMoebiusArithmeticCellResidual M w L : ℝ) := by
  have hhead : pairedEtaProjectionHead t = (Real.exp t * (if L = 1 then 1 else 0) : ℝ) := by
    by_cases hL1 : L = 1
    · subst L
      have hh : t ∈ Ioc 0 (Real.log 2) := by
        simpa only [Nat.cast_one, Real.log_one, one_add_one_eq_two] using ht
      simp [pairedEtaProjectionHead, hh]
    · have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      have hh : Real.log 2 < t := (Real.log_le_log (by norm_num) hL2).trans_lt ht.1
      have hnot : t ∉ Ioc 0 (Real.log 2) := fun h ↦ (not_le_of_gt hh) h.2
      simp [pairedEtaProjectionHead, hnot, hL1]
  rw [hhead, pairedEtaMoebiusContinuumCombination_eq_arithmetic_cell M w hL ht,
    pairedEtaMoebiusArithmeticCellResidual]
  push_cast
  ring

end

end RiemannGaussian
