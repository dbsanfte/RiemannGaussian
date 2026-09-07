import RiemannGaussian.EtaMoebiusBilinearWindow
import RiemannGaussian.NatDivisorSquareDirichlet

/-!
# A uniform power bound for the actual bilinear product diagonal

The fixed alternating coefficients vanish through the divisor cutoff.
The full divisor-square Dirichlet mass therefore bounds their weighted
product diagonal uniformly over all physical windows. The exact split
keeps every off-diagonal product interaction as a signed complex sum.
The diagonal estimate is not a bound on that surviving sum.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The actual fixed high-divisor coefficient has the full divisor-count bound at every positive product. -/
theorem abs_pairedEtaMoebiusHighProductCoefficient_le_divisors (D : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    |pairedEtaMoebiusHighProductCoefficient D n| ≤ n.divisors.card := by
  rw [← pairedEtaAlternatingRegionCoefficient_divisor_cut n D (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)]
  exact abs_pairedEtaAlternatingRegionCoefficient_le_divisors _ hn

/-- The whole finite weighted coefficient energy has a power tail bound independent of its upper endpoint. -/
theorem sum_sq_pairedEtaMoebiusHighProductCoefficient_mul_rpow_neg_le
    {p s : ℝ} (hp : 1 < p) (hps : p ≤ s) {D : ℕ} (hD : 1 ≤ D) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 *
      (n : ℝ) ^ (-s)) ≤ divisorSquareDirichletMass p * (D : ℝ) ^ (p - s) := by
  have he : (Finset.Icc 1 M).filter (fun n ↦ D < n) = Finset.Ioc D M := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ = ∑ n ∈ Finset.Ioc D M, (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 *
        (n : ℝ) ^ (-s) := by
      rw [← he, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : D < n
      · rw [if_pos hn]
      · rw [if_neg hn, pairedEtaMoebiusHighProductCoefficient_eq_zero (by omega)]
        simp
    _ ≤ ∑ n ∈ Finset.Ioc D M, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s) := by
      apply Finset.sum_le_sum
      intro n hn
      have ha : |(pairedEtaMoebiusHighProductCoefficient D n : ℝ)| ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast abs_pairedEtaMoebiusHighProductCoefficient_le_divisors D
          (by have := (Finset.mem_Ioc.mp hn).1; omega : 1 ≤ n)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr ha
    _ ≤ _ := sum_Ioc_card_divisors_sq_mul_rpow_neg_le hp hps hD M

/-- The product diagonal of the actual completed high-divisor window matrix, with its exact overlap weights. -/
def pairedEtaCompletedMoebiusBilinearDiagonal (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
    ∑ n ∈ Finset.Icc 1 (A + L), pairedEtaBilinearPrefixWindowKernel A L n n *
      (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * rho.1.re))

/-- The diagonal of the actual physical-window matrix is nonnegative. -/
theorem pairedEtaCompletedMoebiusBilinearDiagonal_nonneg
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusBilinearDiagonal rho A L D := by
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (pairedEtaBilinearPrefixWindowKernel_bounds A L n n).1
    (sq_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Every actual physical window satisfies the same power bound for its entire product diagonal, without assuming cancellation or orthogonality of distinct products. -/
theorem pairedEtaCompletedMoebiusBilinearDiagonal_le_power
    (rho : NontrivialZetaZero) {p : ℝ} (hp : 1 < p) (hpr : p ≤ 2 * rho.1.re)
    {D : ℕ} (hD : 1 ≤ D) (A L : ℕ) :
    pairedEtaCompletedMoebiusBilinearDiagonal rho A L D ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass p *
        (D : ℝ) ^ (p - 2 * rho.1.re) := by
  rw [pairedEtaCompletedMoebiusBilinearDiagonal, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply le_trans _ (sum_sq_pairedEtaMoebiusHighProductCoefficient_mul_rpow_neg_le hp hpr hD (A + L))
  apply Finset.sum_le_sum
  intro n _
  have hK := (pairedEtaBilinearPrefixWindowKernel_bounds A L n n).2
  have hsq := sq_nonneg (pairedEtaMoebiusHighProductCoefficient D n : ℝ)
  have hrpow := Real.rpow_nonneg (Nat.cast_nonneg n) (-(2 * rho.1.re))
  nlinarith [mul_nonneg hsq hrpow, mul_le_mul_of_nonneg_right hK (mul_nonneg hsq hrpow)]

/-- Every ordered pair of distinct products remains in this complex off-diagonal sum, with its exact physical overlap and original Mellin phase. -/
def pairedEtaMoebiusBilinearOffDiagonal (rho : NontrivialZetaZero) (A L D : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ (Finset.Icc 1 (A + L)).erase n,
    (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
      (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
      (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))

private theorem product_pair_diagonal (rho : NontrivialZetaZero) (A L D : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    (pairedEtaBilinearPrefixWindowKernel A L n n : ℂ) *
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
      (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((n : ℂ) ^ (-rho.1)) =
        ((pairedEtaBilinearPrefixWindowKernel A L n n *
          (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 *
          (n : ℝ) ^ (-(2 * rho.1.re)) : ℝ) : ℂ) := by
  have he : (n : ℝ) ^ (-(2 * rho.1.re)) = ((n : ℝ) ^ (-rho.1.re)) ^ 2 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    norm_num
    ring
  rw [he]
  have hz := Complex.mul_conj' ((n : ℂ) ^ (-rho.1))
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re] at hz
  push_cast
  calc
    _ = (pairedEtaBilinearPrefixWindowKernel A L n n : ℂ) *
        (pairedEtaMoebiusHighProductCoefficient D n : ℂ) ^ 2 *
        ((n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((n : ℂ) ^ (-rho.1))) := by ring
    _ = _ := by rw [hz]

/-- The full actual bilinear energy is exactly its nonnegative product diagonal plus the signed complex sum of every distinct-product interaction. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_diagonal_add_offDiagonal
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho A L D : ℂ) =
      (pairedEtaCompletedMoebiusBilinearDiagonal rho A L D : ℂ) +
        (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
          pairedEtaMoebiusBilinearOffDiagonal rho A L D := by
  rw [pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_window]
  have he : (∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ Finset.Icc 1 (A + L),
      (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
        (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
        (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
        (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))) =
      (∑ n ∈ Finset.Icc 1 (A + L), ((pairedEtaBilinearPrefixWindowKernel A L n n *
        (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 *
        (n : ℝ) ^ (-(2 * rho.1.re)) : ℝ) : ℂ)) +
        pairedEtaMoebiusBilinearOffDiagonal rho A L D := by
    rw [pairedEtaMoebiusBilinearOffDiagonal, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← product_pair_diagonal rho A L D (Finset.mem_Icc.mp hn).1]
    exact (Finset.add_sum_erase _ _ hn).symm
  rw [he, mul_add, pairedEtaCompletedMoebiusBilinearDiagonal]
  push_cast
  rfl

/-- On the original squared divisor cutoff the entire product diagonal has a uniform negative power whenever the zero lies strictly to the right of one half. -/
theorem pairedEtaCompletedMoebiusBilinearDiagonal_twoThirds_le
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {u : ℕ} (hu : 1 ≤ u) (A L : ℕ) :
    pairedEtaCompletedMoebiusBilinearDiagonal rho A L (u ^ 2) ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
        (u : ℝ) ^ (1 - 2 * rho.1.re) := by
  have hp : 1 < rho.1.re + 1 / 2 := by linarith
  have hpr : rho.1.re + 1 / 2 ≤ 2 * rho.1.re := by linarith
  have h := pairedEtaCompletedMoebiusBilinearDiagonal_le_power rho hp hpr
    (by nlinarith : 1 ≤ u ^ 2) A L
  have he : ((u ^ 2 : ℕ) : ℝ) ^ (rho.1.re + 1 / 2 - 2 * rho.1.re) =
      (u : ℝ) ^ (1 - 2 * rho.1.re) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg u)]
    congr 1
    norm_num
    ring
  rwa [he] at h

/-- The actual bilinear product diagonal tends to zero on any sequence of physical windows, with the original squared divisor cutoff. -/
theorem pairedEtaCompletedMoebiusBilinearDiagonal_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) (A L : ℕ → ℕ) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusBilinearDiagonal rho (A u) (L u) (u ^ 2))
      atTop (𝓝 0) := by
  have hd : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (1 - 2 * rho.1.re)) atTop (𝓝 0) := by
    have hreal := tendsto_rpow_neg_atTop (by linarith : 0 < 2 * rho.1.re - 1)
    convert hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  have hb := hd.const_mul (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
    divisorSquareDirichletMass (rho.1.re + 1 / 2))
  rw [mul_zero] at hb
  exact squeeze_zero' (Eventually.of_forall (fun u ↦
    pairedEtaCompletedMoebiusBilinearDiagonal_nonneg rho (A u) (L u) (u ^ 2)))
    ((eventually_ge_atTop 1).mono fun u hu ↦
      pairedEtaCompletedMoebiusBilinearDiagonal_twoThirds_le rho hrho hu (A u) (L u)) hb

/-- After the independently bounded product diagonal vanishes, the full signed distinct-product correlation retains the source square on the actual cubic windows. No upper bound for this remaining correlation is inferred. -/
theorem pairedEtaMoebiusBilinearOffDiagonal_twoThirds_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
      (pairedEtaMoebiusBilinearOffDiagonal rho (u ^ 3) (u ^ 3) (u ^ 2)).re)
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hh := pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho
  have hd := pairedEtaCompletedMoebiusBilinearDiagonal_tendsto_zero rho hrho (fun u ↦ u ^ 3) (fun u ↦ u ^ 3)
  have he (u : ℕ) : ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
      (pairedEtaMoebiusBilinearOffDiagonal rho (u ^ 3) (u ^ 3) (u ^ 2)).re =
        pairedEtaCompletedMoebiusLargeMeanSquare rho (u ^ 3) (u ^ 3) (u ^ 2) -
          pairedEtaCompletedMoebiusBilinearDiagonal rho (u ^ 3) (u ^ 3) (u ^ 2) := by
    have h := congrArg Complex.re
      (pairedEtaCompletedMoebiusLargeMeanSquare_eq_diagonal_add_offDiagonal rho (u ^ 3) (u ^ 3) (u ^ 2))
    simp only [Complex.add_re, Complex.ofReal_re, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul] at h
    linarith
  simpa only [he, sub_zero] using hh.sub hd

end

end RiemannGaussian
