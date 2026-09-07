import RiemannGaussian.NatDivisorSquareMean
import RiemannGaussian.EtaInverseProductCoefficients

/-!
# Signed coefficients on actual hyperbolic inverse regions

Arbitrary finite portions of the positive product region retain the
original inner Möbius signs. Exact product fibers are bounded by the
complete divisor antidiagonal, whose second moment controls interactions
across the entire curved region.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full positive divisor region with its actual product cutoff. -/
def pairedEtaInverseHyperbolicRegion (T : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 T) ×ˢ (Finset.Icc 1 T)).filter (fun p ↦ p.1 * p.2 ≤ T)

/-- Region membership retains positivity of both factors and the physical product cutoff. -/
theorem mem_pairedEtaInverseHyperbolicRegion {T : ℕ} {p : ℕ × ℕ} :
    p ∈ pairedEtaInverseHyperbolicRegion T ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ T := by
  simp only [pairedEtaInverseHyperbolicRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hd, _⟩, ⟨he, _⟩⟩, hprod⟩
    exact ⟨hd, he, hprod⟩
  · rintro ⟨hd, he, hprod⟩
    exact ⟨⟨⟨hd, (Nat.le_mul_of_pos_right p.1 he).trans hprod⟩,
      ⟨he, (Nat.le_mul_of_pos_left p.2 hd).trans hprod⟩⟩, hprod⟩

/-- The curved region discharges the original divided inner cutoff. -/
theorem pairedEtaInverseHyperbolicRegion_inner_cutoff {T M : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ pairedEtaInverseHyperbolicRegion T) (hTM : T ≤ M) : p.2 ≤ M / p.1 := by
  obtain ⟨hd, _, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hp
  apply (Nat.le_div_iff_mul_le hd).mpr
  simpa only [Nat.mul_comm] using hprod.trans hTM

/-- An outer band retains the whole curved inner range at every selected outer divisor. -/
def pairedEtaInverseHyperbolicBand (T E F : ℕ) : Finset (ℕ × ℕ) :=
  (pairedEtaInverseHyperbolicRegion T).filter (fun p ↦ E < p.1 ∧ p.1 ≤ F)

/-- Every actual outer band is contained in its original physical product region. -/
theorem pairedEtaInverseHyperbolicBand_subset (T E F : ℕ) :
    pairedEtaInverseHyperbolicBand T E F ⊆ pairedEtaInverseHyperbolicRegion T :=
  Finset.filter_subset _ _

/-- The exact signed coefficient of a product in a selected inverse region. -/
def pairedEtaInverseRegionCoefficient (S : Finset (ℕ × ℕ)) (n : ℕ) : ℤ :=
  ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n), μ p.2

/-- Product grouping preserves every original inner Möbius sign on the entire selected region. -/
theorem sum_pairedEtaInverseRegionCoefficient_mul {S : Finset (ℕ × ℕ)} {T : ℕ}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion T) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 T, (pairedEtaInverseRegionCoefficient S n : ℂ) * f n) =
      ∑ p ∈ S, (μ p.2 : ℂ) * f (p.1 * p.2) := by
  have h := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.Icc 1 T)
    (g := fun p : ℕ × ℕ ↦ p.1 * p.2) (fun p hp ↦ by
      obtain ⟨hd, he, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp (hS hp)
      exact Finset.mem_Icc.mpr ⟨by nlinarith, hprod⟩)
    (fun p : ℕ × ℕ ↦ (μ p.2 : ℂ) * f (p.1 * p.2))
  calc
    _ = ∑ n ∈ Finset.Icc 1 T, ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n),
        (μ p.2 : ℂ) * f (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairedEtaInverseRegionCoefficient, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := h

/-- The full selected product coefficient is bounded by its actual factorization count. -/
theorem abs_pairedEtaInverseRegionCoefficient_le_card (S : Finset (ℕ × ℕ)) (n : ℕ) :
    |pairedEtaInverseRegionCoefficient S n| ≤ (S.filter (fun p ↦ p.1 * p.2 = n)).card := by
  unfold pairedEtaInverseRegionCoefficient
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n), (1 : ℤ) :=
      Finset.sum_le_sum (fun p _ ↦ ArithmeticFunction.abs_moebius_le_one)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Every positive product fiber embeds in its complete divisor antidiagonal. -/
theorem abs_pairedEtaInverseRegionCoefficient_le_divisors (S : Finset (ℕ × ℕ))
    {n : ℕ} (hn : 1 ≤ n) : |pairedEtaInverseRegionCoefficient S n| ≤ n.divisors.card := by
  apply (abs_pairedEtaInverseRegionCoefficient_le_card S n).trans
  have h : S.filter (fun p ↦ p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
    intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2, by omega⟩
  have hc := Finset.card_le_card h
  rw [← Nat.map_div_right_divisors, Finset.card_map] at hc
  exact_mod_cast hc

/-- All selected product coefficients have cubic logarithmic energy,
including every interaction between separate parts of the curved region. -/
theorem sum_sq_pairedEtaInverseRegionCoefficient_le_log_cube (S : Finset (ℕ × ℕ)) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (pairedEtaInverseRegionCoefficient S n : ℝ) ^ 2) ≤
      (T : ℝ) * (1 + Real.log T) ^ 3 := by
  apply le_trans _ (sum_Icc_card_divisors_sq_le_log_cube T)
  apply Finset.sum_le_sum
  intro n hn
  have h : |(pairedEtaInverseRegionCoefficient S n : ℝ)| ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast abs_pairedEtaInverseRegionCoefficient_le_divisors S (Finset.mem_Icc.mp hn).1
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr h

end

end RiemannGaussian
