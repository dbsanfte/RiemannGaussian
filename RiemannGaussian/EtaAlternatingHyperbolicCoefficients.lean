import RiemannGaussian.EtaMoebiusQuotientBilinear

/-!
# Alternating Möbius product coefficients on the actual hyperbola

The Abel-transformed quotient carrier uses the original Möbius product
fibres with the literal eta sign on the other factor. Their exact signed
coefficients connect to the existing odd and even inverse regions. The
factorization-count bound controls coefficient energy only; it is not a
bound for the full physical-window quadratic form.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Every product fibre retains the eta sign of the quotient and the Möbius sign of the divisor. -/
def pairedEtaAlternatingRegionCoefficient (S : Finset (ℕ × ℕ)) (n : ℕ) : ℤ :=
  ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n), pairedEtaDirichletSign p.1 * μ p.2

/-- The alternating product coefficient is exactly the difference of the existing odd and even quotient-region coefficients. -/
theorem pairedEtaAlternatingRegionCoefficient_eq_odd_sub_even
    (S : Finset (ℕ × ℕ)) (n : ℕ) :
    pairedEtaAlternatingRegionCoefficient S n =
      pairedEtaInverseRegionCoefficient (S.filter (fun p ↦ Odd p.1)) n -
        pairedEtaInverseRegionCoefficient (S.filter (fun p ↦ Even p.1)) n := by
  simp only [pairedEtaAlternatingRegionCoefficient, pairedEtaInverseRegionCoefficient,
    Finset.sum_filter, ← Finset.sum_sub_distrib, pairedEtaDirichletSign]
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : Even p.1
  · have ho : ¬Odd p.1 := by simpa only [Nat.not_odd_iff_even] using he
    by_cases hn : p.1 * p.2 = n <;> simp [he, ho, hn]
  · have ho : Odd p.1 := Nat.not_even_iff_odd.mp he
    simp [he, ho]

/-- Grouping a selected hyperbolic region by its products preserves both original arithmetic signs and the entire complex product phase. -/
theorem sum_pairedEtaAlternatingRegionCoefficient_mul {S : Finset (ℕ × ℕ)} {M : ℕ}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion M) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 M, (pairedEtaAlternatingRegionCoefficient S n : ℂ) * f n) =
      ∑ p ∈ S, (pairedEtaDirichletSign p.1 : ℂ) * (μ p.2 : ℂ) * f (p.1 * p.2) := by
  have hs := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.Icc 1 M)
    (g := fun p : ℕ × ℕ ↦ p.1 * p.2) (fun p hp ↦ by
      obtain ⟨hq, hd, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp (hS hp)
      exact Finset.mem_Icc.mpr ⟨by nlinarith, hprod⟩)
    (fun p : ℕ × ℕ ↦ (pairedEtaDirichletSign p.1 : ℂ) * (μ p.2 : ℂ) * f (p.1 * p.2))
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n),
        (pairedEtaDirichletSign p.1 : ℂ) * (μ p.2 : ℂ) * f (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [pairedEtaAlternatingRegionCoefficient, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Int.cast_mul, (Finset.mem_filter.mp hp).2]
    _ = _ := hs

/-- Every alternating coefficient is bounded by the complete factorization count, without splitting its odd and even square energies. -/
theorem abs_pairedEtaAlternatingRegionCoefficient_le_divisors (S : Finset (ℕ × ℕ))
    {n : ℕ} (hn : 1 ≤ n) : |pairedEtaAlternatingRegionCoefficient S n| ≤ n.divisors.card := by
  have hs : S.filter (fun p ↦ p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
    intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2, by omega⟩
  have hc := Finset.card_le_card hs
  rw [← Nat.map_div_right_divisors, Finset.card_map] at hc
  calc
    _ ≤ ∑ p ∈ S.filter (fun p ↦ p.1 * p.2 = n), |pairedEtaDirichletSign p.1 * μ p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S.filter (fun p ↦ p.1 * p.2 = n), (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_pairedEtaDirichletSign, one_mul]
      exact ArithmeticFunction.abs_moebius_le_one
    _ = ((S.filter (fun p ↦ p.1 * p.2 = n)).card : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast hc

/-- The complete second-moment collision bound applies to the actual alternating coefficients with the same cubic logarithmic cost. This is coefficient energy, with no physical sampling claim. -/
theorem sum_sq_pairedEtaAlternatingRegionCoefficient_le_log_cube (S : Finset (ℕ × ℕ)) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (pairedEtaAlternatingRegionCoefficient S n : ℝ) ^ 2) ≤
      (M : ℝ) * (1 + Real.log M) ^ 3 := by
  apply le_trans _ (sum_Icc_card_divisors_sq_le_log_cube M)
  apply Finset.sum_le_sum
  intro n hn
  have h : |(pairedEtaAlternatingRegionCoefficient S n : ℝ)| ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast abs_pairedEtaAlternatingRegionCoefficient_le_divisors S (Finset.mem_Icc.mp hn).1
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr h

/-- The alternating high-divisor coefficient depends only on the fixed divisor cutoff and the product, not on the later physical endpoint. -/
def pairedEtaMoebiusHighProductCoefficient (D n : ℕ) : ℤ :=
  ∑ p ∈ n.divisorsAntidiagonal.filter (fun p ↦ D < p.2), pairedEtaDirichletSign p.1 * μ p.2

/-- Each actual region fibre equals the fixed-cutoff divisor coefficient on every product in its physical range. -/
theorem pairedEtaAlternatingRegionCoefficient_divisor_cut
    (M D : ℕ) {n : ℕ} (hn : n ∈ Finset.Icc 1 M) :
    pairedEtaAlternatingRegionCoefficient
      ((pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ D < p.2)) n =
      pairedEtaMoebiusHighProductCoefficient D n := by
  have he : ((pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ D < p.2)).filter
      (fun p ↦ p.1 * p.2 = n) = n.divisorsAntidiagonal.filter (fun p ↦ D < p.2) := by
    ext p
    simp only [Finset.mem_filter, mem_pairedEtaInverseHyperbolicRegion, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨⟨⟨hq, hd, _⟩, hD⟩, hprod⟩
      exact ⟨⟨hprod, by nlinarith⟩, hD⟩
    · rintro ⟨⟨hprod, hn0⟩, hD⟩
      have hprodpos : 0 < p.1 * p.2 := by rw [hprod]; exact (Finset.mem_Icc.mp hn).1
      have hp := Nat.pos_of_mul_pos_right hprodpos
      have hd := Nat.pos_of_mul_pos_left hprodpos
      exact ⟨⟨⟨hp, hd, hprod ▸ (Finset.mem_Icc.mp hn).2⟩, hD⟩, hprod⟩
  exact congrArg (fun S : Finset (ℕ × ℕ) ↦ ∑ p ∈ S, pairedEtaDirichletSign p.1 * μ p.2) he

/-- All products below the fixed Möbius divisor cutoff vanish exactly. -/
theorem pairedEtaMoebiusHighProductCoefficient_eq_zero {D n : ℕ} (hn : n ≤ D) :
    pairedEtaMoebiusHighProductCoefficient D n = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp, hD⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hq : 0 < p.1 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).1
  have hd : p.2 ≤ n := by rw [← hprod]; exact Nat.le_mul_of_pos_left _ hq
  omega

/-- The first product band is exactly the original Möbius sequence: its only admissible quotient is one. This band remains part of the full bilinear form. -/
theorem pairedEtaMoebiusHighProductCoefficient_eq_moebius
    {D n : ℕ} (hDn : D < n) (hnD : n ≤ 2 * D) :
    pairedEtaMoebiusHighProductCoefficient D n = μ n := by
  have he : n.divisorsAntidiagonal.filter (fun p ↦ D < p.2) = {(1, n)} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hprod, hn0⟩, hD⟩
      have hq : 0 < p.1 := Nat.pos_of_ne_zero (fun hz ↦ hn0 (by rw [← hprod, hz, zero_mul]))
      have hp : p.1 = 1 := by nlinarith
      apply Prod.ext hp
      simpa only [hp, one_mul] using hprod
    · rintro rfl
      exact ⟨⟨by simp, by omega⟩, hDn⟩
  rw [pairedEtaMoebiusHighProductCoefficient, he, Finset.sum_singleton]
  norm_num [pairedEtaDirichletSign]

/-- The fixed-cutoff alternating coefficients inherit the complete hyperbolic collision-energy bound. -/
theorem sum_sq_pairedEtaMoebiusHighProductCoefficient_le_log_cube (D M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2) ≤
      (M : ℝ) * (1 + Real.log M) ^ 3 := by
  convert sum_sq_pairedEtaAlternatingRegionCoefficient_le_log_cube
    ((pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ D < p.2)) M using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [pairedEtaAlternatingRegionCoefficient_divisor_cut M D hn]

/-- The original bilinear Abel carrier is a partial Dirichlet sum of fixed-cutoff alternating product coefficients, with the actual reciprocal boundary as cutoff. -/
theorem pairedEtaMoebiusQuotientBilinearSum_eq_product_prefix
    (rho : NontrivialZetaZero) (M Q : ℕ) :
    pairedEtaMoebiusQuotientBilinearSum rho M Q =
      ∑ n ∈ Finset.Icc 1 M, (pairedEtaMoebiusHighProductCoefficient (M / (Q + 1)) n : ℂ) *
        (n : ℂ) ^ (-rho.1) := by
  rw [pairedEtaMoebiusQuotientBilinearSum,
    ← sum_pairedEtaAlternatingRegionCoefficient_mul (pairedEtaMoebiusQuotientBilinearRegion_subset M Q)
      (fun n : ℕ ↦ (n : ℂ) ^ (-rho.1)),
    pairedEtaMoebiusQuotientBilinearRegion_eq_divisor_cut]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pairedEtaAlternatingRegionCoefficient_divisor_cut M (M / (Q + 1)) hn]

end

end RiemannGaussian
