import RiemannGaussian.EtaInverseCoherentBand

/-!
# Exact coefficient and parity energies of the coherent inverse band

These are the actual signed product coefficients from the original
inverse region. Their energy is the number of selected divisors, while
their whole parity sum is that same number throughout the physical
window. The excess short-window energy is therefore present before
any analytic approximation or physical normalization.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual product divisors of the original coherent inverse band. -/
def pairedEtaCoherentDivisors (B K : ℕ) : Finset ℕ :=
  (Finset.range K).image (fun j ↦ B * K + 2 * j + 1)

/-- Every selected product is positive and lies inside the physical cutoff. -/
theorem pairedEtaCoherentDivisors_subset (B K : ℕ) :
    pairedEtaCoherentDivisors B K ⊆ Finset.Icc 1 ((B + 2) * K) := by
  intro n hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
  have hjK := Finset.mem_range.mp hj
  apply Finset.mem_Icc.mpr
  simp only [Nat.add_mul]
  omega

/-- No original midpoint divisor is repeated. -/
theorem card_pairedEtaCoherentDivisors (B K : ℕ) : (pairedEtaCoherentDivisors B K).card = K := by
  unfold pairedEtaCoherentDivisors
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro i hi j hj hij
  change B * K + 2 * i + 1 = B * K + 2 * j + 1 at hij
  omega

/-- At the scale chosen from the actual zero, every original outer divisor belongs to the odd channel. -/
theorem odd_mem_pairedEtaCoherentDivisors (rho : NontrivialZetaZero) {K d : ℕ}
    (hd : d ∈ pairedEtaCoherentDivisors (pairedEtaInverseCoherenceScale rho) K) : Odd d := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  rw [pairedEtaInverseCoherenceScale, Nat.mul_assoc]
  exact ⟨2 * ((1 + ⌈‖rho.1‖⌉₊) * K) + j, by omega⟩

/-- Each selected product has exactly its original inner Möbius coefficient one; all others have coefficient zero. -/
theorem pairedEtaInverseRegionCoefficient_coherentBand (B K n : ℕ) :
    pairedEtaInverseRegionCoefficient (pairedEtaInverseCoherentBand B K) n =
      if n ∈ pairedEtaCoherentDivisors B K then 1 else 0 := by
  by_cases hn : n ∈ pairedEtaCoherentDivisors B K
  · have hf : (pairedEtaInverseCoherentBand B K).filter (fun p ↦ p.1 * p.2 = n) = {(n, 1)} := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpS, hprod⟩ := Finset.mem_filter.mp hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hpS
        apply Finset.mem_singleton.mpr
        exact Prod.ext (by simpa only [mul_one] using hprod) rfl
      · intro hp
        have he := Finset.mem_singleton.mp hp
        subst p
        obtain ⟨j, hj, hjn⟩ := Finset.mem_image.mp hn
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨j, hj, Prod.ext hjn rfl⟩, by simp⟩
    rw [pairedEtaInverseRegionCoefficient, hf, if_pos hn]
    norm_num
  · have hf : (pairedEtaInverseCoherentBand B K).filter (fun p ↦ p.1 * p.2 = n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp heq
      apply hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨j, hj, by simpa only [mul_one] using heq⟩
    rw [pairedEtaInverseRegionCoefficient, hf, Finset.sum_empty, if_neg hn]

/-- The literal signed product coefficients have energy exactly the number of coherent inverse divisors. -/
theorem sum_sq_pairedEtaInverseRegionCoefficient_coherentBand (B K : ℕ) :
    (∑ n ∈ Finset.Icc 1 ((B + 2) * K),
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseCoherentBand B K) n : ℝ) ^ 2) = K := by
  simp_rw [pairedEtaInverseRegionCoefficient_coherentBand, Int.cast_ite, Int.cast_one, Int.cast_zero,
    ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  have hf : (Finset.Icc 1 ((B + 2) * K)).filter
      (fun n ↦ n ∈ pairedEtaCoherentDivisors B K) = pairedEtaCoherentDivisors B K := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨pairedEtaCoherentDivisors_subset B K h, h⟩⟩
  rw [hf]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_pairedEtaCoherentDivisors]

/-- The original signed parity family is exactly coherent throughout the full physical window. -/
theorem pairedEtaWeightedDivisorParityFamily_coherentBand_eq
    {B K r : ℕ} (hB : 4 ≤ B) (hr : r < K) :
    pairedEtaWeightedDivisorParityFamily
      (fun n ↦ pairedEtaInverseRegionCoefficient (pairedEtaInverseCoherentBand B K) n)
      ((B + 2) * K + r) ((B + 2) * K) = (K : ℂ) := by
  unfold pairedEtaWeightedDivisorParityFamily
  simp only [Complex.ofReal_intCast]
  rw [sum_pairedEtaInverseRegionCoefficient_mul (pairedEtaInverseCoherentBand_subset B K)]
  unfold pairedEtaInverseCoherentBand
  rw [Finset.sum_image]
  · calc
      _ = ∑ _j ∈ Finset.range K, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [mul_one]
        rw [div_eq_one_on_pairedEtaInverseCoherentBand hB hr (Finset.mem_range.mp hj)]
        norm_num [pairedEtaDirichletSign]
      _ = _ := by simp
  · intro i hi j hj hij
    have h := congrArg Prod.fst hij
    change B * K + 2 * i + 1 = B * K + 2 * j + 1 at h
    omega

end

end RiemannGaussian
