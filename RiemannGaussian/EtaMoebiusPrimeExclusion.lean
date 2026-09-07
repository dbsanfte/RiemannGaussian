import RiemannGaussian.EtaMoebiusPrimeProductDecay

/-!
# Removing all prime-divisible product rows with their cross terms

The exact complementary product prefix excludes multiples of one fixed
odd prime. Its energy keeps every remaining pair. The vanishing energy
of the removed family also controls its full mixed correlation with the
original high aggregate, so deleting these dense rows and columns has
vanishing cost on the original cubic windows. The complementary energy
still carries the source; its independent upper bound remains open.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The unchanged completed high product prefix on products not divisible by the selected prime. -/
def pairedEtaCompletedMoebiusPrimeFreeAggregate (rho : NontrivialZetaZero) (p D M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ ¬p ∣ n),
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)

/-- The original high aggregate splits into the full prime-divisible family and its literal complement, before taking norms or discarding mixed terms. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_prime_add_free
    (rho : NontrivialZetaZero) (p D M : ℕ) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M +
        pairedEtaCompletedMoebiusPrimeFreeAggregate rho p D M := by
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix, pairedEtaCompletedMoebiusPrimeProductAggregate,
    pairedEtaCompletedMoebiusPrimeFreeAggregate, ← mul_add,
    Finset.sum_filter_add_sum_filter_not]

/-- The original completed high family paired with its entire prime-divisible part, retaining its complex orientation and the literal cubic averaging window. -/
def pairedEtaMoebiusPrimeMixedCubicCorrelation (rho : NontrivialZetaZero) (p v : ℕ) : ℂ :=
  (∑ t ∈ Finset.range ((p * v) ^ 3),
    pairedEtaCompletedMoebiusLargeAggregate rho ((p * v) ^ 3 + t) ((p * v) ^ 2) *
      starRingEnd ℂ (pairedEtaCompletedMoebiusPrimeProductAggregate rho p ((p * v) ^ 2) ((p * v) ^ 3 + t))) /
        ((p * v) ^ 3 : ℕ)

/-- The whole mean square on products not divisible by the selected prime, with all surviving product cross terms and the original cutoff schedule. -/
def pairedEtaMoebiusPrimeFreeCubicEnergy (rho : NontrivialZetaZero) (p v : ℕ) : ℝ :=
  (∑ t ∈ Finset.range ((p * v) ^ 3),
    ‖pairedEtaCompletedMoebiusPrimeFreeAggregate rho p ((p * v) ^ 2) ((p * v) ^ 3 + t)‖ ^ 2) /
      ((p * v) ^ 3 : ℕ)

/-- Removing the prime-divisible products retains their entire signed interference with the original full family, including every row-to-complement interaction. -/
theorem pairedEtaMoebiusPrimeFreeCubicEnergy_eq_mixed
    (rho : NontrivialZetaZero) (p v : ℕ) :
    pairedEtaMoebiusPrimeFreeCubicEnergy rho p v =
      pairedEtaCompletedMoebiusLargeMeanSquare rho ((p * v) ^ 3) ((p * v) ^ 3) ((p * v) ^ 2) +
        pairedEtaMoebiusPrimeProductCubicEnergy rho p v -
          2 * (pairedEtaMoebiusPrimeMixedCubicCorrelation rho p v).re := by
  have hpoint (M D : ℕ) :
      ‖pairedEtaCompletedMoebiusPrimeFreeAggregate rho p D M‖ ^ 2 =
        ‖pairedEtaCompletedMoebiusLargeAggregate rho M D‖ ^ 2 +
          ‖pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M‖ ^ 2 -
            2 * (pairedEtaCompletedMoebiusLargeAggregate rho M D *
              starRingEnd ℂ (pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M)).re := by
    have he : pairedEtaCompletedMoebiusPrimeFreeAggregate rho p D M =
        pairedEtaCompletedMoebiusLargeAggregate rho M D -
          pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M := by
      rw [pairedEtaCompletedMoebiusLargeAggregate_eq_prime_add_free rho p D M]
      ring
    rw [he, Complex.sq_norm, Complex.normSq_sub]
    simp only [← Complex.sq_norm]
  simp only [pairedEtaMoebiusPrimeFreeCubicEnergy, hpoint,
    pairedEtaCompletedMoebiusLargeMeanSquare, pairedEtaMoebiusPrimeProductCubicEnergy,
    pairedEtaMoebiusPrimeMixedCubicCorrelation, Complex.div_natCast_re,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    add_div, sub_div, mul_div_assoc]
  rw [Complex.re_sum]

private theorem norm_mean_mixed_sq_le (L : ℕ) (f g : ℕ → ℂ) :
    ‖(∑ t ∈ Finset.range L, f t * starRingEnd ℂ (g t)) / (L : ℂ)‖ ^ 2 ≤
      ((∑ t ∈ Finset.range L, ‖f t‖ ^ 2) / (L : ℝ)) *
        ((∑ t ∈ Finset.range L, ‖g t‖ ^ 2) / (L : ℝ)) := by
  have hn := norm_sum_le (Finset.range L) (fun t ↦ f t * starRingEnd ℂ (g t))
  simp only [norm_mul, norm_conj] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun t ↦ ‖f t‖) (fun t ↦ ‖g t‖)
  rw [norm_div, Complex.norm_natCast, div_pow]
  apply (div_le_div_of_nonneg_right (hs.trans hc) (sq_nonneg (L : ℝ))).trans_eq
  ring

/-- The full complex mixed correlation is bounded by the product of the actual original and removed mean squares, on the same physical window. -/
theorem norm_pairedEtaMoebiusPrimeMixedCubicCorrelation_sq_le
    (rho : NontrivialZetaZero) (p v : ℕ) :
    ‖pairedEtaMoebiusPrimeMixedCubicCorrelation rho p v‖ ^ 2 ≤
      pairedEtaCompletedMoebiusLargeMeanSquare rho ((p * v) ^ 3) ((p * v) ^ 3) ((p * v) ^ 2) *
        pairedEtaMoebiusPrimeProductCubicEnergy rho p v := by
  exact norm_mean_mixed_sq_le ((p * v) ^ 3)
    (fun t ↦ pairedEtaCompletedMoebiusLargeAggregate rho ((p * v) ^ 3 + t) ((p * v) ^ 2))
    (fun t ↦ pairedEtaCompletedMoebiusPrimeProductAggregate rho p ((p * v) ^ 2) ((p * v) ^ 3 + t))

private theorem full_prime_cubic_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {p : ℕ} (hp : 0 < p) :
    Tendsto (fun v : ℕ ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho
      ((p * v) ^ 3) ((p * v) ^ 3) ((p * v) ^ 2)) atTop
        (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hcofinal : Tendsto (fun v : ℕ ↦ p * v) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with v hv
    exact hv.trans (Nat.le_mul_of_pos_left _ hp)
  exact (pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho).comp hcofinal

/-- Every mixed interaction of the removed odd-prime family with the original full aggregate vanishes together, without assigning a sign to any individual pair. -/
theorem pairedEtaMoebiusPrimeMixedCubicCorrelation_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Tendsto (pairedEtaMoebiusPrimeMixedCubicCorrelation rho p) atTop (𝓝 0) := by
  have hu := pairedEtaMoebiusPrimeProductCubicEnergy_tendsto_zero rho hrho hp hodd
  have hh := full_prime_cubic_tendsto_source rho hrho hp.pos
  have hz : Tendsto (fun v ↦ ‖pairedEtaMoebiusPrimeMixedCubicCorrelation rho p v‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ sq_nonneg _) (norm_pairedEtaMoebiusPrimeMixedCubicCorrelation_sq_le rho p)
    simpa only [mul_zero] using hh.mul hu
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hz.sqrt

/-- Deleting all product rows and columns divisible by a fixed odd prime has vanishing total signed cost in the original full mean square. -/
theorem pairedEtaMoebiusLargeMeanSquare_sub_primeFree_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Tendsto (fun v : ℕ ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho
      ((p * v) ^ 3) ((p * v) ^ 3) ((p * v) ^ 2) - pairedEtaMoebiusPrimeFreeCubicEnergy rho p v)
      atTop (𝓝 0) := by
  have hu := pairedEtaMoebiusPrimeProductCubicEnergy_tendsto_zero rho hrho hp hodd
  have hm : Tendsto (fun v ↦ (pairedEtaMoebiusPrimeMixedCubicCorrelation rho p v).re) atTop (𝓝 0) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (pairedEtaMoebiusPrimeMixedCubicCorrelation_tendsto_zero rho hrho hp hodd) using 1
    · ext v
      rfl
    · rfl
  have hz := (hm.const_mul 2).sub hu
  simp only [mul_zero, sub_zero] at hz
  convert hz using 1
  ext v
  rw [pairedEtaMoebiusPrimeFreeCubicEnergy_eq_mixed]
  ring

/-- The exact complement after odd-prime exclusion still carries the original nonzero source square; an independent sub-source estimate for the surviving products remains necessary. -/
theorem pairedEtaMoebiusPrimeFreeCubicEnergy_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Tendsto (pairedEtaMoebiusPrimeFreeCubicEnergy rho p) atTop
      (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hh := full_prime_cubic_tendsto_source rho hrho hp.pos
  have hd := pairedEtaMoebiusLargeMeanSquare_sub_primeFree_tendsto_zero rho hrho hp hodd
  have hz := hh.sub hd
  simp only [sub_zero] at hz
  convert hz using 1
  ext v
  ring

end

end RiemannGaussian
