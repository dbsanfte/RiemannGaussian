/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityOrderPacket
import RiemannGaussian.ZetaRieszParityOrderPhase

/-!
# Independent removal of all exceptional derivative allocations

The complete bad packet is bounded at source scale using only the literal
multinomial tail and the existing arithmetic coefficient/kernel majorants.
All support, phase, allocation and physical masks remain in the sum.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint
open ZetaRieszPrimeCountFrequency ZetaRieszMatchedMiddle

/-- The exact normalized geometric rate after the summable majorant
has been inserted. Its strict saving includes the entire source growth. -/
def badOrderRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/400 : ℝ))

theorem badOrderRate_bounds : 0 ≤ badOrderRate ∧ badOrderRate < 1 := by
  constructor
  · unfold badOrderRate radiusCeiling; positivity
  · rw [badOrderRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/400 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

/-- An independent majorant for each literal exceptional atom,
uniformly in the phase height and the remaining finite count cutoff. -/
theorem badPacket_atom_bound (N K n : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*((badParitySelection u N K n : ℂ)*
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
      (39*radiusCeiling)*badOrderRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  have hb := badParitySelection_bounds u N K n
  have hc := norm_residualCoefficient_le (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) N n
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 131071/262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N+1)
  have he : Real.exp (-(N : ℝ)/400) = Real.exp (-(1/400 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
    Real.norm_of_nonneg hb.1]
  calc
    _ ≤ radiusCeiling^(N+1)*(39*Real.exp (-(N : ℝ)/400))*
        zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) := by
      calc
        _ = (u^(N+1)*badParitySelection u N K n)*
            ‖residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n‖*
              ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
        _ ≤ _ := mul_le_mul
          (mul_le_mul (mul_le_mul hpow hb.2 hb.1 (by unfold radiusCeiling; positivity))
            hc (norm_nonneg _) (by unfold radiusCeiling; positivity))
          hk (norm_nonneg _) (mul_nonneg (by unfold radiusCeiling; positivity)
            (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [he, badOrderRate, mul_pow, mul_pow, pow_succ]; ring

/-- The whole exceptional packet is independently geometrically small.
The result is uniform in height, rather than conditional on a zero. -/
theorem badPacket_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*badPacket u y N K‖ ≤
      (39*radiusCeiling)*badOrderRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [badPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ coreBand u N K, (39*radiusCeiling)*badOrderRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum (fun n _ => badPacket_atom_bound N K n y hu huU)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg badOrderRate_bounds.1 _))

/-- Every cofinal order schedule pays all exceptional orders, even at
arbitrary moving heights and count cutoffs. -/
theorem tendsto_badPacket (orders counts : ℕ → ℕ) (y : ℕ → ℝ)
    (horders : Tendsto orders atTop atTop) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*badPacket u (y t) (orders t) (counts t))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one badOrderRate_bounds.1
    badOrderRate_bounds.2).const_mul (39*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp horders
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => badPacket_bound (orders t) (counts t) (y t) hu huU) ht

/-- The literal packet differs from its good-order part by an
independently vanishing term. This asserts no bound on the good part. -/
theorem tendsto_fullParity_sub_good (orders counts : ℕ → ℕ) (y : ℕ → ℝ)
    (horders : Tendsto orders atTop atTop) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (fullParityPacket u (y t) (orders t) (counts t)-goodPacket u (y t) (orders t) (counts t)))
      atTop (𝓝 0) := by
  simpa only [fullParityPacket_split, add_sub_cancel_left] using
    tendsto_badPacket orders counts y horders hu huU

end
end RiemannGaussian.ZetaRieszParityOrderTail
