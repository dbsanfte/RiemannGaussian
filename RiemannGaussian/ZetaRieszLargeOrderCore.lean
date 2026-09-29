/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCubicPrimeEnergy

/-!
# A uniform large-order payment inside the previous whole core

The literal core's two outer radial strips are paid at the explicit
geometric rate exp(-N/1000000), uniformly in height, radius, counts and
all existing arithmetic masks. The remaining joint cost is restricted to
1.971 N < log n <= 2.029 N, without changing the original carrier.
The central signed estimate remains open.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLargeOrderCore
open Real Filter Topology LogarithmicDeviation ZetaArithmeticDeviationBounds
  ZetaArithmeticLogWindow ZetaRieszJointAllocation ZetaRieszParityPacket

/-- One fixed summable tilt for both new radial edges. -/
def sigma : ℝ := 1+1/10000000

/-- An explicit large-order geometric saving, not a fitted finite-order rate. -/
def rate : ℝ := exp (-(1/1000000 : ℝ))

/-- Both arithmetic tails have a genuinely subunit common rate. -/
theorem rate_bounds : 0 < rate ∧ rate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

private theorem lower_log_bound :
    log (ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000))+
      (sigma-3/2+(1971/1000 : ℝ)⁻¹)*(1971/1000) < -(1/1000000 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 288029/39711971)
    (by norm_num : (288029/39711971 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at h
  have he : (20000000/19711971 : ℝ) =
      (ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000))⁻¹ := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  rw [he,Real.log_inv] at h
  norm_num [sigma]
  linarith

private theorem upper_log_bound :
    log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000))+
      (sigma-3/2+(2029/1000 : ℝ)⁻¹)*(2029/1000) < -(1/1000000 : ℝ) := by
  have hl : log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000)) <
      (2029/2000-1-(1/10000000)*(2029/1000)-1/1000000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 2029/2000-1-(1/10000000)*(2029/1000)-1/1000000) 4
    norm_num [Finset.sum_range_succ] at h
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
    linarith
  norm_num [sigma] at *
  linarith

/-- The lower edge pays the original factorial/source scale at every
large order, with an explicit strict exponential margin. -/
theorem lower_rate_lt :
    ZetaRieszWideOwnerAudit.radiusCeiling*((1971/1000)*
      exp ((sigma-3/2+(1971/1000 : ℝ)⁻¹)*(1971/1000))) < rate := by
  have hu : 0 < ZetaRieszWideOwnerAudit.radiusCeiling := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  calc
    _ = exp (log (ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000))+
        (sigma-3/2+(1971/1000 : ℝ)⁻¹)*(1971/1000)) := by
      rw [Real.exp_add,Real.exp_log (by positivity)]
      ring
    _ < _ := Real.exp_lt_exp.mpr lower_log_bound

/-- The upper edge has the SAME explicit saving, with the moving length,
factorial kernel and source radius still retained in the arithmetic bound. -/
theorem upper_rate_lt :
    ZetaRieszWideOwnerAudit.radiusCeiling*((2029/1000)*
      exp ((sigma-3/2+(2029/1000 : ℝ)⁻¹)*(2029/1000))) < rate := by
  have hu : 0 < ZetaRieszWideOwnerAudit.radiusCeiling := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  calc
    _ = exp (log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000))+
        (sigma-3/2+(2029/1000 : ℝ)⁻¹)*(2029/1000)) := by
      rw [Real.exp_add,Real.exp_log (by positivity)]
      ring
    _ < _ := Real.exp_lt_exp.mpr upper_log_bound

/-- Every dominated selection outside the contracted window is paid at
an explicit geometric rate, with ONE finite constant for all original
orders, radii, heights, masks and count cutoffs. No zero hypothesis. -/
theorem exists_edge_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      (∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n) →
      ∀ (y u : ℝ), 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*((∑ n ∈ S, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
          ∑ n ∈ deviationBand S (1971/1000) (2029/1000) N,
            a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤ rate^N*C := by
  let U := ZetaRieszWideOwnerAudit.radiusCeiling
  let C₀ := U*tiltConstant (1 : Polynomial ℂ) (1971/1000 : ℝ)⁻¹ sigma
  let C₁ := U*tiltConstant (1 : Polynomial ℂ) (2029/1000 : ℝ)⁻¹ sigma
  have hU : 0 < U := by norm_num [U,ZetaRieszWideOwnerAudit.radiusCeiling]
  have hC₀ : 0 ≤ C₀ := mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num))
  have hC₁ : 0 ≤ C₁ := mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num))
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro N S a ha y u hu huU
  have hl := norm_normalized_sum_le
    (S.filter (fun n => log n ≤ (1971/1000 : ℝ)*N)) a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (1 : Polynomial ℂ) N y hU
    (by norm_num : (0 : ℝ) < 1971/1000) (by norm_num [sigma] : 1 < sigma) (by
      intro n hn
      have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hn).2
        (by norm_num [sigma] : 0 ≤ sigma-3/2+(1971/1000 : ℝ)⁻¹)
      nlinarith only [h])
  have hh := norm_normalized_sum_le
    (S.filter (fun n => (2029/1000 : ℝ)*N < log n)) a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (1 : Polynomial ℂ) N y hU
    (by norm_num : (0 : ℝ) < 2029/1000) (by norm_num [sigma] : 1 < sigma) (by
      intro n hn
      have h := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hn).2.le
        (by norm_num [sigma] : sigma-3/2+(2029/1000 : ℝ)⁻¹ ≤ 0)
      nlinarith only [h])
  simp only [SquarefreeEulerQuadratic.primeFilterKernel_one,zetaPrimeLogKernel] at hl hh ⊢
  apply (sourceScale_norm_mono hu huU N _).trans
  rw [sum_sub_deviationBand (hab := by norm_num),mul_add]
  apply (norm_add_le _ _).trans
  have h0 := pow_le_pow_left₀ (by positivity) lower_rate_lt.le N
  have h1 := pow_le_pow_left₀ (by positivity) upper_rate_lt.le N
  calc
    _ ≤ _ := add_le_add hl hh
    _ ≤ rate^N*C₀+rate^N*C₁ := add_le_add
      (mul_le_mul_of_nonneg_right h0 hC₀) (mul_le_mul_of_nonneg_right h1 hC₁)
    _ = _ := by ring

/-- The actual original-core error tends to zero even for moving heights,
radii and count cutoffs. Every remaining finite mask is unchanged. -/
theorem tendsto_core_edge (u y : ℕ → ℝ) (K : ℕ → ℕ)
    (hu : ∀ N, 0 ≤ u N ∧ u N ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u N : ℂ)^(N+1)*(coreResponse (u N) (y N) N (K N)-
      ∑ n ∈ deviationBand (coreBand (u N) N (K N)) (1971/1000) (2029/1000) N,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes (u N) N)
          (SquarefreeVaughanLogSource.length (u N) N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*(y N)) n)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := exists_edge_bound
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one rate_bounds.1.le rate_bounds.2).mul_const C
  simp only [zero_mul] at ht
  apply squeeze_zero_norm (fun N => ?_) ht
  exact hb N (coreBand (u N) N (K N)) _
    (fun n _ => norm_residualCoefficient_le _ (SquarefreeVaughanLogSource.length_pos (u N) N) N n)
    (y N) (u N) (hu N).1 (hu N).2

open ZetaRieszJointPrimeEnergy ZetaRieszQuadraticPrimeEnergy ZetaRieszCubicPrimeEnergy

/-- BOTH original whole-core bounds now pay all labels outside the smaller
radial window geometrically, before charging any remaining joint energy.
The actual centers and costs inside it stay explicit; no bound for their
eventual combined size is assumed or claimed. -/
theorem exists_contracted_core_bounds :
    ∃ E C : ℝ, 0 < E ∧ 0 ≤ C ∧ ∀ (u y : ℝ) (N K : ℕ)
      (I : Finset ℕ) (O : ℕ → ℕ → ℝ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      let B := deviationBand ((coreBand u N K).filter Squarefree) (1971/1000) (2029/1000) N;
      Coordinates I (ownerPrimes B) O →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H₂ := wholeCenter A B I O N L y (u^(N+1));
      let C₂ := wholeQuadraticCost E A B I O N L y (u^(N+1));
      let H₃ := wholeCubicCenter A B I O N L y (u^(N+1));
      let C₃ := wholeCubicCost E A B I O N L y (u^(N+1));
      let J := u^(N+1)*(coreResponse u y N K).re;
      max (H₂-C₂) (H₃-C₃)-rate^N*C ≤ J ∧
        J ≤ min (H₂+C₂) (H₃+C₃)+rate^N*C ∧ C₃ ≤ C₂ := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_cubic_bounds
  obtain ⟨C,hC,hgeo⟩ := exists_edge_bound
  refine ⟨E,C,hE,hC,fun u y N K I O hu hU hO => ?_⟩
  let S := (coreBand u N K).filter Squarefree
  let B := deviationBand S (1971/1000) (2029/1000) N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hB : ∀ n ∈ B, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1)
    exact ⟨hs.2,core_count hs.1⟩
  have hb := hbound A B I O N L y (u^(N+1)) hB hO
  have hg := hgeo N S (residualCoefficient A L N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  have he := (Complex.abs_re_le_norm _).trans hg
  dsimp only [S,A,L] at he
  rw [← core_eq_squarefree] at he
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re,mul_sub] at he
  have hel := (abs_le.mp he).1
  have heu := (abs_le.mp he).2
  dsimp only [A,B,S,L] at hb
  dsimp only
  refine ⟨?_,?_,hb.2.2⟩
  · linarith only [hb.1,hel]
  · linarith only [hb.2.1,heu]

end RiemannGaussian.ZetaRieszLargeOrderCore
