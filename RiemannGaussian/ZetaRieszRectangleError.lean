/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleAllocation

/-!
# Independent source-scale removal of the rectangle's old allocation

Only the old allocated part is removed. All other masks remain literal;
no claim about their completion error or the raw rectangle's sign is made.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency

/-- The actual allocated rectangle atom has a summable geometric
majorant, uniformly in the full complex phase. -/
theorem allocatedRectangleAtom_bound (N : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) {n q : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 3)
    (hq : q ∈ secondIncidences u N n) :
    ‖(u : ℂ) ^ (N + 1) *
      ((boundedShare (intermediatePrimes u N) N n : ℂ) * rawRectangleAtom u y N n q)‖ ≤
      (3 * radiusCeiling) * rectangleAllocationRate ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let w := rectangleMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
    (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ))
  obtain ⟨_, _, _, hx, hr⟩ := second_log_data hn hc hq
  have hw : 0 ≤ w := (rectangleMass_bounds N hx.1 hx.2 hr.1 hr.2).1
  have hb : 0 ≤ boundedShare A N n := (boundedShare_bounds A N n).1
  have hjoint := boundedShare_mul_rectangleMass A N hn hc hr.1 hr.2
  have hcbd := SquarefreeVaughanLogSource.norm_coefficient_le
    (SquarefreeVaughanLogSource.length_pos u N) n
  have hk : ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3 / 2 + Complex.I * y) n
      (by norm_num : (0 : ℝ) < 131071 / 262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N + 1)
  have he : Real.exp (-(N : ℝ) / 3200) = Real.exp (-(1 / 3200 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change ‖(u : ℂ) ^ (N + 1) * ((boundedShare A N n : ℂ) * ((w : ℂ) *
    (SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)))‖ ≤ _
  simp only [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu, Real.norm_of_nonneg hw, Real.norm_of_nonneg hb]
  calc
    _ = u ^ (N + 1) * (boundedShare A N n * w) *
        ‖SquarefreeVaughanLogSource.coefficient L n‖ *
          ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ := by ring
    _ ≤ radiusCeiling ^ (N + 1) * (3 * Real.exp (-(N : ℝ) / 3200)) *
        zetaMoebiusLogMajorant n *
          ((131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul hpow hjoint (mul_nonneg hb hw)
        (by unfold radiusCeiling; positivity)) hcbd (norm_nonneg _)
          (by unfold radiusCeiling; positivity)) hk (norm_nonneg _)
            (mul_nonneg (by unfold radiusCeiling; positivity) (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [he, rectangleAllocationRate, mul_pow, mul_pow, pow_succ]; ring

/-- The complete literal old allocated rectangle is geometrically small.
This is an independent arithmetic estimate, with no zero hypothesis. -/
theorem allocatedRectangleResponse_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ) ^ (N + 1) * allocatedRectangleResponse u y N K‖ ≤
      (3 * radiusCeiling) * rectangleAllocationRate ^ N *
        zetaMoebiusLogMajorantMass (1 + 1 / 262144) := by
  rw [allocatedRectangleResponse, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ tripleBand u N K, (3 * radiusCeiling) * rectangleAllocationRate ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
      rw [Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      have h := Finset.sum_le_sum (fun q (hq : q ∈ rectangleIncidences u N n) =>
        allocatedRectangleAtom_bound N y hu huU hs hc (Finset.mem_filter.mp hq).1)
      simp only [Finset.sum_const, nsmul_eq_mul] at h
      apply h.trans
      apply mul_le_of_le_one_left
      · exact mul_nonneg (mul_nonneg (by unfold radiusCeiling; positivity)
          (pow_nonneg rectangleAllocationRate_bounds.1 _))
          (mul_nonneg (zetaMoebiusLogMajorant_nonneg _) (Real.exp_pos _).le)
      · have hh : (rectangleIncidences u N n).card ≤ 1 :=
          (Finset.card_filter_le _ _).trans (secondIncidences_card_le_one hs)
        exact_mod_cast hh
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity)
          (pow_nonneg rectangleAllocationRate_bounds.1 _))

/-- The old allocation vanishes along the original dyadic schedule,
even for arbitrary moving heights. -/
theorem tendsto_allocatedRectangleResponse (y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      allocatedRectangleResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t))
      atTop (𝓝 0) := by
  have h := (((tendsto_pow_atTop_nhds_zero_of_lt_one
    rectangleAllocationRate_bounds.1 rectangleAllocationRate_bounds.2).const_mul
      (3 * radiusCeiling)).mul_const (zetaMoebiusLogMajorantMass (1 + 1 / 262144))).comp
        tendsto_dyadicMomentOrder
  simp only [mul_zero, zero_mul, Function.comp_def] at h
  exact squeeze_zero_norm (fun t => allocatedRectangleResponse_bound
    (dyadicMomentOrder t) (dyadicPrimeCount t) (y t) hu huU) h

/-- Source-scale removal of precisely the old allocation, with every
other rectangle mask unchanged. -/
theorem tendsto_raw_sub_rectangle (y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      (rawRectangleResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t) -
        rectangleResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)))
      atTop (𝓝 0) := by
  simpa only [rawRectangleResponse_eq, add_sub_cancel_right] using
    tendsto_allocatedRectangleResponse y hu huU

end
end RiemannGaussian.ZetaRieszSkewAllocation
