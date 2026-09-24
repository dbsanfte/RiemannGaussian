/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityRectangleTail
import RiemannGaussian.ZetaRieszParityOrderError

/-!
# Paying the literal factorial rectangle at source scale

The comparison keeps the exact log-share box, every arithmetic mask,
the old allocation and the full phase. Its sole difference is the
original factorial rectangle, whose omitted mass is now paid.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint

/-- The strict source-normalized rate after paying the omitted rectangle mass. -/
def rectangleOrderRate : ℝ :=
  radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/6000 : ℝ))

theorem rectangleOrderRate_bounds : 0 ≤ rectangleOrderRate ∧ rectangleOrderRate < 1 := by
  constructor
  · unfold rectangleOrderRate radiusCeiling; positivity
  · rw [rectangleOrderRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/6000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

/-- The same literal arithmetic packet with weight one on its original
factorial rectangle. Its exact difference is bounded below, not assumed. -/
def shareBoxPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K,
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The exact omitted factorial weight on the unchanged finite packet support. -/
def rectangleOrderError (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K, (rectangleOmittedMass N n : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The paid error refers to the original packet, not a new target. -/
theorem shareBoxPacket_eq (u y : ℝ) (N K : ℕ) :
    shareBoxPacket u y N K = fullParityPacket u y N K+rectangleOrderError u y N K := by
  have he : fullParityPacket u y N K = ∑ n ∈ fullParityBand u N K,
      (fullParitySelection u N K n : ℂ)*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hn
    change n ∉ fullParityBand u N K at hn
    rw [fullParitySelection, if_neg hn, Complex.ofReal_zero, zero_mul]
  rw [he, shareBoxPacket, rectangleOrderError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fullParitySelection, if_pos hn, ← add_mul, ← Complex.ofReal_add,
    rectangleMass_add_omitted (Finset.mem_filter.mp hn).2.1, Complex.ofReal_one, one_mul]

theorem rectangleOrderError_atom_bound (N K n : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) (hn : n ∈ fullParityBand u N K) :
    ‖(u : ℂ)^(N+1)*((rectangleOmittedMass N n : ℂ)*
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
      (6*radiusCeiling)*rectangleOrderRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  have hb := rectangleOmittedMass_bounds (Finset.mem_filter.mp hn).2.1 N
  have hc := norm_residualCoefficient_le (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) N n
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 131071/262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N+1)
  have he : Real.exp (-(N : ℝ)/6000) = Real.exp (-(1/6000 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
    Real.norm_of_nonneg hb.1]
  calc
    _ ≤ radiusCeiling^(N+1)*(6*Real.exp (-(N : ℝ)/6000))*
        zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) := by
      calc
        _ = (u^(N+1)*rectangleOmittedMass N n)*
            ‖residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n‖*
              ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
        _ ≤ _ := mul_le_mul
          (mul_le_mul (mul_le_mul hpow hb.2 hb.1 (by unfold radiusCeiling; positivity))
            hc (norm_nonneg _) (by unfold radiusCeiling; positivity))
          hk (norm_nonneg _) (mul_nonneg (by unfold radiusCeiling; positivity)
            (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [he, rectangleOrderRate, mul_pow, mul_pow, pow_succ]; ring

/-- The entire factorial mask error decays geometrically, independently
of zeta zeros and uniformly in the original moving height and count. -/
theorem rectangleOrderError_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*rectangleOrderError u y N K‖ ≤
      (6*radiusCeiling)*rectangleOrderRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [rectangleOrderError, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ fullParityBand u N K, (6*radiusCeiling)*rectangleOrderRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum (fun n hn => rectangleOrderError_atom_bound N K n y hu huU hn)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg rectangleOrderRate_bounds.1 _))

theorem tendsto_shareBox_sub_fullParity (orders counts : ℕ → ℕ) (y : ℕ → ℝ)
    (horders : Tendsto orders atTop atTop) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (shareBoxPacket u (y t) (orders t) (counts t)-
        fullParityPacket u (y t) (orders t) (counts t))) atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one rectangleOrderRate_bounds.1
    rectangleOrderRate_bounds.2).const_mul (6*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp horders
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  simp only [shareBoxPacket_eq, add_sub_cancel_left]
  exact squeeze_zero_norm (fun t => rectangleOrderError_bound (orders t) (counts t) (y t) hu huU) ht

end
end RiemannGaussian.ZetaRieszParityOrderTail
