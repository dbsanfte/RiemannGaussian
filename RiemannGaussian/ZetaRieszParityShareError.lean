/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityMaskError
import RiemannGaussian.ZetaRieszParityShareTail

/-!
# Paying both finite factorial masks on the unchanged full parity support

Only errors proved geometrically small are removed. The full Riesz
coefficient, phase and literal log-share/physical/count/core masks remain.
The resulting coefficient box is not a product of completed prime legs.
-/
namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityPacket ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint

/-- The strict source-normalized rate for the original allocated fraction. -/
def allocationBoxRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/1000 : ℝ))

theorem allocationBoxRate_bounds : 0 ≤ allocationBoxRate ∧ allocationBoxRate < 1 := by
  constructor
  · unfold allocationBoxRate radiusCeiling; positivity
  · rw [allocationBoxRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/1000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

/-- The original signed coefficient on the very same finite packet support. -/
def coefficientBox (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The original allocated coefficient on exactly the same finite share-box support. -/
def allocationBoxError (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullParityBand u N K, (boundedShare (intermediatePrimes u N) N n : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem coefficientBox_eq (u y : ℝ) (N K : ℕ) :
    coefficientBox u y N K = shareBoxPacket u y N K+allocationBoxError u y N K := by
  unfold coefficientBox shareBoxPacket allocationBoxError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [residualCoefficient]
  push_cast
  ring

/-- An independent majorant for each literal old allocated atom,
uniformly in the phase height and the remaining finite count cutoff. -/
theorem allocationBoxError_atom_bound (N K n : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) (hn : n ∈ fullParityBand u N K) :
    ‖(u : ℂ)^(N+1)*((boundedShare (intermediatePrimes u N) N n : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
      (39*radiusCeiling)*allocationBoxRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  have hb := And.intro (boundedShare_bounds (intermediatePrimes u N) N n).1
    (fullParityBox_boundedShare (Finset.mem_filter.mp hn).2.1 (intermediatePrimes u N) N)
  have hc := SquarefreeVaughanLogSource.norm_coefficient_le
    (SquarefreeVaughanLogSource.length_pos u N) n
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
      (by norm_num : (0 : ℝ) < 131071/262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N+1)
  have he : Real.exp (-(N : ℝ)/1000) = Real.exp (-(1/1000 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
    Real.norm_of_nonneg hb.1]
  calc
    _ ≤ radiusCeiling^(N+1)*(39*Real.exp (-(N : ℝ)/1000))*
        zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) := by
      calc
        _ = (u^(N+1)*boundedShare (intermediatePrimes u N) N n)*
            ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖*
              ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
        _ ≤ _ := mul_le_mul
          (mul_le_mul (mul_le_mul hpow hb.2 hb.1 (by unfold radiusCeiling; positivity))
            hc (norm_nonneg _) (by unfold radiusCeiling; positivity))
          hk (norm_nonneg _) (mul_nonneg (by unfold radiusCeiling; positivity)
            (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [he, allocationBoxRate, mul_pow, mul_pow, pow_succ]; ring

/-- The whole old allocated part is independently geometrically small.
The result is uniform in height, rather than conditional on a zero. -/
theorem allocationBoxError_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*allocationBoxError u y N K‖ ≤
      (39*radiusCeiling)*allocationBoxRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [allocationBoxError, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ fullParityBand u N K, (39*radiusCeiling)*allocationBoxRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum (fun n hn => allocationBoxError_atom_bound N K n y hu huU hn)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg allocationBoxRate_bounds.1 _))

/-- The original allocation is paid without replacing any prime phase. -/
theorem tendsto_allocationBoxError (orders counts : ℕ → ℕ) (y : ℕ → ℝ)
    (horders : Tendsto orders atTop atTop) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*allocationBoxError u (y t) (orders t) (counts t))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one allocationBoxRate_bounds.1
    allocationBoxRate_bounds.2).const_mul (39*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp horders
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => allocationBoxError_bound (orders t) (counts t) (y t) hu huU) ht

/-- Both factorial masks are now paid at the actual source scale.
This is not a decay theorem for the surviving signed coefficient box. -/
theorem tendsto_coefficientBox_sub_fullParity (orders counts : ℕ → ℕ) (y : ℕ → ℝ)
    (horders : Tendsto orders atTop atTop) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (coefficientBox u (y t) (orders t) (counts t)-
        fullParityPacket u (y t) (orders t) (counts t))) atTop (𝓝 0) := by
  have h := (tendsto_allocationBoxError orders counts y horders hu huU).add
    (tendsto_shareBox_sub_fullParity orders counts y horders hu huU)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with t
  rw [coefficientBox_eq]
  ring

end
end RiemannGaussian.ZetaRieszParityOrderTail
