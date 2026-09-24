/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityCells

/-!
# Independent removal of the upper cells without a quintuple surplus

The original carrier and Type-II target are unchanged. This theorem pays
the difference to the smaller 1.95N < log(n) <= 2.03N window, independently
of zeros and uniformly in height. Numerical exploration motivated the
upper endpoint; its strict deviation margin is proved with rational
inequalities, not numerical quadrature.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open Filter Topology LogarithmicDeviation ZetaArithmeticDeviationBounds
open ZetaRieszTypeII ZetaRieszJointAllocation ZetaRieszAnnulusJoint

/-- Both deviations still beat the source growth at the requested upper radius. -/
theorem core_window_costs :
    Real.log (2*ZetaRieszWideOwnerAudit.radiusCeiling) < deviationCost (39/20) ∧
      Real.log (2*ZetaRieszWideOwnerAudit.radiusCeiling) < deviationCost (203/100) := by
  have hlo : Real.log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤
      Real.log (2*ZetaRieszTypeII.radiusCeiling) := by
    apply Real.log_le_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling, ZetaRieszTypeII.radiusCeiling]
  refine ⟨hlo.trans_lt narrow_window_costs.1, ?_⟩
  have hhi : Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(203/100)) < (3/200 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/200) 4
    norm_num [Finset.sum_range_succ] at h
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
    linarith
  have he := log_rate_eq_deviation
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] : 0 < ZetaRieszWideOwnerAudit.radiusCeiling)
    (by norm_num : (0 : ℝ) < 203/100)
  linarith

/-- The smaller support is an intersection of the literal original support. -/
def coreBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  deviationBand (narrowBand u N K) (39/20) (203/100) N

/-- The original narrow carrier restricted to the independently paid core window. -/
def coreResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K,
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The unchanged packet atoms in the smaller core window. -/
def corePacketResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, packetAtom u y N K n

/-- All discarded cells of the full original narrow carrier have an
independent geometric bound, uniformly in every original parameter. -/
theorem exists_core_window_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*(narrowResponse u y N K-coreResponse u y N K)‖ ≤ r^N*C := by
  obtain ⟨r,C,hr0,hr1,hC,h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    core_window_costs.1 core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N K y u hu huU
  simpa only [narrowResponse, coreResponse, coreBand,
    SquarefreeEulerQuadratic.primeFilterKernel_one, zetaPrimeLogKernel] using
    h N (narrowBand u N K)
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N)
      (fun n _ => norm_residualCoefficient_le _ (SquarefreeVaughanLogSource.length_pos u N) N n)
      y u hu huU

/-- The same discarded-cell estimate applies to the actual paired packet;
its selection lies between zero and one, including all fractional orders. -/
theorem exists_core_packet_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*(packetResponse u y N K-corePacketResponse u y N K)‖ ≤ r^N*C := by
  obtain ⟨r,C,hr0,hr1,hC,h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    core_window_costs.1 core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N K y u hu huU
  have hb (n : ℕ) (_hn : n ∈ narrowBand u N K) :
      ‖(packetSelection u N K n : ℂ)*residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n‖ ≤ zetaMoebiusLogMajorant n := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (packetSelection_bounds u N K n).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (packetSelection_bounds u N K n).2).trans
      (norm_residualCoefficient_le _ (SquarefreeVaughanLogSource.length_pos u N) N n)
  simpa only [packetResponse, corePacketResponse, coreBand, packetAtom, mul_assoc,
    SquarefreeEulerQuadratic.primeFilterKernel_one, zetaPrimeLogKernel] using
    h N (narrowBand u N K)
      (fun n => (packetSelection u N K n : ℂ)*residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n) hb y u hu huU

/-- The packet's entire upper-edge deletion is paid before trying to
compare the remaining triple/quintuple cells. -/
theorem tendsto_packet_sub_core (K : ℕ → ℕ) (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(packetResponse u (y N) N (K N)-
      corePacketResponse u (y N) N (K N))) atTop (𝓝 0) := by
  obtain ⟨r,C,hr0,hr1,_,hb⟩ := exists_core_packet_error
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C
  simp only [zero_mul] at ht
  exact squeeze_zero_norm (fun N => hb N (K N) (y N) u hu huU) ht

end
end RiemannGaussian.ZetaRieszParityPacket
