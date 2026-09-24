/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityPacket
import RiemannGaussian.ZetaRieszRectangleTailRates

/-!
# Phase-preserving cells for the literal parity packet

The cell main term is the signed weighted difference, not its absolute
mass. Only the phase-transport error is bounded in norm. Exponentially
thin cells pay that error independently at the original source scale.
No estimate for the remaining signed cell main term is assumed or proved.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open Filter Topology
open ZetaRieszJointAllocation ZetaRieszTypeII ZetaRieszAnnulusJoint
open ZetaRieszSkewAllocation ZetaArithmeticBandCorrelation

/-- Deterministic half-width cells of the total logarithm. -/
def logCell (d : ℝ) (n : ℕ) : ℕ := ⌊Real.log n / (2*d)⌋₊

/-- The midpoint of the deterministic cell of full width twice d. -/
def cellCenter (d : ℝ) (k : ℕ) : ℝ := (2*(k : ℝ)+1)*d

theorem logCell_distance {d : ℝ} (hd : 0 < d) (n : ℕ) :
    |Real.log n-cellCenter d (logCell d n)| ≤ d := by
  have hx := div_nonneg (Real.log_natCast_nonneg n) (by positivity : 0 ≤ 2*d)
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one (Real.log n/(2*d))
  have h₁ := (le_div_iff₀ (by positivity : 0 < 2*d)).mp hlo
  have h₂ := (div_lt_iff₀ (by positivity : 0 < 2*d)).mp hhi
  unfold cellCenter logCell
  rw [abs_le]
  constructor <;> nlinarith

/-- Exact signed density in a total-log cell: both prime-count classes,
all masks, the factorial rectangle and the allocation are still inside. -/
def cellBalance (u : ℝ) (N K : ℕ) (d : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ (narrowBand u N K).filter (fun n => logCell d n = k), packetDensity u N K n

/-- The exact signed cell masses with only their phases frozen at cell centers. -/
def frozenPacket (u y : ℝ) (N K : ℕ) (d : ℝ) : ℂ :=
  ∑ k ∈ (narrowBand u N K).image (logCell d),
    (cellBalance u N K d k : ℂ) * unitPhase (-y*cellCenter d k)

/-- The cell comparison keeps the two nonnegative arithmetic masses
coupled, with their actual opposite signs. -/
theorem cellBalance_eq_difference (u : ℝ) (N K : ℕ) (d : ℝ) (k : ℕ) :
    cellBalance u N K d k =
      (∑ n ∈ (narrowBand u N K).filter (fun n => logCell d n = k), tripleDensity u N K n)-
      ∑ n ∈ (narrowBand u N K).filter (fun n => logCell d n = k), quintupleDensity u N K n := by
  simp only [cellBalance, packetDensity_eq_difference, Finset.sum_sub_distrib]

/-- The remaining numerical obligation retains the cell's common cosine;
a surplus of quintuple counts alone cannot delete this factor. -/
theorem re_frozenPacket (u y : ℝ) (N K : ℕ) (d : ℝ) :
    (frozenPacket u y N K d).re = ∑ k ∈ (narrowBand u N K).image (logCell d),
      cellBalance u N K d k*Real.cos (y*cellCenter d k) := by
  simp only [frozenPacket, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, unitPhase, Complex.exp_re]
  apply Finset.sum_congr rfl
  intro k _
  simp [Complex.mul_re, Complex.mul_im, Real.cos_neg]

/-- Grouping by cells is exactly finite; no label is completed or lost. -/
theorem frozenPacket_eq_sum (u y : ℝ) (N K : ℕ) (d : ℝ) :
    frozenPacket u y N K d = ∑ n ∈ narrowBand u N K,
      (packetDensity u N K n : ℂ) * unitPhase (-y*cellCenter d (logCell d n)) := by
  unfold frozenPacket cellBalance
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  have he : ∀ k ∈ (narrowBand u N K).image (logCell d),
      (∑ n ∈ (narrowBand u N K).filter (fun n => logCell d n = k),
        (packetDensity u N K n : ℂ)*unitPhase (-y*cellCenter d k)) =
      ∑ n ∈ (narrowBand u N K).filter (fun n => logCell d n = k),
        (packetDensity u N K n : ℂ)*unitPhase (-y*cellCenter d (logCell d n)) := by
    intro k _
    apply Finset.sum_congr rfl
    intro n hn
    rw [(Finset.mem_filter.mp hn).2]
  simp_rw [Finset.sum_congr rfl he]
  exact Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _

/-- The phase error is paid separately; the signed cell balance remains
the main term. The error is width times total variation, not width alone. -/
theorem packet_phase_error (u y : ℝ) (N K : ℕ) {d : ℝ} (hd : 0 < d) :
    ‖packetResponse u y N K-frozenPacket u y N K d‖ ≤
      |y| *d*∑ n ∈ narrowBand u N K, |packetDensity u N K n| := by
  rw [packetResponse, frozenPacket_eq_sum]
  simp_rw [packetAtom_eq_density_phase]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hh := norm_unitPhase_sub_le (-y*Real.log n) (-y*cellCenter d (logCell d n))
  have he : -y*Real.log n-(-y*cellCenter d (logCell d n)) =
      -y*(Real.log n-cellCenter d (logCell d n)) := by ring
  rw [he, abs_mul, abs_neg] at hh
  calc
    _ ≤ |packetDensity u N K n| *(|y| *|Real.log n-cellCenter d (logCell d n)|) :=
      mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ ≤ |packetDensity u N K n| *(|y| *d) := by
      gcongr
      exact logCell_distance hd n
    _ = _ := by ring

/-- The existing unconditional summable majorant applies to the actual
selected density, because its selection is between zero and one. -/
theorem packetDensity_bound (u : ℝ) (N K n : ℕ) :
    |packetDensity u N K n| ≤ rectangleTilt⁻¹^N *
      (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  have he := packetAtom_eq_density_phase u 0 N K n
  simp only [neg_zero, zero_mul, unitPhase, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one] at he
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← he]
  unfold packetAtom
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (packetSelection_bounds u N K n).1]
  apply (mul_le_of_le_one_left (norm_nonneg _) (packetSelection_bounds u N K n).2).trans
  rw [norm_mul]
  have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*(0 : ℂ)) n‖ ≤
      rectangleTilt⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*(0 : ℂ)) n
      (by norm_num [rectangleTilt] : 0 < rectangleTilt) using 1
    norm_num [rectangleTilt]
  calc
    _ ≤ zetaMoebiusLogMajorant n*(rectangleTilt⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) :=
      mul_le_mul (norm_residualCoefficient_le _ (SquarefreeVaughanLogSource.length_pos u N) N n)
        hk (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg _)
    _ = _ := by ring

/-- A concrete exponentially thin width pays the complete phase error. -/
def packetCellWidth (N : ℕ) : ℝ := Real.exp (-(N : ℝ)/4000)

theorem packet_phase_error_at_source (N K : ℕ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(packetResponse u y N K-
      frozenPacket u y N K (packetCellWidth N))‖ ≤
      ZetaRieszWideOwnerAudit.radiusCeiling*|y| *rectangleMaskRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have hmass : (∑ n ∈ narrowBand u N K, |packetDensity u N K n|) ≤
      rectangleTilt⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
    apply (Finset.sum_le_sum (fun n _ => packetDensity_bound u N K n)).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num [rectangleTilt])
    exact Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
      (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num))
  have hw : 0 < packetCellWidth N := Real.exp_pos _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ u^(N+1)*(|y| *packetCellWidth N*
        (rectangleTilt⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144))) :=
      mul_le_mul_of_nonneg_left ((packet_phase_error u y N K hw).trans
        (mul_le_mul_of_nonneg_left hmass (mul_nonneg (abs_nonneg _) hw.le))) (pow_nonneg hu _)
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*(|y| *packetCellWidth N*
        (rectangleTilt⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144))) := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huU _)
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hw.le)
        (mul_nonneg (by norm_num [rectangleTilt])
          (zetaMoebiusLogMajorantMass_nonneg _))
    _ = _ := by
      have he : packetCellWidth N = Real.exp (-(1/4000 : ℝ))^N := by
        rw [packetCellWidth, ← Real.exp_nat_mul]
        congr 1
        ring
      simp only [he, rectangleMaskRate, div_eq_mul_inv, mul_pow, pow_succ]
      ring

/-- All original masks remain in the signed cell main term, while the
entire phase-transport error independently tends to zero. -/
theorem tendsto_packet_sub_frozen (K : ℕ → ℕ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(packetResponse u y N (K N)-
      frozenPacket u y N (K N) (packetCellWidth N))) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one rectangleMaskRate_bounds.1
    rectangleMaskRate_bounds.2).const_mul (ZetaRieszWideOwnerAudit.radiusCeiling*|y|)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [mul_zero, zero_mul] at ht
  exact squeeze_zero_norm (fun N => packet_phase_error_at_source N (K N) y hu huU) ht

/-- A larger magnitude of negative-coefficient quintuple mass is adverse
at common phase zero. A density surplus alone is not a signed lower bound. -/
theorem common_phase_surplus_is_negative {s q : ℝ} (h : s < q) :
    (((s-q : ℝ) : ℂ)*unitPhase 0).re < 0 := by
  simpa [unitPhase] using sub_neg.mpr h

end
end RiemannGaussian.ZetaRieszParityPacket
