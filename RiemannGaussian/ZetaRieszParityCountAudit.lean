/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityCells
import RiemannGaussian.RosserSchoenfeldLargePrimeCounting

/-!
# Counting-resolution audit for the proposed parity transport

The proved Rosser bounds cannot certify a positive count by endpoint
subtraction in the exponentially thin cells which independently pay the
source-scale phase error. This is an obstruction to that use of those
estimates, not a claim that the intervals are empty, that stronger short
interval results are unavailable, or that the signed packet bound is false.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open Filter Topology Real
open RosserSchoenfeldComparison ZetaRieszSkewAllocation

private theorem exp_small_linear {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1/2) :
    exp d ≤ 1+2*d := by
  apply (Real.exp_bound_div_one_sub_of_interval hd (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-d)).mpr
  nlinarith

/-- At these widths the actual lower/upper comparison functions overlap.
Consequently subtracting the repository's two endpoint count bounds gives
a nonpositive lower allowance even before weights or masks are imposed. -/
theorem rosser_thin_interval_overlap {t d : ℝ} (ht : 2 ≤ t) (hd : 0 ≤ d)
    (hdt : d ≤ 1/(16*t)) : lower (exp (t+d)) < upper (exp t) := by
  have ht0 : 0 < t := by linarith
  have htd : 16*t*d ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16*t)).mp hdt
    nlinarith
  have hdhalf : d ≤ 1/2 := by nlinarith
  have he := exp_small_linear hd hdhalf
  have hden : 0 < t+d-1/2 := by linarith
  have hrat : (1+2*d)/(t+d-1/2) < 1/t*(1+3/(2*t)) := by
    apply (div_lt_iff₀ hden).mpr
    apply (mul_lt_mul_iff_right₀ (show 0 < 2*t^2 by positivity)).mp
    have h₁ : 16*t^2*d ≤ t := by nlinarith [mul_le_mul_of_nonneg_right htd ht0.le]
    field_simp
    nlinarith [sq_nonneg t, mul_nonneg hd ht0.le]
  unfold RosserSchoenfeldComparison.lower RosserSchoenfeldComparison.upper
  rw [log_exp, log_exp, exp_add]
  calc
    _ ≤ exp t*(1+2*d)/(t+d-1/2) := by gcongr
    _ = exp t*((1+2*d)/(t+d-1/2)) := by ring
    _ < exp t*(1/t*(1+3/(2*t))) := mul_lt_mul_of_pos_left hrat (exp_pos _)
    _ = _ := by ring

/-- This is the literal prime-count difference and the literal lower
allowance supplied by the existing proved endpoints. The latter has the
wrong sign to certify even one prime at this resolution. -/
theorem actual_prime_count_thin_cell {t d : ℝ} (ht : 5100 ≤ t) (hd : 0 ≤ d)
    (hdt : d ≤ 1/(16*t)) :
    lower (exp (t+d))-upper (exp t) <
      (Nat.primeCounting ⌊exp (t+d)⌋₊ : ℝ)-(Nat.primeCounting ⌊exp t⌋₊ : ℝ) ∧
    lower (exp (t+d))-upper (exp t) < 0 := by
  have hl := (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100
    (Real.exp_le_exp.mpr (show (5100 : ℝ) ≤ t+d by linarith))).1
  have hu := (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100
    (Real.exp_le_exp.mpr ht)).2
  exact ⟨sub_lt_sub hl hu, sub_neg.mpr (rosser_thin_interval_overlap (by linarith) hd hdt)⟩

/-- The precise exponentially thin width eventually lies below the
counting resolution, uniformly for all prime logs in the narrow carrier. -/
theorem eventually_packet_cells_below_count_resolution :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 5100 ≤ t → t ≤ (41/20 : ℝ)*N →
      2*packetCellWidth N ≤ 1/(16*t) := by
  have he : 0 < exp (-(1/4000 : ℝ)) := exp_pos _
  have he1 : exp (-(1/4000 : ℝ)) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 he he1
  have ht' : Tendsto (fun N : ℕ => 96*((N : ℝ)+1)*packetCellWidth N) atTop (𝓝 0) := by
    convert ht.const_mul 96 using 1
    · ext N
      have heq : packetCellWidth N = exp (-(1/4000 : ℝ))^N := by
        rw [packetCellWidth, ← Real.exp_nat_mul]
        congr 1
        ring
      simp only [heq, pow_one]
      ring
    · norm_num
  filter_upwards [ht'.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN t htlo hthi
  have hw : 0 < packetCellWidth N := exp_pos _
  apply (le_div_iff₀ (by positivity : 0 < 16*t)).mpr
  have hh := mul_le_mul_of_nonneg_right hthi hw.le
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Polynomially shrinking widths do not pay the existing exponential
variation envelope at source scale. This is an envelope audit, not a
lower bound for the actual signed packet or its actual transport error. -/
theorem polynomial_width_envelope_diverges {u : ℝ} (hu : 1/2 < u) (B : ℝ) :
    Tendsto (fun t : ℝ => exp (log (u/rectangleTilt)*t)/t^B) atTop atTop := by
  apply tendsto_exp_mul_div_rpow_atTop
  apply log_pos
  apply (one_lt_div (by norm_num [rectangleTilt] : 0 < rectangleTilt)).mpr
  norm_num [rectangleTilt] at *
  linarith

/-- At the smallest allowed prime-log share, this cell width corresponds
to an ordinary short interval of exponent 77/78, not a microscopic
integer interval. Stronger short-interval counting is a separate possible
input; the endpoint-overlap audit does not rule it out. -/
theorem packet_width_vs_smallest_prime {N t : ℝ}
    (ht : (39/2000 : ℝ)*N ≤ t) : exp (-(t/78)) ≤ exp (-N/4000) := by
  apply exp_le_exp.mpr
  linarith

end
end RiemannGaussian.ZetaRieszParityPacket
