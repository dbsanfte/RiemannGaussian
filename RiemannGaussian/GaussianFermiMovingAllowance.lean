/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RiemannGaussian.GaussianFermiZeroTailRate

/-!
# Vanishing Gaussian Fermi allowance at moving scales

The reflected-pair derivative cost grows at most as the inverse known
zero-free width. The actual multiplicity-weighted zero tail decays as the
inverse square root of height. Their product therefore vanishes uniformly
over every Gaussian scale between the square of that width and one.

This controls the full zero-side allowance. It does not assert an
unproved identity with a prime sum or a new numerical zero-free region.
-/

namespace RiemannGaussian.GaussianFermiMovingAllowance

noncomputable section
open Complex Filter Set
open scoped Topology Classical
open GaussianFermiDerivativeBounds GaussianFermiZeroTail GaussianFermiZeroTailRate

/-- The exact error allowance at the interior line supplied by the proved
zero-free margin, retaining the Gaussian scale and actual divisor tail. -/
def allowance (b H : ℝ) : ℝ :=
  let δ := zetaPoleReserveZeroMargin H
  4 * integralCost (1 - 2 * δ) b δ * divisorTail H

/-- The derivative cost is only inverse-linear in the strip margin,
uniformly over every admissible small Gaussian scale. -/
theorem integralCost_le_inverse_margin {δ b : ℝ} (hδ : 0 < δ) (hδu : δ ≤ 1 / 4)
    (hscale : δ ^ 2 ≤ b) (hb : b ≤ 1) :
    integralCost (1 - 2 * δ) b δ ≤
      (86 * Real.exp (1 / 2) * Real.sqrt Real.pi) / δ := by
  have hbpos : 0 < b := (sq_pos_of_pos hδ).trans_le hscale
  have hpoly : (2 * (1 - 2 * δ) + δ) ^ 2 ≤ 4 := by nlinarith
  have hamp : amplitudeCost (1 - 2 * δ) b δ ≤ 43 * Real.exp (1 / 2) := by
    unfold amplitudeCost
    nlinarith [Real.exp_pos (1 / 2)]
  have hrad : Real.pi / (b / 4) ≤ Real.pi / (δ ^ 2 / 4) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
  have hroot : Real.sqrt (Real.pi / (b / 4)) ≤ 2 * Real.sqrt Real.pi / δ := by
    calc
      _ ≤ Real.sqrt (Real.pi / (δ ^ 2 / 4)) := Real.sqrt_le_sqrt hrad
      _ = _ := by
        rw [show Real.pi / (δ ^ 2 / 4) = (Real.pi * 4) / δ ^ 2 by ring,
          Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le,
          Real.sqrt_sq hδ.le]
        norm_num
        ring
  unfold integralCost
  calc
    _ ≤ (43 * Real.exp (1 / 2)) * (2 * Real.sqrt Real.pi / δ) :=
      mul_le_mul hamp hroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

/-- The already proved zero-free region bounds the inverse strip margin
by a logarithm at every height at least one. -/
theorem inverse_margin_le_log {H : ℝ} (hH : 1 ≤ H) :
    1 / zetaPoleReserveZeroMargin H ≤ (7625 / 792 : ℝ) * Real.log (H + 2) := by
  have hm := zetaSignedPole_margin_le_poleReserve H
  have hp := zetaSignedPoleZeroMargin_pos H
  have hH0 : 0 ≤ H := by linarith
  calc
    _ ≤ 1 / zetaSignedPoleZeroMargin H := one_div_le_one_div_of_le hp hm
    _ = (7625 * Real.log (H + 2) - 2000) / 792 := by
      unfold zetaSignedPoleZeroMargin
      rw [abs_of_nonneg hH0]
      field_simp
    _ ≤ _ := by linarith

/-- The actual zero-side allowance is nonnegative at positive Gaussian
scale; all multiplicities in the tail are nonnegative. -/
theorem allowance_nonneg {b : ℝ} (hb : 0 < b) (H : ℝ) : 0 ≤ allowance b H := by
  have htail : 0 ≤ divisorTail H := by
    apply tsum_nonneg
    intro ρ
    split_ifs <;> positivity [divisorWeight_nonneg ρ]
  exact mul_nonneg (mul_nonneg (by norm_num) (integralCost_pos hb _ _).le) htail

/-- A single height rate controls every admissible Gaussian scale. The
constant comes from the unconditional xi-growth bound and is independent
of the scale, cutoff and evaluation ordinate. -/
theorem exists_uniform_allowance_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H b : ℝ), 1 ≤ H → zetaPoleReserveZeroMargin H ^ 2 ≤ b →
      b ≤ 1 → allowance b H ≤ K * (Real.log (H + 2) / Real.sqrt H) := by
  obtain ⟨C, hC, htail⟩ := exists_divisorTail_sqrt_bound
  let A := 86 * Real.exp (1 / 2) * Real.sqrt Real.pi
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨4 * A * (7625 / 792) * C, by positivity, ?_⟩
  intro H b hH hscale hb
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hbpos := (sq_pos_of_pos hm.1).trans_le hscale
  have hcost : integralCost (1 - 2 * zetaPoleReserveZeroMargin H) b
      (zetaPoleReserveZeroMargin H) ≤ A * (7625 / 792) * Real.log (H + 2) := by
    calc
      _ ≤ A / zetaPoleReserveZeroMargin H :=
        integralCost_le_inverse_margin hm.1 hm.2.le hscale hb
      _ = A * (1 / zetaPoleReserveZeroMargin H) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (inverse_margin_le_log hH) hA.le).trans_eq
        (by ring)
  have hlog : 0 ≤ Real.log (H + 2) := Real.log_nonneg (by linarith)
  have hcpos := (integralCost_pos hbpos (1 - 2 * zetaPoleReserveZeroMargin H)
    (zetaPoleReserveZeroMargin H)).le
  unfold allowance
  calc
    _ ≤ (4 * integralCost (1 - 2 * zetaPoleReserveZeroMargin H) b
        (zetaPoleReserveZeroMargin H)) * (C / Real.sqrt H) :=
      mul_le_mul_of_nonneg_left (htail H hH) (by positivity)
    _ ≤ (4 * (A * (7625 / 792) * Real.log (H + 2))) * (C / Real.sqrt H) := by
      gcongr
    _ = _ := by ring

/-- The common height rate tends to zero, independently of any chosen
Gaussian family. -/
theorem tendsto_log_shift_div_sqrt :
    Tendsto (fun H : ℝ => Real.log (H + 2) / Real.sqrt H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log H / Real.sqrt H) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun H : ℝ => (Real.sqrt H)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hupper : Tendsto (fun H : ℝ => Real.log 3 / Real.sqrt H +
      Real.log H / Real.sqrt H) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using
      (hinv.const_mul (Real.log 3)).add hlog
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg H)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hHpos : 0 < H := by linarith
    have hlogle : Real.log (H + 2) ≤ Real.log 3 + Real.log H := by
      calc
        _ ≤ Real.log (3 * H) := Real.log_le_log (by positivity) (by linarith)
        _ = _ := Real.log_mul (by norm_num) hHpos.ne'
    simpa only [add_div] using div_le_div_of_nonneg_right hlogle (Real.sqrt_nonneg H)

/-- The rate vanishes uniformly over all admissible scales, without
selecting a family of coefficients or one Gaussian sequence. -/
theorem eventually_allowance_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ b : ℝ, zetaPoleReserveZeroMargin H ^ 2 ≤ b → b ≤ 1 →
      allowance b H < ε := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_allowance_bound
  have hlim : Tendsto (fun H : ℝ => K * (Real.log (H + 2) / Real.sqrt H))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_log_shift_div_sqrt.const_mul K
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_lt_const hε] with H hH hsmall
  intro b hscale hb
  exact (hbound H b hH hscale hb).trans_lt hsmall

/-- Every moving Gaussian scale within the proved admissible range has
vanishing full allowance. No continuity or regularity of that choice is
needed. -/
theorem tendsto_allowance_of_admissible (b : ℝ → ℝ)
    (hscale : ∀ᶠ H : ℝ in atTop, zetaPoleReserveZeroMargin H ^ 2 ≤ b H ∧ b H ≤ 1) :
    Tendsto (fun H : ℝ => allowance (b H) H) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_allowance_bound
  have hlim : Tendsto (fun H : ℝ => K * (Real.log (H + 2) / Real.sqrt H))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_log_shift_div_sqrt.const_mul K
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hscale] with H hH
    exact allowance_nonneg
      ((sq_pos_of_pos (zetaPoleReserveZeroMargin_bounds H).1).trans_le hH.1) H
  · filter_upwards [hscale, eventually_ge_atTop (1 : ℝ)] with H hscaleH hH
    exact hbound H (b H) hH hscaleH.1 hscaleH.2

private theorem allowance_eq (b H : ℝ) :
    allowance b H = 4 * integralCost (2 * (1 - zetaPoleReserveZeroMargin H) - 1) b
      (1 - (1 - zetaPoleReserveZeroMargin H)) * divisorTail H := by
  unfold allowance
  rw [show 2 * (1 - zetaPoleReserveZeroMargin H) - 1 =
    1 - 2 * zetaPoleReserveZeroMargin H by ring,
    show 1 - (1 - zetaPoleReserveZeroMargin H) = zetaPoleReserveZeroMargin H by ring]

/-- The signed outside-band sum and the full zero side are controlled by
one common vanishing rate, uniformly in the evaluation ordinate and in
all admissible Gaussian scales. Every analytic multiplicity is included. -/
theorem exists_uniform_zero_side_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H b t : ℝ), 1 ≤ H → zetaPoleReserveZeroMargin H ^ 2 ≤ b →
      b ≤ 1 → 2 * |t| ≤ H →
      |∑' ρ : NontrivialZetaZero, outside b (1 - zetaPoleReserveZeroMargin H) t H ρ| ≤
        K * (Real.log (H + 2) / Real.sqrt H) ∧
      -(K * (Real.log (H + 2) / Real.sqrt H)) ≤
        ∑' ρ : NontrivialZetaZero, contribution b (1 - zetaPoleReserveZeroMargin H) t ρ := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_allowance_bound
  refine ⟨K, hK, ?_⟩
  intro H b t hH hscale hb ht
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hbpos := (sq_pos_of_pos hm.1).trans_le hscale
  have hσ0 : 1 / 2 ≤ 1 - zetaPoleReserveZeroMargin H := by linarith [hm.2]
  have hσ1 : 1 - zetaPoleReserveZeroMargin H ≤ 1 := by linarith [hm.1]
  have hscale' : (1 - (1 - zetaPoleReserveZeroMargin H)) ^ 2 ≤ b := by
    simpa only [sub_sub_cancel] using hscale
  have hboundH := hbound H b hH hscale hb
  rw [allowance_eq] at hboundH
  exact ⟨(abs_tsum_outside_le hbpos hσ0 hσ1 hscale' ht hH).trans hboundH,
    (neg_le_neg hboundH).trans (global_zero_side_lower_bound hbpos ht hH hscale)⟩

/-- Uniformly for all admissible Gaussian scales and all ordinates in
the half-height band, the actual global zero side eventually exceeds any
fixed negative tolerance. -/
theorem eventually_zero_side_ge_neg {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ b t : ℝ, zetaPoleReserveZeroMargin H ^ 2 ≤ b → b ≤ 1 →
      2 * |t| ≤ H → -ε ≤
        ∑' ρ : NontrivialZetaZero, contribution b (1 - zetaPoleReserveZeroMargin H) t ρ := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_zero_side_bound
  have hlim : Tendsto (fun H : ℝ => K * (Real.log (H + 2) / Real.sqrt H))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_log_shift_div_sqrt.const_mul K
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_lt_const hε] with H hH hsmall
  intro b t hscale hb ht
  exact (neg_le_neg hsmall.le).trans (hbound H b t hH hscale hb ht).2

end
end RiemannGaussian.GaussianFermiMovingAllowance
