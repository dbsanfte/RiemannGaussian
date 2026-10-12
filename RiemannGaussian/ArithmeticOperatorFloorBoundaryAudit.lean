/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorSourceAudit
import RiemannGaussian.ArithmeticOperatorFactorialUniqueness

/-!
# Physical lower boundary does not restore the linear floor source

The exact full transform vanishes at a hypothetical zero. Truncating the
physical scale to positive logarithms leaves a uniformly bounded response,
not a power-size source. This is a diagnostic smooth-mode no-go; it is not
an estimate for a literal twisted Mangoldt packet. Exact factorial data
still determine the actual Mangoldt sequence, as proved separately.
-/

namespace RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit
noncomputable section
open Complex MeasureTheory Set Filter
open ArithmeticOperatorFloorSourceAudit
open scoped Topology

/-- The complete physical positive-scale observation of one power mode.
The finite cutoff boundary is kept, not completed and silently discarded. -/
def truncatedResponse (s : ℂ) (T : ℝ) : ℂ :=
  Complex.exp (s*T)*∫ t in Iic T,
    Complex.exp (-s*t)*(centeredFloor t : ℂ)

/-- The ordinary floor-error tail has an exact exponential majorant. -/
theorem norm_floor_tail_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) (T : ℝ) :
    ‖∫ t in Ioi T, Complex.exp (-s*t)*(centeredFloor t : ℂ)‖ ≤
      Real.exp (-s.re*T)/s.re := by
  have hi := (integrable_floorTransform hs hs1).integrableOn (s := Ioi T)
  have hb := integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) T
  calc
    _ ≤ ∫ t in Ioi T, ‖Complex.exp (-s*t)*(centeredFloor t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, Real.exp (-s.re*t) := by
      apply integral_mono_ae hi.norm hb
      filter_upwards with t
      rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
      have he : (-s*(t : ℂ)).re = -s.re*t := by simp
      rw [he]
      exact (mul_le_mul_of_nonneg_left (centeredFloor_abs_le_one t)
        (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = _ := by rw [integral_exp_mul_Ioi (by linarith : -s.re < 0) T]; ring

/-- The retained lower physical boundary is O(1), uniformly in the
cutoff, at every hypothetical critical-strip zeta zero. It cannot create
the missing exponential/power source of a linear Gamma observation. -/
theorem norm_truncatedResponse_le_of_zeta_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta s = 0) (T : ℝ) :
    ‖truncatedResponse s T‖ ≤ 1/s.re := by
  have hi := integrable_floorTransform hs hs1
  have he := integral_add_compl (s := Iic T) measurableSet_Iic hi
  rw [compl_Iic] at he
  change (∫ t in Iic T, Complex.exp (-s*t)*(centeredFloor t : ℂ))+
    (∫ t in Ioi T, Complex.exp (-s*t)*(centeredFloor t : ℂ)) = floorTransform s at he
  rw [floorTransform_zero_at_zeta_zero hs hs1 hz] at he
  have hh := eq_neg_of_add_eq_zero_left he
  unfold truncatedResponse
  rw [hh,norm_mul,norm_neg,Complex.norm_exp]
  have hre : (s*(T : ℂ)).re = s.re*T := by simp
  rw [hre]
  calc
    _ ≤ Real.exp (s.re*T)*(Real.exp (-s.re*T)/s.re) :=
      mul_le_mul_of_nonneg_left (norm_floor_tail_le hs hs1 T) (Real.exp_pos _).le
    _ = 1/s.re := by
      rw [← mul_div_assoc,← Real.exp_add]
      ring_nf
      rw [Real.exp_zero,one_mul]

/-- Even after the physical boundary is retained, the response divided
by any positive exponential tends to zero. No source-carrying boundary
has been hidden in the full-line Mellin identity. -/
theorem tendsto_scaled_truncatedResponse {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ => (Real.exp (-a*T) : ℂ)*truncatedResponse s T)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => Real.exp (-a*T)*(1/s.re)) atTop (𝓝 0) := by
    have hn : Tendsto (fun T : ℝ => -a*T) atTop atBot := by
      simpa only [Function.comp_def,id_eq] using
        tendsto_const_nhds.neg_mul_atTop (by linarith : -a < 0) tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp hn).mul_const (1/s.re)
  apply squeeze_zero_norm (fun T => ?_) ht
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_truncatedResponse_le_of_zeta_zero hs hs1 hz T)
    (Real.exp_pos _).le

end
end RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit
