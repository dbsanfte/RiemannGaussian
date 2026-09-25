/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityInsertionPoisson

/-!
# A moving-cutoff compensated insertion estimate

The reciprocal-density jump process is written in the already-proved
fixed-cutoff coordinate; scaling its gap scales the largest allowed jump.
This bounds the supported insertion process. Identifying it with a
multimode arithmetic packet is a separate obligation.
-/

namespace RiemannGaussian.ZetaRieszMovingInsertion
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszParityInsertionPoisson

/-- The physical threshold p>(N+1)^16 on the lower core edge. -/
def physicalShare (N : ℕ) : ℝ := (320/39)*Real.log ((N : ℝ)+1)/N

theorem physicalShare_pos {N : ℕ} (hN : 0 < N) : 0 < physicalShare N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) hNR

/-- Convexity gives a uniform compensated jump-moment bound at any
nonnegative tilt, not just the previous frozen tilt two. -/
theorem jumpMoment_sub_mass_tilt {a b : ℝ} (ha : 0 < a) (har : a ≤ cutoff)
    (hb : 0 ≤ b) : jumpMoment a (b/cutoff)-jumpMass a ≤ Real.exp b-1 := by
  have he1 : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hcut : (0 : ℝ) < cutoff := by norm_num [cutoff]
  have hbound : ∀ x ∈ Ioc a cutoff,
      x⁻¹*(Real.exp ((b/cutoff)*x)-1) ≤ (Real.exp b-1)/cutoff := by
    intro x hx
    have hx0 : 0 < x := ha.trans hx.1
    have hratio : 0 ≤ x/cutoff ∧ x/cutoff ≤ 1 :=
      ⟨div_nonneg hx0.le hcut.le, (div_le_one hcut).mpr hx.2⟩
    have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ b)
      (by linarith : 0 ≤ 1-x/cutoff) hratio.1 (by ring : 1-x/cutoff+x/cutoff = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have hh : Real.exp ((b/cutoff)*x)-1 ≤ (x/cutoff)*(Real.exp b-1) := by
      rw [show (b/cutoff)*x = x/cutoff*b by ring]
      linarith
    calc
      _ ≤ x⁻¹*((x/cutoff)*(Real.exp b-1)) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hx0.le)
      _ = _ := by field_simp
  have hint : IntegrableOn (fun x : ℝ => x⁻¹*(Real.exp ((b/cutoff)*x)-1)) (Ioc a cutoff) := by
    apply ((integrable_jumpMoment ha (b/cutoff)).sub (integrable_density ha)).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  calc
    _ = ∫ x in Ioc a cutoff, x⁻¹*(Real.exp ((b/cutoff)*x)-1) := by
      rw [show (fun x : ℝ => x⁻¹*(Real.exp ((b/cutoff)*x)-1)) =
        (fun x => x⁻¹*Real.exp ((b/cutoff)*x)-x⁻¹) by ext; ring]
      rw [integral_sub (integrable_jumpMoment ha _) (integrable_density ha)]
      rfl
    _ ≤ ∫ _x in Ioc a cutoff, (Real.exp b-1)/cutoff := by
      apply integral_mono_ae hint (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hbound x hx
    _ = (cutoff-a)*((Real.exp b-1)/cutoff) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le har]
    _ ≤ Real.exp b-1 := by
      apply (mul_le_mul_of_nonneg_right (sub_le_self cutoff ha.le)
        (div_nonneg (by linarith) hcut.le)).trans_eq
      field_simp

/-- The scaled support gap for a jump cutoff tending to zero. The
auxiliary lower endpoint is still positive and is not silently removed. -/
def movingInsertion (N : ℕ) (a g : ℝ) : ℝ :=
  supportInsertionSum a (g*cutoff/physicalShare N)

theorem movingInsertion_exp_bound {N : ℕ} (hN : 100000 ≤ N) {a g : ℝ}
    (ha : 0 < a) (har : a ≤ cutoff) (hg : (7/25 : ℝ) ≤ g) :
    0 ≤ movingInsertion N a g ∧ movingInsertion N a g ≤ Real.exp (-(N : ℝ)/100) := by
  have hNR : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log ((N : ℝ)+1) := Real.log_pos (by linarith)
  let b : ℝ := Real.log ((N : ℝ)+1)/2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcut : (0 : ℝ) < cutoff := by norm_num [cutoff]
  have hbound := supportInsertionSum_bounds ha (div_nonneg hb hcut.le)
    (g*cutoff/physicalShare N)
  have hmoment := jumpMoment_sub_mass_tilt ha har hb
  have hexp : Real.exp b ≤ (N : ℝ)/200 := by
    have he : Real.exp b^2 = (N : ℝ)+1 := by
      rw [show Real.exp b^2 = Real.exp (b+b) by rw [Real.exp_add, pow_two]]
      dsimp [b]
      rw [show Real.log ((N : ℝ)+1)/2+Real.log ((N : ℝ)+1)/2 =
        Real.log ((N : ℝ)+1) by ring, Real.exp_log (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ)-100000), Real.exp_pos b]
  have hr : (b/cutoff)*(g*cutoff/physicalShare N) = (39/640 : ℝ)*N*g := by
    dsimp [b, physicalShare]
    field_simp
    ring
  have hrate : jumpMoment a (b/cutoff)-jumpMass a-
      (b/cutoff)*(g*cutoff/physicalShare N) ≤ -(N : ℝ)/100 := by
    rw [hr]
    nlinarith
  exact ⟨hbound.1, hbound.2.trans (Real.exp_le_exp.mpr hrate)⟩

end
end RiemannGaussian.ZetaRieszMovingInsertion
