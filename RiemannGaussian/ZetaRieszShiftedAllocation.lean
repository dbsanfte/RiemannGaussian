/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedCenter
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import RiemannGaussian.ZetaRieszCascadeAbelAudit

/-!
# Arithmetic size of the per-leg correction

These are pointwise bounds for the exact product multiplier. They must not
be confused with an absolute source-normalized estimate for a packet.
-/

namespace RiemannGaussian.ZetaRieszShiftedCenter
noncomputable section
open Filter Topology
open scoped BigOperators Classical

theorem adaptive_order_le_four_log {N k : ℕ} {T : ℝ} (hN : 1 ≤ N)
    (hT : (39/20 : ℝ)*N < T) (p : ℕ)
    (hk : (k : ℝ) ≤ 2*((N : ℝ)+1)*Real.log p/T) :
    (k : ℝ) ≤ 4*Real.log p := by
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTp : 0 < T := by linarith
  have hlog := Real.log_natCast_nonneg p
  have hm : 2*((N : ℝ)+1) ≤ 4*T := by linarith
  exact hk.trans ((div_le_iff₀ hTp).mpr (by nlinarith))

/-- Raising the physical prime threshold gives an explicit polynomial
bound on each exact arithmetic correction. -/
theorem multiplier_error_polynomial {y : ℝ} (hy : 54 < |y|)
    (N k p : ℕ) (hp : (N+1)^16 < p) (hk : (k : ℝ) ≤ 4*Real.log p) :
    ‖ratio y^k/(p : ℂ)‖ ≤ 1/((N : ℝ)+1)^15 := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
  have hN0 : 0 < (N : ℝ)+1 := by positivity
  have hpn : ((N : ℝ)+1)^16 < p := by exact_mod_cast hp
  have hlog : 16*Real.log ((N : ℝ)+1) < Real.log p := by
    have h := Real.log_lt_log (by positivity) hpn
    rwa [Real.log_pow] at h
  have hnlog : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ Real.exp (-(99/100 : ℝ)*Real.log p) :=
      multiplier_error_le hy k p (by omega) hk
    _ ≤ Real.exp (-15*Real.log ((N : ℝ)+1)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      have he : Real.exp (15*Real.log ((N : ℝ)+1)) = ((N : ℝ)+1)^15 := by
        simpa only [Nat.cast_ofNat, Real.exp_log hN0] using
          Real.exp_nat_mul (Real.log ((N : ℝ)+1)) 15
      rw [neg_mul, Real.exp_neg, he, one_div]

/-- Telescoping the exact multipliers, with every allocated prime kept. -/
theorem product_multiplier_error {y : ℝ} (hy : 54 < |y|) (N : ℕ)
    (A : Finset ℕ) (k : ℕ → ℕ)
    (hp : ∀ p ∈ A, (N+1)^16 < p)
    (hk : ∀ p ∈ A, (k p : ℝ) ≤ 4*Real.log p) :
    ‖∏ p ∈ A, (1-ratio y^(k p)/(p : ℂ))-1‖ ≤
      Real.exp ((A.card : ℝ)/((N : ℝ)+1)^15)-1 := by
  have h := A.norm_prod_one_add_sub_one_le (fun p => -ratio y^(k p)/(p : ℂ))
  simp only [neg_div, ← sub_eq_add_neg, norm_neg] at h
  apply h.trans
  gcongr
  calc
    _ ≤ ∑ p ∈ A, 1/((N : ℝ)+1)^15 :=
      Finset.sum_le_sum (fun p hpA => multiplier_error_polynomial hy N (k p) p
        (hp p hpA) (hk p hpA))
    _ = _ := by simp; ring

theorem arithmetic_product_identity (A : Finset ℕ) (k : ℕ → ℕ) (u y : ℝ)
    (hp : ∀ p ∈ A, 0 < p) :
    (∏ p ∈ A, leg u y (k p) p) =
      (∏ p ∈ A, (1-ratio y^(k p)/(p : ℂ)))*
      (∏ p ∈ A, ((k p : ℂ)*(u : ℂ)^(k p)*zetaPrimeLogKernel (k p) (center y) p)) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p hpA => leg_eq_multiplier u y (k p) p (hp p hpA))

theorem product_multiplier_error_linear {y : ℝ} (hy : 54 < |y|) (N : ℕ)
    (A : Finset ℕ) (k : ℕ → ℕ)
    (hp : ∀ p ∈ A, (N+1)^16 < p)
    (hk : ∀ p ∈ A, (k p : ℝ) ≤ 4*Real.log p)
    (hc : (A.card : ℝ) ≤ 3*((N : ℝ)+1)) :
    ‖∏ p ∈ A, (1-ratio y^(k p)/(p : ℂ))-1‖ ≤
      Real.exp (3/((N : ℝ)+1)^14)-1 := by
  apply (product_multiplier_error hy N A k hp hk).trans
  have he : 3*((N : ℝ)+1)/((N : ℝ)+1)^15 = 3/((N : ℝ)+1)^14 := by
    rw [show (15 : ℕ) = 14+1 by omega, pow_succ]
    field_simp
  have hr := (div_le_div_of_nonneg_right hc (by positivity)).trans_eq he
  exact sub_le_sub_right (Real.exp_le_exp.mpr hr) 1

/-- The multiplier product really approaches one uniformly when the
factor count is at most linear. This is a relative arithmetic assertion. -/
theorem tendsto_product_multiplier_error_envelope :
    Tendsto (fun N : ℕ => Real.exp (3/((N : ℝ)+1)^14)-1) atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+1)^14) atTop atTop :=
    tendsto_pow_atTop (by norm_num) |>.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun N : ℕ => 3/((N : ℝ)+1)^14) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ht
  have hh := (Real.continuous_exp.continuousAt.tendsto.comp hsmall).sub_const 1
  simpa using hh

end
end RiemannGaussian.ZetaRieszShiftedCenter
