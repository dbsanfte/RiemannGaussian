/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalCallBounds
import RiemannGaussian.SemiprimeD1AuxiliaryRate

/-! # Original-input call count at the explicit quantitative target rate
The actual finite call inventory has a fixed-constant bound in original input
length, with the natural logarithm in the denominator and literal base two.
This counts recursive calls. Their complete primitive execution cost remains
a separate theorem; no call-count bound is substituted for a runtime bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalCallRate
open SemiprimeD1OriginalCallBounds SemiprimeD1OriginalStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1PackingReady
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
noncomputable section

/-- Main exponent scale of the actual original-size recursive controller. -/
def mainScale (s : ℕ) : ℝ := (s:ℝ)/Real.sqrt (logarithm s:ℕ)

/-- Requested exponent scale in ORIGINAL binary input length. -/
def inputScale (ell : ℕ) : ℝ := (ell:ℝ)/Real.sqrt (Real.log (ell+2:ℕ))

/-- The real input logarithm is dominated by the actual scaled integer logarithm. -/
theorem input_log_le (ell : ℕ) :
    Real.log (ell+2:ℕ) ≤ (logarithm (SemiprimeD1PublicPackingReady.scale ell):ℝ) := by
  have hell : ell ≤ SemiprimeD1PublicPackingReady.scale ell := by
    unfold SemiprimeD1PublicPackingReady.scale
    norm_num
    omega
  have hp : ell+2 ≤ 2^logarithm (SemiprimeD1PublicPackingReady.scale ell) :=
    (Nat.add_le_add_right hell 2).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  have hpR : (ell+2:ℕ) ≤ (2:ℝ)^logarithm (SemiprimeD1PublicPackingReady.scale ell) := by
    exact_mod_cast hp
  have hh := Real.log_le_log (show (0:ℝ) < (ell+2:ℕ) by positivity) hpR
  rw [Real.log_pow] at hh
  have htwo : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  exact hh.trans (by nlinarith [show (0:ℝ) ≤ logarithm (SemiprimeD1PublicPackingReady.scale ell) by positivity])

/-- The public linear scale changes only a fixed multiplicative constant,
without losing any additional power of the logarithm. -/
theorem mainScale_public (ell : ℕ) :
    mainScale (SemiprimeD1PublicPackingReady.scale ell) ≤ 1048576*inputScale ell := by
  have hlog : 0 < Real.log (ell+2:ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ell+2))
  have hroot := Real.sqrt_le_sqrt (input_log_le ell)
  have hdiv := div_le_div_of_nonneg_left (show (0:ℝ) ≤ ell by positivity)
    (Real.sqrt_pos.mpr hlog) hroot
  have hscale : (SemiprimeD1PublicPackingReady.scale ell:ℝ) = 1048576*(ell:ℝ) := by
    simp [SemiprimeD1PublicPackingReady.scale]
  unfold mainScale inputScale
  rw [hscale,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hdiv (by norm_num)

/-- Polynomial grid factors in the actual whole-tree envelope cost only16
additional units of the main exponent; all constants precede the family. -/
theorem count_envelope_le (s : ℕ)
    (haux : ((degreeCap s+(logarithm s+1)^3:ℕ):ℝ) ≤ 2*mainScale s) :
    (logarithm s+2:ℕ)*Real.exp (98304*mainScale s+
      (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) ≤ Real.exp (98320*mainScale s) := by
  let x : ℝ := logarithm s
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hc : x+1 ≤ (x+1)^3 := by nlinarith [sq_nonneg x]
  have hpref : (logarithm s+2:ℕ) ≤ Real.exp ((x+1)^3) := by
    have he := Real.add_one_le_exp (x+1)
    have hexp := Real.exp_le_exp.mpr hc
    push_cast
    dsimp only [x] at he hc hexp ⊢
    linarith
  have hsmall : (x+1)^3 ≤ 2*mainScale s := by
    push_cast at haux
    dsimp only [x]
    linarith [show (0:ℝ) ≤ degreeCap s by positivity]
  have hquad : (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ) ≤ 7*(x+1)^3 := by
    push_cast
    dsimp only [x]
    nlinarith [show (0:ℝ) ≤ (logarithm s:ℝ)^3 by positivity]
  calc
    _ ≤ Real.exp ((x+1)^3)*Real.exp (98304*mainScale s+
        (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp ((x+1)^3+98304*mainScale s+
        (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Elementary fixed-base conversion, with the lower bound log2≥1/2 proved. -/
theorem exp_le_two_rpow (x : ℝ) (hx : 0 ≤ x) : Real.exp x ≤ (2:ℝ)^(2*x) := by
  have hlog : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Fixed original-input constant for the CALL COUNT, not the full runtime. -/
def callConstant : ℕ := 2*98320*1048576

/-- CLOSED actual original-input whole-call-family bound at the requested
functional rate. Every root parameter and every branching choice is acquired
by the actual program. Per-call bit work is explicitly outside this theorem. -/
theorem eventually_original_call_rate : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N) × Bool)) (fuel : ℕ),
        (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ) ≤
          (2:ℝ)^((callConstant:ℝ)*(ell:ℝ)/Real.sqrt (Real.log (ell+2:ℕ))) := by
  filter_upwards [eventually_original_count,
    scale_tendsto.eventually SemiprimeD1AuxiliaryRate.eventually_auxiliary_rate] with ell hcount haux
  intro N hN hEll fixed fuel
  have hfirst := hcount N hN hEll fixed fuel
  have haux' : ((degreeCap (SemiprimeD1PublicPackingReady.scale ell)+
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1)^3:ℕ):ℝ) ≤
      2*mainScale (SemiprimeD1PublicPackingReady.scale ell) := by
    simpa only [mainScale,mul_div_assoc] using haux
  have henv := count_envelope_le (SemiprimeD1PublicPackingReady.scale ell) haux'
  have hscale := mainScale_public ell
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 98320))
  have hpow := exp_le_two_rpow (98320*(1048576*inputScale ell)) (by unfold inputScale;positivity)
  have hfirst' : (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ) ≤
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+2:ℕ)*Real.exp
        (98304*mainScale (SemiprimeD1PublicPackingReady.scale ell)+
          (((4*logarithm (SemiprimeD1PublicPackingReady.scale ell)+7)*
            (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1):ℕ):ℝ)) := by
    simpa only [mainScale,mul_div_assoc] using hfirst
  refine hfirst'.trans (henv.trans (he.trans (hpow.trans_eq ?_)))
  congr 1
  unfold callConstant inputScale
  push_cast
  ring

end
end RiemannGaussian.SemiprimeD1OriginalCallRate
