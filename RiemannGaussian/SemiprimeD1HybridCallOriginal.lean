/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridCallTree
import RiemannGaussian.SemiprimeD1OriginalCallRate

/-! # Improved call count for every actual original input and prescription
The exact leading natural-exponential coefficient is 393216/7. The unchanged
auxiliary reserve adds sixteen and rounds upward to 56190. These are call
counts for the original controller, not primitive bit-time bounds.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridCallOriginal
open SemiprimeD1OriginalCallRate SemiprimeD1OriginalCallBounds
open SemiprimeD1OriginalStateResources SemiprimeD1RootStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1PackingReady
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
noncomputable section

/-- The actual all-input root caller inherits the complete finite-fuel call
bound without any supplied branching, degree, precision or packing answers. -/
theorem eventually_original_count : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N) × Bool)) (fuel : ℕ),
        (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ) ≤
          (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+2:ℕ)*
            Real.exp ((393216/7:ℝ)*(SemiprimeD1PublicPackingReady.scale ell:ℝ)/
              Real.sqrt (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell):ℕ)+
              (((4*SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+7)*
                (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+1):ℕ):ℝ)) := by
  filter_upwards [scale_tendsto.eventually SemiprimeD1HybridCallTree.eventually_count_le] with ell hcount
  intro N hN hEll fixed fuel
  subst ell
  have hs := original_shape N hN fixed
  exact hcount (originalCall N hN fixed) fuel rfl (root_edges_le_scale N hN fixed)
    hs.2.2.2 hs.1 hs.2.1 hs.2.2.1 (root_global_degree N hN fixed)

/-- Polynomial grid factors in the actual whole-tree envelope cost only16
additional units of the main exponent; all constants precede the family. -/
theorem count_envelope_le (s : ℕ)
    (haux : ((degreeCap s+(logarithm s+1)^3:ℕ):ℝ) ≤ 2*mainScale s) :
    (logarithm s+2:ℕ)*Real.exp ((393216/7:ℝ)*mainScale s+
      (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) ≤ Real.exp (56190*mainScale s) := by
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
    _ ≤ Real.exp ((x+1)^3)*Real.exp ((393216/7:ℝ)*mainScale s+
        (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp ((x+1)^3+(393216/7:ℝ)*mainScale s+
        (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ)) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Fixed original-input constant for the CALL COUNT, not the full runtime. -/
def callConstant : ℕ := 2*56190*1048576

/-- The rounded coefficient is strictly below the original call-count constant. -/
theorem callConstant_lt_original : callConstant < SemiprimeD1OriginalCallRate.callConstant := by
  norm_num [callConstant,SemiprimeD1OriginalCallRate.callConstant]

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
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 56190))
  have hpow := exp_le_two_rpow (56190*(1048576*inputScale ell)) (by unfold inputScale;positivity)
  have hfirst' : (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ) ≤
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+2:ℕ)*Real.exp
        ((393216/7:ℝ)*mainScale (SemiprimeD1PublicPackingReady.scale ell)+
          (((4*logarithm (SemiprimeD1PublicPackingReady.scale ell)+7)*
            (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1):ℕ):ℝ)) := by
    simpa only [mainScale,mul_div_assoc] using hfirst
  refine hfirst'.trans (henv.trans (he.trans (hpow.trans_eq ?_)))
  congr 1
  unfold callConstant inputScale
  push_cast
  ring

end
end RiemannGaussian.SemiprimeD1HybridCallOriginal
