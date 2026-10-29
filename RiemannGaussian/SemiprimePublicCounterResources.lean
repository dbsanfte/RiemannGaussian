/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicCounterBudget
import RiemannGaussian.SemiprimeMaterializedRate

/-! # Closed exponential resources of the actual public counter
Only parameter envelopes are compared to the established rate functions.
No default-layout identity or complete primitive machine clock is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace RiemannGaussian.SemiprimePublicCounterResources
open scoped BigOperators
open SemiprimePublicCounterBudget SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution SemiprimeCounterRate SemiprimeSourceLayoutRate
open SemiprimeMacroParameters SemiprimeMaterializedRate

/-- The literal closed floor-power envelope lies below the real rate envelope. -/
theorem closed_summary_le {n : ℕ} (hν : 64≤ Nat.clog 2 (Nat.clog 2 n)) :
    ((sourceSignatureBase n^
      (4*n/(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)):ℕ):ℝ)≤ summaryEnvelope n := by
  have hlog := SemiprimeIndexedDesignResources.summary_envelope_log hν
  have hp : (0:ℝ)<((sourceSignatureBase n^
      (4*n/(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)):ℕ):ℝ) := by
    exact_mod_cast (pow_pos (show 0< sourceSignatureBase n by unfold sourceSignatureBase; omega) _)
  apply (Real.log_le_iff_le_exp hp).mp
  convert hlog using 1
  dsimp [summaryEnvelope,decay]
  ring

/-- The actual public summary envelope is the closed indexed envelope above. -/
theorem summaryBound_le (N : ℕ) (hν : 64≤ Nat.clog 2 (Nat.clog 2 (wireCount N))) :
    (summaryBound N:ℝ)≤ summaryEnvelope (wireCount N) := by
  simpa only [summaryBound,groups,points,degree,lambda,sourceSignatureBase,sourceHeight,
    SemiprimeAcquiredSourceCounter.measurementBound] using closed_summary_le (n:=wireCount N) hν

/-- Rounding a balanced head costs at most the gap between 3/2 and 2,
provided the actual input has at least two coordinates per group. -/
theorem ceil_head_le {n r : ℕ} (hr : 0< r) (hnr : 2*r≤ n) :
    (⌈3*(n:ℚ)/(2*(r:ℚ))⌉₊:ℝ)≤2*(n:ℝ)/(r:ℝ) := by
  have hrq : (0:ℚ)< r := by exact_mod_cast hr
  have hnrq : 2*(r:ℚ)≤ n := by exact_mod_cast hnr
  have hc := Nat.ceil_lt_add_one (show (0:ℚ)≤3*(n:ℚ)/(2*(r:ℚ)) by positivity)
  have hm := mul_le_mul_of_nonneg_right (le_of_lt hc) (le_of_lt hrq)
  have he1 : (3*(n:ℚ)/(2*(r:ℚ)))*(2*(r:ℚ))=3*(n:ℚ) :=
    div_mul_cancel₀ _ (by positivity)
  have he2 : (2*(n:ℚ)/(r:ℚ))*(r:ℚ)=2*(n:ℚ) := div_mul_cancel₀ _ (ne_of_gt hrq)
  have hq : (⌈3*(n:ℚ)/(2*(r:ℚ))⌉₊:ℚ)≤2*(n:ℚ)/(r:ℚ) := by
    apply (le_div_iff₀ hrq).mpr
    nlinarith
  have hcR := (Rat.cast_le (K:=ℝ)).mpr hq
  simpa only [Rat.cast_natCast,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hcR

/-- The actual fast guard pays enough headroom for the ceiling. -/
theorem fast_headroom (N : ℕ) (hg : fastGuard N) : 2*groups N≤ wireCount N := by
  rcases hg with ⟨hn,hw,hr,hQ,hR,hs,he,heh,hl,hh,hwidth,hload⟩
  have hrr : groups N≤ groups N^2 := by nlinarith only [hr]
  calc
    2*groups N≤16*groups N^2 := by nlinarith only [hrr]
    _ ≤16*points N*groups N^2 := by gcongr; omega
    _ ≤ wireCount N := hh

/-- The literal native 2^H factor fits the known head envelope. -/
theorem headBound_le (N : ℕ) (hg : fastGuard N) :
    ((2:ℕ)^headBound N:ℝ)≤ headEnvelope (wireCount N) := by
  have hh := ceil_head_le (guard_groups_pos N hg) (fast_headroom N hg)
  change (headBound N:ℝ)≤2*(wireCount N:ℝ)/(groups N:ℝ) at hh
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hh (Real.log_nonneg (show (1:ℝ)≤2 by norm_num))
  simpa only [headEnvelope,groups,lambda,mul_comm] using hm

/-- Original growing arity, with the ACTUAL public wire count in the exponent. -/
theorem scopeBound_le (N : ℕ) (hN : 0< N) :
    ((2:ℕ)^scopeBound (bitLength N):ℝ)≤
      Real.exp (512*(wireCount N:ℝ)^(3/4:ℝ)*Real.log 2) := by
  have hs := scopeBound_le_variableCount_rpow (bitLength_pos hN)
  rw [← wireCount_eq N] at hs
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hs (Real.log_nonneg (show (1:ℝ)≤2 by norm_num))
  simpa only [mul_comm] using hm

/-- The actual finite precision uses exactly the established inclusive cutoff. -/
theorem supportCount_eq (N : ℕ) :
    SemiprimeCounterEnumeration.weightedCount (wireCount N) (precision N-1)=
      SemiprimeCounterEnumeration.weightedCount (wireCount N)
        (SemiprimeScheduledSupportRate.cutoff (wireCount N)) := by
  simp only [precision_formula,SemiprimeScheduledSupportRate.cutoff,Nat.add_sub_cancel]

end RiemannGaussian.SemiprimePublicCounterResources
