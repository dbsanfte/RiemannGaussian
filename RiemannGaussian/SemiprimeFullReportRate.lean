/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicReportGrowth
import RiemannGaussian.SemiprimePublicCounterResources

/-! # Subpower growth of the actual retained execution report
The conclusion concerns the concrete FullSetupScheduledController.run.work
ledger. Scalar source/encoding/native arithmetic, graph/schedule acquisition
and finite-memory refinements still prevent identifying it with a complete
primitive-bit clock. This is not a theorem of achieved whole-machine bit time.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace RiemannGaussian.SemiprimeFullReportRate
open Filter
open SemiprimePublicReportPolynomial SemiprimeScheduledScalarBudget
open SemiprimePublicCounterResources SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution SemiprimeMacroParameters

/-- All actual resources fit one instance of the established rate envelope,
using the concrete polynomial scalar bound and the actual exponential bounds. -/
theorem resources_le (N : ℕ) (hN : 0<N) (hg : fastGuard N)
    (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 (wireCount N)))
    (C d : ℕ) (hpoly : ∀ s, scalarEnvelope s ≤ C*(s+1)^d) :
    (resources N : ℝ) ≤ ((C*2^d+1 : ℕ) : ℝ)*
      SemiprimeMaterializedRate.budget d (wireCount N) := by
  have hn : 0<wireCount N := hg.1
  have hs : scalarResources N ≤ (C*2^d)*(wireCount N)^d := by
    calc
      scalarResources N ≤ scalarEnvelope (wireCount N) := scalarResources_le N hN hg
      _ ≤ C*(wireCount N+1)^d := hpoly _
      _ ≤ C*(2*wireCount N)^d :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)
      _ = _ := by rw [mul_pow]; ring
  have hsR : (scalarResources N : ℝ) ≤ ((C*2^d : ℕ) : ℝ)*(wireCount N : ℝ)^d := by
    exact_mod_cast hs
  have hy := summaryBound_le N hν
  have hh := headBound_le N hg
  have hw := scopeBound_le N hN
  norm_num only [Nat.cast_ofNat] at hh hw
  have hn0 : (0:ℝ) ≤ (wireCount N : ℝ)^d := by positivity
  have hrest0 : (0:ℝ) ≤
      (SemiprimeCounterEnumeration.weightedCount (wireCount N)
        (SemiprimeScheduledSupportRate.cutoff (wireCount N)) : ℝ)+
      SemiprimeMaterializedRate.summaryEnvelope (wireCount N)+
      SemiprimeMaterializedRate.headEnvelope (wireCount N)+
      Real.exp (512*(wireCount N : ℝ)^(3/4:ℝ)*Real.log 2) := by
    unfold SemiprimeMaterializedRate.summaryEnvelope SemiprimeMaterializedRate.headEnvelope
    positivity
  have hb : (wireCount N : ℝ)^d ≤ SemiprimeMaterializedRate.budget d (wireCount N) := by
    unfold SemiprimeMaterializedRate.budget
    linarith
  have he :
      (SemiprimePublicCounterBudget.summaryBound N : ℝ)+
      (SemiprimeCounterEnumeration.weightedCount (wireCount N) (precision N-1) : ℝ)+
      ((2:ℕ)^scopeBound (bitLength N) : ℝ)+
      ((2:ℕ)^SemiprimePublicCounterBudget.headBound N : ℝ) ≤
        SemiprimeMaterializedRate.budget d (wireCount N) := by
    rw [supportCount_eq]
    unfold SemiprimeMaterializedRate.budget
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsB := hsR.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (C*2^d)))
  calc
    (resources N : ℝ) =
        (scalarResources N : ℝ)+
        ((SemiprimePublicCounterBudget.summaryBound N : ℝ)+
          (SemiprimeCounterEnumeration.weightedCount (wireCount N) (precision N-1) : ℝ)+
          ((2:ℕ)^scopeBound (bitLength N) : ℝ)+
          ((2:ℕ)^SemiprimePublicCounterBudget.headBound N : ℝ)) := by
      simp only [resources,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ ((C*2^d : ℕ) : ℝ)*SemiprimeMaterializedRate.budget d (wireCount N)+
        SemiprimeMaterializedRate.budget d (wireCount N) := add_le_add hsB he
    _ = _ := by push_cast; ring

/-- The actual report is bounded by a fixed polynomial of the common rate
envelope, with both coefficients and exponents independent of N. -/
theorem run_le_rate_budget (N : ℕ) (hN : 0<N) (hg : fastGuard N)
    [NeZero (groups N)] (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 (wireCount N)))
    (Cs d Cw k : ℕ) (hs : ∀ s, scalarEnvelope s ≤ Cs*(s+1)^d)
    (hw : ∀ s, controllerEnvelope s ≤ Cw*(s+1)^k) :
    ((SemiprimeFullSetupScheduledController.run N).work : ℝ) ≤
      ((Cw*(Cs*2^d+2)^k : ℕ) : ℝ)*
        (SemiprimeMaterializedRate.budget d (wireCount N))^k := by
  have hr := resources_le N hN hg hν Cs d hs
  have hn : (1:ℝ) ≤ wireCount N := by exact_mod_cast hg.1
  have hp : (1:ℝ) ≤ (wireCount N : ℝ)^d := one_le_pow₀ hn
  have hb : (1:ℝ) ≤ SemiprimeMaterializedRate.budget d (wireCount N) := by
    unfold SemiprimeMaterializedRate.budget
    have hy : (0:ℝ) ≤ SemiprimeMaterializedRate.summaryEnvelope (wireCount N) := by
      unfold SemiprimeMaterializedRate.summaryEnvelope; positivity
    have hh : (0:ℝ) ≤ SemiprimeMaterializedRate.headEnvelope (wireCount N) := by
      unfold SemiprimeMaterializedRate.headEnvelope; positivity
    have he := Real.exp_pos (512*(wireCount N : ℝ)^(3/4:ℝ)*Real.log 2)
    have hc : (0:ℝ) ≤ SemiprimeCounterEnumeration.weightedCount (wireCount N)
        (SemiprimeScheduledSupportRate.cutoff (wireCount N)) := Nat.cast_nonneg _
    linarith
  have hr1 : (resources N : ℝ)+1 ≤ ((Cs*2^d+2 : ℕ) : ℝ)*
      SemiprimeMaterializedRate.budget d (wireCount N) := by
    push_cast at hr ⊢
    nlinarith
  have hc := (SemiprimePublicReportPolynomial.run_work N hN hg).trans (hw (resources N))
  have hcR : ((SemiprimeFullSetupScheduledController.run N).work : ℝ) ≤
      (Cw : ℝ)*((resources N : ℝ)+1)^k := by exact_mod_cast hc
  calc
    ((SemiprimeFullSetupScheduledController.run N).work : ℝ) ≤
        (Cw : ℝ)*((resources N : ℝ)+1)^k := hcR
    _ ≤ (Cw : ℝ)*(((Cs*2^d+2 : ℕ) : ℝ)*
        SemiprimeMaterializedRate.budget d (wireCount N))^k := by gcongr
    _ = _ := by rw [mul_pow]; push_cast; ring

/-- Actual public wire counts tend to infinity with the original input. -/
theorem wireCount_atTop : Tendsto wireCount atTop atTop := by
  have he : wireCount = variableCount ∘ Nat.size := by
    funext N
    exact wireCount_eq N
  rw [he]
  exact SemiprimeMaterializedRate.public_size_atTop.comp SemiprimeMaterializedRate.size_atTop

/-- The literal logarithmic threshold needed by the closed summary envelope
holds eventually for the actual public input schedule. -/
theorem eventually_summary_threshold :
    ∀ᶠ N : ℕ in atTop, 64 ≤ Nat.clog 2 (Nat.clog 2 (wireCount N)) := by
  exact ((SemiprimeCounterRate.tendsto_clog_two_atTop.comp
    SemiprimeCounterRate.tendsto_clog_two_atTop).comp wireCount_atTop).eventually
      (eventually_ge_atTop 64)

/-- Every positive input power eventually bounds the ACTUAL retained report.
This conclusion is expressly about run.work, not a complete primitive bit clock. -/
theorem run_report_subpower (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      ((SemiprimeFullSetupScheduledController.run N).work : ℝ) ≤ (N : ℝ)^ε := by
  obtain ⟨Cs,d,hs⟩ := SemiprimePublicReportGrowth.scalar_monomial
  obtain ⟨Cw,k,hw⟩ := SemiprimePublicReportGrowth.controller_monomial
  have hrate := SemiprimeMaterializedRate.public_fixed_polynomial_subpower d 0 k
    ((Cw*(Cs*2^d+2)^k : ℕ) : ℝ) ε hε
  filter_upwards [hrate,eventually_fastGuard,eventually_gt_atTop 0,eventually_summary_threshold]
    with N hrate hg hN hν
  let _ : NeZero (groups N) := ⟨Nat.ne_of_gt (guard_groups_pos N hg)⟩
  apply (run_le_rate_budget N hN hg hν Cs d Cw k hs hw).trans
  simpa only [wireCount_eq,bitLength,pow_zero,mul_one] using hrate

/-- In particular, the concrete retained report has eventual sixth-power scaling;
the separate original-input primitive-bit refinement remains open. -/
theorem run_report_sixth :
    ∀ᶠ N : ℕ in atTop,
      ((SemiprimeFullSetupScheduledController.run N).work : ℝ) ≤ (N : ℝ)^(1/6:ℝ) :=
  run_report_subpower (1/6) (by norm_num)

end RiemannGaussian.SemiprimeFullReportRate
