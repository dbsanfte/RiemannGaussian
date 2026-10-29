/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicHermiteReportPolynomial
import RiemannGaussian.SemiprimePublicResourceRate

/-! # Subpower growth of the actual physical-Hermite caller report
The new implementation has its own original-resource cost proof. Only numerical
schedule estimates are reused from earlier work. Source/scalar control, memory
and final conversion still require the complete primitive-bit execution join.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeHermiteFullReportRate
open Filter
open SemiprimeScheduledFactorExecution SemiprimeMacroParameters

/-- Every positive input power eventually bounds the actual NEW caller report.
This is not yet a theorem identifying that ledger with whole-machine bit time. -/
theorem run_report_subpower (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      ((SemiprimeHermiteBitsScheduledController.run N).work : ℝ)≤(N:ℝ)^ε := by
  obtain ⟨C,k,hpoly⟩ := SemiprimePublicHermiteReportPolynomial.controllerEnvelope_monomial
  have hr := SemiprimePublicResourceRate.polynomial_subpower C k ε hε
  filter_upwards [hr,eventually_fastGuard,eventually_gt_atTop 0] with N hr hg hN
  let _ : NeZero (groups N) := ⟨Nat.ne_of_gt (guard_groups_pos N hg)⟩
  have hw := (SemiprimePublicHermiteReportPolynomial.run_work N hN hg).trans
    (hpoly (SemiprimePublicReportPolynomial.resources N))
  exact (show ((SemiprimeHermiteBitsScheduledController.run N).work : ℝ)≤
      ((C*(SemiprimePublicReportPolynomial.resources N+1)^k : ℕ) : ℝ) by exact_mod_cast hw).trans hr

/-- The actual physical-Hermite report in particular has eventual sixth-power
scaling; the original-input primitive-memory clock remains a separate obligation. -/
theorem run_report_sixth :
    ∀ᶠ N : ℕ in atTop,
      ((SemiprimeHermiteBitsScheduledController.run N).work : ℝ)≤(N:ℝ)^(1/6:ℝ) :=
  run_report_subpower (1/6) (by norm_num)

end RiemannGaussian.SemiprimeHermiteFullReportRate
