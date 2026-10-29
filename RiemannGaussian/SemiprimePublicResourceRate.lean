/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullReportRate

/-! # Every fixed polynomial of the actual scheduled resources is subpower
Only the existing numerical resource estimate is reused here. No work report
is equated with another program or with a complete primitive-bit execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace RiemannGaussian.SemiprimePublicResourceRate
open Filter
open SemiprimePublicReportPolynomial SemiprimeScheduledScalarBudget
open SemiprimePublicAcquiredExecution SemiprimeScheduledFactorExecution SemiprimeMacroParameters

/-- The literal resource polynomial fits the established analytic schedule envelope. -/
theorem polynomial_le_rate_budget (N : ℕ) (hN : 0<N) (hg : fastGuard N)
    (hν : 64≤Nat.clog 2 (Nat.clog 2 (wireCount N)))
    (Cs d C k : ℕ) (hs : ∀ s,scalarEnvelope s≤Cs*(s+1)^d) :
    ((C*(resources N+1)^k : ℕ) : ℝ)≤
      ((C*(Cs*2^d+2)^k : ℕ) : ℝ)*(SemiprimeMaterializedRate.budget d (wireCount N))^k := by
  have hr := SemiprimeFullReportRate.resources_le N hN hg hν Cs d hs
  have hn : (1:ℝ)≤wireCount N := by exact_mod_cast hg.1
  have hp : (1:ℝ)≤(wireCount N : ℝ)^d := one_le_pow₀ hn
  have hb : (1:ℝ)≤SemiprimeMaterializedRate.budget d (wireCount N) := by
    have hrest : (0:ℝ)≤
        (SemiprimeCounterEnumeration.weightedCount (wireCount N)
          (SemiprimeScheduledSupportRate.cutoff (wireCount N)) : ℝ)+
        SemiprimeMaterializedRate.summaryEnvelope (wireCount N)+
        SemiprimeMaterializedRate.headEnvelope (wireCount N)+
        Real.exp (512*(wireCount N : ℝ)^(3/4:ℝ)*Real.log 2) := by
      unfold SemiprimeMaterializedRate.summaryEnvelope SemiprimeMaterializedRate.headEnvelope
      positivity
    unfold SemiprimeMaterializedRate.budget
    linarith
  have hr1 : (resources N : ℝ)+1≤((Cs*2^d+2 : ℕ) : ℝ)*
      SemiprimeMaterializedRate.budget d (wireCount N) := by
    push_cast at hr ⊢
    nlinarith
  calc
    ((C*(resources N+1)^k : ℕ) : ℝ)=(C:ℝ)*((resources N:ℝ)+1)^k := by push_cast; rfl
    _ ≤ (C:ℝ)*(((Cs*2^d+2 : ℕ) : ℝ)*
        SemiprimeMaterializedRate.budget d (wireCount N))^k := by gcongr
    _ = _ := by rw [mul_pow]; push_cast; ring

/-- Every fixed resource polynomial is eventually below every positive input power.
This is a resource estimate, available to any separately proved actual-cost join. -/
theorem polynomial_subpower (C k : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ((C*(resources N+1)^k : ℕ) : ℝ)≤(N:ℝ)^ε := by
  obtain ⟨Cs,d,hs⟩ := SemiprimePublicReportGrowth.scalar_monomial
  have hrate := SemiprimeMaterializedRate.public_fixed_polynomial_subpower d 0 k
    ((C*(Cs*2^d+2)^k : ℕ) : ℝ) ε hε
  filter_upwards [hrate,eventually_fastGuard,eventually_gt_atTop 0,
    SemiprimeFullReportRate.eventually_summary_threshold] with N hrate hg hN hν
  apply (polynomial_le_rate_budget N hN hg hν Cs d C k hs).trans
  simpa only [wireCount_eq,bitLength,pow_zero,mul_one] using hrate

end RiemannGaussian.SemiprimePublicResourceRate
