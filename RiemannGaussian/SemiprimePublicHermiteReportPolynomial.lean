/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicHermiteCounterBudget
import RiemannGaussian.SemiprimeHermiteReportEnvelope
import RiemannGaussian.SemiprimePublicReportPolynomial

/-! # Actual physical-Hermite controller bounded by public numeric resources
Only the old numerical resource sum is reused. No old/new clock equality is
assumed and the original source/entry/control model boundaries remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimePublicHermiteReportPolynomial
open scoped BigOperators
open SemiprimePublicHermiteCounterBudget SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution SemiprimeMacroParameters
open SemiprimePublicReportPolynomial (resources scalarResources)

/-- Uniform inflation pays the literal physical checker and constant overhead. -/
def inflation (S : ℕ) : ℕ := 10*(S+1)^2

/-- The complete actual counter is bounded by the new physical diagonal. -/
def countEnvelope (S : ℕ) : ℕ :=
  SemiprimeHermiteReportEnvelope.polynomialEnvelope (inflation S)

/-- Every original public resource is included before the fixed polynomial is applied. -/
theorem counterBudget_le (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    counterBudget N hN ≤ countEnvelope (resources N) := by
  let S := resources N
  let T := inflation S
  have hscalar :
      wireCount N ≤ S ∧ factorCount N ≤ S ∧ 2*wireCount N ≤ S ∧ groups N ≤ S ∧
      points N ≤ S ∧ degree N ≤ S ∧ 2 ≤ S ∧ precision N ≤ S ∧
      SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N) ≤ S ∧
      scopeBound (bitLength N) ≤ S ∧ headBound N ≤ S ∧ 4*wireCount N ≤ S ∧
      (groups N)^(2*points N) ≤ S ∧ (groups N)^(points N) ≤ S ∧
      summaryBound N ≤ S ∧
      SemiprimeCounterEnumeration.weightedCount (wireCount N) (precision N-1) ≤ S ∧
      2^(scopeBound (bitLength N)) ≤ S ∧ 2^(headBound N) ≤ S := by
    simp only [SemiprimePublicHermiteCounterBudget.headBound,SemiprimePublicHermiteCounterBudget.summaryBound]
    dsimp only [S]
    unfold resources scalarResources
    generalize (2:ℕ)^(scopeBound (bitLength N))=ew
    generalize (2:ℕ)^(headBound N)=eh
    omega
  rcases hscalar with ⟨hn,hF,hs,hr,hQ,hR,hB,hJ,hE,hw,hH,hM,hD,hA,hY,hCq,hEw,hEh⟩
  have hST : S ≤ T := by dsimp [T,inflation]; nlinarith
  have hentry : entryBound N ≤ T := by
    dsimp [entryBound,T,inflation]
    nlinarith
  have hd := actual_design_resources N hN hg
  have h := SemiprimeHermiteReportEnvelope.fullBudget_le_envelope
    (groups N) (degree N) 2 (precision N) (headBound N) (4*wireCount N)
    (scopeBound (bitLength N)) (entryBound N) (summaryBound N) T
    (indexedArity N)
    (SemiprimeHermiteBitsSetupBudget.designs (r:=groups N) (Q:=points N)
      (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2)
    (hn.trans hST) (hF.trans hST)
    (by rw [indexed_incidence_count N hN]; exact hs.trans hST)
    (hr.trans hST) (hQ.trans hST) (hR.trans hST) (hB.trans hST) (hJ.trans hST)
    (hH.trans hST) (hM.trans hST) (hw.trans hST) hentry (hY.trans hST)
    (hD.trans hST) (hA.trans hST)
    (fun a => (le_of_eq (hd.1 a)).trans (hr.trans hST)) hd.2.1 hd.2.2.1 hd.2.2.2
    (hCq.trans hST) (hEw.trans hST) (hEh.trans hST)
  simpa only [counterBudget,countEnvelope,S,T,indexed_incidence_count N hN] using h

/-- Fixed resource polynomial retaining every repeated query, controller and decoder report. -/
def controllerEnvelope (S : ℕ) : ℕ :=
  (S+1)*(countEnvelope S+S+3*(S+1)^2+S+19)

/-- The new actual public caller report, with no counter-budget or design advice. -/
theorem run_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    (SemiprimeHermiteBitsScheduledController.run N).work ≤ controllerEnvelope (resources N) := by
  have hc := counterBudget_le N hN hg
  have hn : wireCount N ≤ resources N := by
    unfold resources scalarResources
    generalize (2:ℕ)^(scopeBound (bitLength N))=ew
    generalize (2:ℕ)^(headBound N)=eh
    omega
  have hd : SemiprimePublicBudgetDimensions.decoderEnvelope (wireCount N) ≤ resources N := by
    unfold resources scalarResources
    generalize (2:ℕ)^(scopeBound (bitLength N))=ew
    generalize (2:ℕ)^(headBound N)=eh
    omega
  exact (SemiprimePublicHermiteCounterBudget.run_work N hN hg).trans (by
    unfold controllerBudget controllerEnvelope
    gcongr)

open SemiprimeReportPolynomialGrowth

/-- Fixed constants and exponents bound the new actual controller envelope. -/
theorem controllerEnvelope_monomial : ∃ C k : ℕ,∀ S,controllerEnvelope S ≤ C*(S+1)^k := by
  obtain ⟨C,k,h⟩ := SemiprimeHermiteReportEnvelope.polynomialEnvelope_monomial
  have hp : Bound (fun S => C*(inflation S+1)^k) := by
    unfold inflation
    boundArithmetic
  obtain ⟨D,l,hp⟩ := hp
  have hc (S : ℕ) : countEnvelope S ≤ D*(S+1)^l :=
    (h (inflation S)).trans (hp S)
  have hb : Bound (fun S => (S+1)*(D*(S+1)^l+S+3*(S+1)^2+S+19)) := by
    boundArithmetic
  obtain ⟨E,m,hb⟩ := hb
  refine ⟨E,m,?_⟩
  intro S
  exact (show controllerEnvelope S ≤ (S+1)*(D*(S+1)^l+S+3*(S+1)^2+S+19) by
    unfold controllerEnvelope
    gcongr
    exact hc S).trans (hb S)

end RiemannGaussian.SemiprimePublicHermiteReportPolynomial
