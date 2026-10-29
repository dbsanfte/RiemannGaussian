/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicCounterBudget
import RiemannGaussian.SemiprimeSetupPolynomialEnvelope

/-! # One polynomial of the actual public resource sum
The resource sum consists of original-input dimensions and proved parameter
envelopes. It contains no acquired counter output, measured running time, or
externally supplied summary. The executed report is bounded by a fixed
polynomial of this sum; primitive-bit refinement remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePublicReportPolynomial
open SemiprimePublicCounterBudget SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution SemiprimeMacroParameters
open SemiprimePublicBudgetDimensions

/-- All polynomial-size public dimensions, including actual separate setup menus
and the explicit entry/decoder report envelopes. -/
def scalarResources (N : ℕ) : ℕ :=
  wireCount N+factorCount N+2*wireCount N+groups N+points N+degree N+2+
    precision N+entryEnvelope (wireCount N)+scopeBound (bitLength N)+headBound N+
    4*wireCount N+(groups N)^(2*points N)+(groups N)^(points N)+
    decoderEnvelope (wireCount N)

/-- Complete public resource sum, with each exponential term kept at its
proved scale rather than replaced by a full-assignment enumeration. -/
def resources (N : ℕ) : ℕ :=
  scalarResources N+summaryBound N+
    SemiprimeCounterEnumeration.weightedCount (wireCount N) (precision N-1)+
    2^(scopeBound (bitLength N))+2^(headBound N)

/-- The retained setup/native sum is one fixed polynomial of all resources. -/
def countEnvelope (S : ℕ) : ℕ :=
  SemiprimeSetupPolynomialEnvelope.polynomialEnvelope S+
    SemiprimeNativeCounterBudget.polynomialEnvelope S

/-- The derived public counter envelope is bounded by the same fixed polynomial,
uniformly in N; no fast-guard assumptions are needed for this algebraic step. -/
theorem counterBudget_le (N : ℕ) : counterBudget N ≤ countEnvelope (resources N) := by
  have hs := SemiprimeSetupPolynomialEnvelope.setupBudget_le_envelope
    (wireCount N) (factorCount N) (2*wireCount N) (groups N) (points N) (degree N)
    2 ((groups N)^(2*points N)) ((groups N)^(points N)) (resources N)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
  have hn := SemiprimeNativeCounterBudget.nativeBudget_le_envelope
    (wireCount N) (factorCount N) (points N) (precision N) (degree N)
    (entryEnvelope (wireCount N)) (scopeBound (bitLength N)) (headBound N)
    (4*wireCount N) (groups N) (summaryBound N) (resources N)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
    (by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega)
  exact Nat.add_le_add hs hn

/-- Fixed polynomial controller envelope including all repeated counter setups. -/
def controllerEnvelope (S : ℕ) : ℕ :=
  (S+1)*(countEnvelope S+S+3*(S+1)^2+S+19)

/-- The public controller envelope uses no extra asymptotic resource. -/
theorem controllerBudget_le (N : ℕ) :
    controllerBudget N ≤ controllerEnvelope (resources N) := by
  have hn : wireCount N ≤ resources N := by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega
  have hd : decoderEnvelope (wireCount N) ≤ resources N := by unfold resources scalarResources; generalize (2:ℕ)^(scopeBound (bitLength N)) = ew; generalize (2:ℕ)^(headBound N) = eh; omega
  have hc := counterBudget_le N
  unfold controllerBudget controllerEnvelope
  gcongr

/-- The actual controller report is bounded by one fixed resource polynomial. -/
theorem run_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    (SemiprimeFullSetupScheduledController.run N).work ≤ controllerEnvelope (resources N) :=
  (SemiprimePublicCounterBudget.run_work N hN hg).trans (controllerBudget_le N)

/-- Eventual resource-polynomial bound for the original-input executed report. -/
theorem eventually_run_work :
    ∀ᶠ N : ℕ in Filter.atTop,
      (SemiprimeFullSetupScheduledController.run N).work ≤ controllerEnvelope (resources N) := by
  filter_upwards [SemiprimePublicCounterBudget.eventually_run_work] with N hN
  exact hN.trans (controllerBudget_le N)

end RiemannGaussian.SemiprimePublicReportPolynomial
