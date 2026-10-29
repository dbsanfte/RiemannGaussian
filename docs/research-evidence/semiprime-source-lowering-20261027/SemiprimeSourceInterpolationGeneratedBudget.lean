/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits
import RiemannGaussian.SemiprimeSourceInterpolationProgramBudget

/-! # Original-resource work of acquired source-code generation and physical readout
The actual generator, acquired literals, emitted instruction interpreter and final
readout are joined. The native scalar generation/acquisition ledger is retained
explicitly alongside the Boolean ledger; original parity/prescription/syntax
construction and a complete primitive machine refinement remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceInterpolationGeneratedBudget
open SemiprimeSourceInterpolationGeneratedBits SemiprimeSourceInterpolationProgramBits
open SemiprimeSourceInterpolationProgramBudget SemiprimeSourceArrayProgramGeneration
open SemiprimeReportPolynomialGrowth
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Original dimension monotonicity for the fixed syntax-size polynomial. -/
theorem nodeCap_mono {Q S : ℕ} (h : Q ≤ S) :
    SemiprimeSourceInterpolationHeight.nodeCap Q ≤ SemiprimeSourceInterpolationHeight.nodeCap S := by
  unfold SemiprimeSourceInterpolationHeight.nodeCap
  gcongr

/-- The paid code-generation polynomial is monotone in original width and syntax size. -/
theorem generationBudget_mono {J N J' N' : ℕ} (hJ : J ≤ J') (hN : N ≤ N') :
    generationBudget J N ≤ generationBudget J' N' := by
  unfold generationBudget unitWork
  gcongr

/-- Actual original-source code generation needs no external code or constant-table advice. -/
theorem source_generation_work {r Q : ℕ} (A R S : ℕ) (a y : UniversalType r Q 1)
    (hQ : Q ≤ S) (hR : R ≤ S) :
    (generate (R+1) (source A R a y)).work ≤
      generationBudget (S+1) (SemiprimeSourceInterpolationHeight.nodeCap S) :=
  (generate_work _ _).trans (generationBudget_mono (Nat.add_le_add_right hR 1)
    ((SemiprimeSourceInterpolationHeight.code_nodes A R a y).trans (nodeCap_mono hQ)))

/-- All retained ledgers of the generated-source coefficient entry point. -/
def workEnvelope (S : ℕ) : ℕ :=
  generationBudget (S+1) (SemiprimeSourceInterpolationHeight.nodeCap S)+
    backendEnvelope S+bankEnvelope S+20

/-- Both original code generation and physical coefficient acquisition have a
derived resource-only bound; this still distinguishes native scalar work from bit work. -/
theorem acquire_work {r Q : ℕ} (A R S : ℕ) (a y : UniversalType r Q 1) (k : ℕ)
    (hA : A ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) :
    (SemiprimeSourceInterpolationGeneratedBits.acquire A R a y k).acquisitionWork+
      (SemiprimeSourceInterpolationGeneratedBits.acquire A R a y k).bitWork ≤ workEnvelope S := by
  have hgen := source_generation_work A R S a y hQ hR
  have hback := acquire_backend_work A R S a y k hA hQ hR
  have hbank := (source_resources A R S a y hA hQ hR).1
  exact (acquire_work_components A R a y k).trans
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hgen hback) hbank) 20)

/-- Fixed monomial witnesses for the actual generated-source joined report. -/
theorem work_monomial : ∃ C k : ℕ,∀ S,workEnvelope S ≤ C*(S+1)^k := by
  have hg : Bound (fun S => generationBudget (S+1) (SemiprimeSourceInterpolationHeight.nodeCap S)) := by
    simp only [generationBudget,unitWork,SemiprimeSourceInterpolationHeight.nodeCap]
    boundArithmetic
  have hb : Bound (fun S => bankEnvelope S) := by
    simp only [bankEnvelope,SemiprimeSourceInterpolationHeight.nodeCap]
    boundArithmetic
  exact add_bound (add_bound (add_bound hg backend_monomial) hb) (constant_bound 20)

end RiemannGaussian.SemiprimeSourceInterpolationGeneratedBudget
