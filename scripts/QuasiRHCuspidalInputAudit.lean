/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability
import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Cuspidal-input applicability audit for the actual inverse coefficients

Dunn's Theorem 1.5 concerns the coefficients of a cuspidal cubic
metaplectic form. The native squarefree/cube coefficients come instead
from the normalized cubic Eisenstein source residual. Its actual cusp
average is nonzero, including after source projection and the coefficient
normalization/conjugation. Thus direct substitution fails the necessary
zero-average input gate. This does not estimate the residual, exclude a
cuspidal decomposition, or assert what happens to a hypothetical-zero
source under an unproved cuspidal projection.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace OpenAIReview.CuspidalInput
open OAI CubicEisenstein ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
  CubicJacobiGlobal EisensteinEmbedding
local notation "Eis" => ActualEisensteinCubic.O

/-- A necessary cusp condition on the native fixed strip; this is not a
definition of all the hypotheses of the published cuspidal estimate. -/
def ZeroCuspStripAverage (f : HyperbolicSpace → ℂ) : Prop :=
  (∫ w in cuspPeriodStrip 5 6, f w ∂hyperbolicVolume) = 0

/-- The corresponding fixed-strip gate for the native quotient Hilbert space. -/
def ZeroKernelCuspAverage (f : KernelQuotientL2) : Prop :=
  kernelCuspStripAverage f = 0

theorem residual_kernel_average_ne_zero :
    kernelCuspStripAverage cubicEisensteinResidue ≠ 0 := by
  rw [cubicEisensteinResidue_cusp_average]
  exact cuspConstantAverageResidue_ne_zero

theorem source_projection_kernel_average_ne_zero :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue) ≠ 0 := by
  rw [kernelSourceProjection_residue_cusp_average]
  exact cuspConstantAverageResidue_ne_zero

theorem residual_fails_kernel_gate : ¬ ZeroKernelCuspAverage cubicEisensteinResidue :=
  residual_kernel_average_ne_zero

theorem source_projection_fails_kernel_gate :
    ¬ ZeroKernelCuspAverage (kernelSourceProjection cubicEisensteinResidue) :=
  source_projection_kernel_average_ne_zero

theorem actual_source_average_ne_zero :
    (∫ w in cuspPeriodStrip 5 6, cubicSourceResidualFunction w ∂hyperbolicVolume) ≠ 0 := by
  rw [cubicSourceResidualFunction_cusp_average]
  exact cuspConstantAverageResidue_ne_zero

theorem actual_source_fails_cuspidal_input : ¬ ZeroCuspStripAverage cubicSourceResidualFunction :=
  actual_source_average_ne_zero

/-- The conjugation and scalar occurring in the actual coefficient bridge
do not remove the nonzero constant channel. -/
def normalizedConjugateSource (w : HyperbolicSpace) : ℂ :=
  infinityCoefficientScalar⁻¹ * star (cubicSourceResidualFunction w)

theorem normalized_source_average :
    (∫ w in cuspPeriodStrip 5 6, normalizedConjugateSource w ∂hyperbolicVolume) =
      infinityCoefficientScalar⁻¹ * star cuspConstantAverageResidue := by
  simp only [normalizedConjugateSource, Complex.star_def]
  rw [integral_const_mul, integral_conj, cubicSourceResidualFunction_cusp_average]

theorem normalized_source_average_ne_zero :
    (∫ w in cuspPeriodStrip 5 6, normalizedConjugateSource w ∂hyperbolicVolume) ≠ 0 := by
  rw [normalized_source_average]
  exact mul_ne_zero (inv_ne_zero infinityCoefficientScalar_ne_zero)
    (star_ne_zero.mpr cuspConstantAverageResidue_ne_zero)

theorem normalized_source_fails_cuspidal_input :
    ¬ ZeroCuspStripAverage normalizedConjugateSource :=
  normalized_source_average_ne_zero

/-- The native `I*J³` coefficients are exactly the noncuspidal residual
coefficients; no arbitrary coefficient family replaces them. -/
theorem actual_squarefree_cube_coefficient (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) (hsq : Squarefree I) :
    infinityCoefficientScalar⁻¹ *
      star (sourceResidualFourierCoefficient (primaryGenerator I * primaryGenerator J ^ 3)) =
      (‖eisEmbedding (primaryGenerator J)‖ : ℂ) *
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))) * gaussTwo I hI :=
  normalized_infinityCoefficient_squarefree_cube I J hI hJ hsq

/-- Normalization cannot be evaded by identifying this residual function
with a zero-average cuspidal input. -/
theorem zero_average_input_ne_normalized_source (f : HyperbolicSpace → ℂ)
    (hf : ZeroCuspStripAverage f) : f ≠ normalizedConjugateSource := by
  intro he
  exact normalized_source_fails_cuspidal_input (he ▸ hf)

theorem zero_average_kernel_input_ne_source_projection (f : KernelQuotientL2)
    (hf : ZeroKernelCuspAverage f) : f ≠ kernelSourceProjection cubicEisensteinResidue := by
  intro he
  exact source_projection_fails_kernel_gate (he ▸ hf)

/-- Any decomposition with a zero-average piece leaves the entire actual
nonzero constant channel in its remainder. No zero-source conclusion is made. -/
theorem zero_average_kernel_remainder (f : KernelQuotientL2)
    (hf : ZeroKernelCuspAverage f) :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue - f) =
      cuspConstantAverageResidue := by
  rw [map_sub, kernelSourceProjection_residue_cusp_average]
  rw [show kernelCuspStripAverage f = 0 from hf, sub_zero]

theorem zero_average_kernel_remainder_ne_zero (f : KernelQuotientL2)
    (hf : ZeroKernelCuspAverage f) : kernelSourceProjection cubicEisensteinResidue - f ≠ 0 := by
  intro he
  have ha := zero_average_kernel_remainder f hf
  rw [he, map_zero] at ha
  exact cuspConstantAverageResidue_ne_zero ha.symm

end OpenAIReview.CuspidalInput

#lint+ in OpenAIReview.CuspidalInput

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty cuspidal-input audit."
  logInfo m!"Cuspidal-input audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cuspidal-input"
  IO.FS.writeFile ".lake/arithmetic-operator-cuspidal-input/axioms.json"
    (Json.mkObj [("scope",toJson "actual normalized cubic Eisenstein source residual fails necessary zero-cusp-average input; no projection-source or prime estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
