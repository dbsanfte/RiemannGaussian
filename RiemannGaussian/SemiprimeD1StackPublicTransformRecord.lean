/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecord
import RiemannGaussian.SemiprimeD1StackPublicTransformTable
/-! # One actual436-role transform checker, scope serializer and record source
Only original binary N, two physical descriptor flags, acquired binary
scope IDs and the caller's history/output are initialized.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRecord
namespace I
export SemiprimeD1StackPublicTransformTable (static inputTemplate template_raw)
end I
namespace G
export SemiprimeD1StackStaticRecord (Control tableStack scopeStack recordStack original history output)
end G
/-- Complete fixed436-role inventory, including all three empty alias shadows. -/
abbrev Stack :=SemiprimeD1StackStaticRecord.Stack SemiprimeD1StackPublicTransform.Stack
/-- All actual component and return labels are fixed before original N. -/
abbrev Label :=SemiprimeD1StackStaticRecord.Label SemiprimeD1StackPublicTransform.Label I.static.roles.length
/-- Literal static transform checker and actual component calls; no runtime supplier. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=SemiprimeD1StackStaticRecord.program I.static
/-- Only actual original N/two-flags inputs, binary scope and caller accumulators. -/
def initial (bits : List Bool) (second inverse : Bool) (bank hist out : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticRecord.initial I.static (I.inputTemplate bits second inverse) bank hist out
/-- Same finite program before all original N and descriptor values. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackStaticRecord.machine I.static
/-- All436 roles, including private shadows, are physical machine roles. -/
theorem stack_card : Fintype.card Stack=436 := by
  rw [SemiprimeD1StackStaticRecord.stack_card,SemiprimeD1StackPublicTransform.stack_card]
end RiemannGaussian.SemiprimeD1StackPublicTransformRecord
