/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecord
import RiemannGaussian.SemiprimeD1StackPublicScaleTable
/-! # One actual348-role scale checker, scope serializer and record source
Only original binary N, physical j/k markers and a singleton selector, acquired binary
scope IDs and the caller's history/output are initialized.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleRecord
namespace I
export SemiprimeD1StackPublicScaleTable (static inputTemplate template_raw)
end I
namespace G
export SemiprimeD1StackStaticRecord (Control tableStack scopeStack recordStack original history output)
end G
/-- Complete fixed348-role inventory, including all three empty alias shadows. -/
abbrev Stack :=SemiprimeD1StackStaticRecord.Stack SemiprimeD1StackPublicScale.Stack
/-- All actual component and return labels are fixed before original N. -/
abbrev Label :=SemiprimeD1StackStaticRecord.Label SemiprimeD1StackPublicScale.Label I.static.roles.length
/-- Literal static scale checker and actual component calls; no runtime supplier. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=SemiprimeD1StackStaticRecord.program I.static
/-- Only actual original N/j/k/selector inputs, binary scope and caller accumulators. -/
def initial (bits stride frequency : List Bool) (inverse : Bool) (bank hist out : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticRecord.initial I.static (I.inputTemplate bits stride frequency inverse) bank hist out
/-- Same finite program before all original N and descriptor values. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackStaticRecord.machine I.static
/-- All348 roles, including private shadows, are physical machine roles. -/
theorem stack_card : Fintype.card Stack=348 := by
  rw [SemiprimeD1StackStaticRecord.stack_card,SemiprimeD1StackPublicScale.stack_card]
end RiemannGaussian.SemiprimeD1StackPublicScaleRecord
