/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivation
/-! # Abstract physical boundaries for one whole activation iteration
These are full115-word specifications. No boundary structure or evaluator
occurs in the literal program or its thirteen-word input interface.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackChildGroupFactoryActivation
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Only the genuinely acquired colour supplies this proof-side Boolean. -/
def active (i:Inputs) (coordinate:Nat) (colours:List (List Bool)):Bool:=
  decide (SemiprimeBitArithmetic.bitValue (Col.result coordinate colours).1=
    SemiprimeBitArithmetic.bitValue i.group)
/-- All eleven lookup allocations are clean; the discovered ID is in its real word. -/
def selectedData (i:Inputs) (todo key hist map selected:List Bool):Stack→List Bool:=
  Function.update (data i todo key hist map) (aux .selectedID) selected
/-- Both real catalogue rows and unary coordinate have been physically acquired. -/
def rowData (i:Inputs) (todo key hist map selected:List Bool) (coordinate:Nat)
    (colours:List (List Bool)):Stack→List Bool:=
  let base:=Function.update (selectedData i todo key hist map selected) (aux .jointKey) (frame selected selected)
  let full:=withRows base (SemiprimeD1StackPacketRowsExecution.result
    (frame selected selected) i.catalogue colours colours)
  Function.update (Function.update full (aux .colourReader) (vectorBits colours))
    (aux .colourCursor) (List.replicate coordinate true)
/-- The actual flag and map row are logged; precisely listed work remains to be drained. -/
def loggedData (i:Inputs) (todo key hist map selected:List Bool) (coordinate:Nat)
    (colours:List (List Bool)):Stack→List Bool:=
  let flag:=active i coordinate colours
  let base:=selectedData i todo key (flag::hist) (true::frame key (frame [flag] map)) selected
  let joint:=Function.update base (aux .jointKey) (frame selected selected)
  let full:=withRows joint (SemiprimeD1StackPacketRowsExecution.result
    (frame selected selected) i.catalogue colours colours)
  Function.update (Function.update (Function.update full (aux .colourReader) (Col.result coordinate colours).2)
    (aux .colourWord) (Col.result coordinate colours).1) (aux .flagScratch) [flag]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationView
