/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationView
/-! # Actual whole activation source block, with its complete115-word boundary -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCleanup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the same literal component/cleanup clocks; no clock is a runtime operand. -/
def budget (i:Inputs) (selected:List Bool) (coordinate:Nat) (colours:List (List Bool)):Nat:=(((selected).length+1))+((((frame selected selected)).length+1))+((((Col.result coordinate colours).1).length+1))+((((Col.result coordinate colours).2).length+1))+((([]:List Bool).length+1))+((([(SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours)]).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([true]).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((((frame selected selected)).length+1))+((((i.catalogue)).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((((vectorBits colours)).length+1))+((((vectorBits colours)).length+1))
/-- Complete actual block; its trace and real returns come from the literal source. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool) (coordinate:Nat) (selected:List Bool) (colours:List (List Bool)):
    ∃t≤budget i selected coordinate colours,Runs program t (.local 1 17) (loggedData i todo key hist map selected coordinate colours) (.local 2 10) (data i todo key (SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours::hist) (true::frame key (frame [SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours] map))):=by
  let active:=decide (SemiprimeBitArithmetic.bitValue (Col.result coordinate colours).1=
    SemiprimeBitArithmetic.bitValue i.group)
  let b0:Stack→List Bool:=loggedData i todo key hist map selected coordinate colours
  let b1:Stack→List Bool:=Function.update b0 (aux .selectedID) []
  have h0:Runs program ((selected).length+1) (.local 1 17) b0 (.local 1 18) b1:=
    drain_loop (.local 1 17) (.local 1 18) (aux .selectedID) rfl b0 selected (by simp [b0,aux,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b2:Stack→List Bool:=Function.update b1 (aux .jointKey) []
  have h1:Runs program (((frame selected selected)).length+1) (.local 1 18) b1 (.local 1 19) b2:=
    drain_loop (.local 1 18) (.local 1 19) (aux .jointKey) rfl b1 (frame selected selected) (by simp [b0,b1,aux,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b3:Stack→List Bool:=Function.update b2 (aux .colourWord) []
  have h2:Runs program (((Col.result coordinate colours).1).length+1) (.local 1 19) b2 (.local 1 20) b3:=
    drain_loop (.local 1 19) (.local 1 20) (aux .colourWord) rfl b2 (Col.result coordinate colours).1 (by simp [b0,b1,b2,aux,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b4:Stack→List Bool:=Function.update b3 (aux .colourReader) []
  have h3:Runs program (((Col.result coordinate colours).2).length+1) (.local 1 20) b3 (.local 1 21) b4:=
    drain_loop (.local 1 20) (.local 1 21) (aux .colourReader) rfl b3 (Col.result coordinate colours).2 (by simp [b0,b1,b2,b3,aux,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b5:Stack→List Bool:=Function.update b4 (aux .colourCursor) []
  have h4:Runs program (([]).length+1) (.local 1 21) b4 (.local 1 22) b5:=
    drain_loop (.local 1 21) (.local 1 22) (aux .colourCursor) rfl b4 [] (by simp [b0,b1,b2,b3,b4,data,input,aux,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b6:Stack→List Bool:=Function.update b5 (aux .flagScratch) []
  have h5:Runs program (([active]).length+1) (.local 1 22) b5 (.local 1 23) b6:=
    drain_loop (.local 1 22) (.local 1 23) (aux .flagScratch) rfl b5 [active] (by simp [b0,b1,b2,b3,b4,b5,aux,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active])
  let b7:Stack→List Bool:=Function.update b6 (rows (.inl (.inl .left))) []
  have h6:Runs program (([]).length+1) (.local 1 23) b6 (.local 1 24) b7:=
    drain_loop (.local 1 23) (.local 1 24) (rows (.inl (.inl .left))) rfl b6 [] (by simp [b0,b1,b2,b3,b4,b5,b6,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b8:Stack→List Bool:=Function.update b7 (rows (.inl (.inl .right))) []
  have h7:Runs program (([]).length+1) (.local 1 24) b7 (.local 1 25) b8:=
    drain_loop (.local 1 24) (.local 1 25) (rows (.inl (.inl .right))) rfl b7 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b9:Stack→List Bool:=Function.update b8 (rows (.inl (.inl .scratch))) []
  have h8:Runs program (([]).length+1) (.local 1 25) b8 (.local 1 26) b9:=
    drain_loop (.local 1 25) (.local 1 26) (rows (.inl (.inl .scratch))) rfl b8 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b10:Stack→List Bool:=Function.update b9 (rows (.inl (.inl .output))) []
  have h9:Runs program (([true]).length+1) (.local 1 26) b9 (.local 1 27) b10:=
    drain_loop (.local 1 26) (.local 1 27) (rows (.inl (.inl .output))) rfl b9 [true] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b11:Stack→List Bool:=Function.update b10 (rows (.inl (.inr .query))) []
  have h10:Runs program (([]).length+1) (.local 1 27) b10 (.local 1 28) b11:=
    drain_loop (.local 1 27) (.local 1 28) (rows (.inl (.inr .query))) rfl b10 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b12:Stack→List Bool:=Function.update b11 (rows (.inl (.inr .reader))) []
  have h11:Runs program (([]).length+1) (.local 1 28) b11 (.local 1 29) b12:=
    drain_loop (.local 1 28) (.local 1 29) (rows (.inl (.inr .reader))) rfl b11 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b13:Stack→List Bool:=Function.update b12 (rows (.inl (.inr .fieldScratch))) []
  have h12:Runs program (([]).length+1) (.local 1 29) b12 (.local 1 30) b13:=
    drain_loop (.local 1 29) (.local 1 30) (rows (.inl (.inr .fieldScratch))) rfl b12 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b14:Stack→List Bool:=Function.update b13 (rows (.inl (.inr .valid))) []
  have h13:Runs program (([]).length+1) (.local 1 30) b13 (.local 1 31) b14:=
    drain_loop (.local 1 30) (.local 1 31) (rows (.inl (.inr .valid))) rfl b13 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b15:Stack→List Bool:=Function.update b14 (rows (.inl (.inr .copyScratch))) []
  have h14:Runs program (([]).length+1) (.local 1 31) b14 (.local 2 0) b15:=
    drain_loop (.local 1 31) (.local 2 0) (rows (.inl (.inr .copyScratch))) rfl b14 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b16:Stack→List Bool:=Function.update b15 (rows (.inl (.inr .discard))) []
  have h15:Runs program (([]).length+1) (.local 2 0) b15 (.local 2 1) b16:=
    drain_loop (.local 2 0) (.local 2 1) (rows (.inl (.inr .discard))) rfl b15 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b17:Stack→List Bool:=Function.update b16 (rows (.inl (.inr .output))) []
  have h16:Runs program (([]).length+1) (.local 2 1) b16 (.local 2 2) b17:=
    drain_loop (.local 2 1) (.local 2 2) (rows (.inl (.inr .output))) rfl b16 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b18:Stack→List Bool:=Function.update b17 (rows (.inr .key)) []
  have h17:Runs program (((frame selected selected)).length+1) (.local 2 2) b17 (.local 2 3) b18:=
    drain_loop (.local 2 2) (.local 2 3) (rows (.inr .key)) rfl b17 (frame selected selected) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b19:Stack→List Bool:=Function.update b18 (rows (.inr .catalogue)) []
  have h18:Runs program (((i.catalogue)).length+1) (.local 2 3) b18 (.local 2 4) b19:=
    drain_loop (.local 2 3) (.local 2 4) (rows (.inr .catalogue)) rfl b18 (i.catalogue) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b20:Stack→List Bool:=Function.update b19 (rows (.inr .keyReader)) []
  have h19:Runs program (([]).length+1) (.local 2 4) b19 (.local 2 5) b20:=
    drain_loop (.local 2 4) (.local 2 5) (rows (.inr .keyReader)) rfl b19 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b21:Stack→List Bool:=Function.update b20 (rows (.inr .leftBytes)) []
  have h20:Runs program (([]).length+1) (.local 2 5) b20 (.local 2 6) b21:=
    drain_loop (.local 2 5) (.local 2 6) (rows (.inr .leftBytes)) rfl b20 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b22:Stack→List Bool:=Function.update b21 (rows (.inr .leftHistory)) []
  have h21:Runs program (([]).length+1) (.local 2 6) b21 (.local 2 7) b22:=
    drain_loop (.local 2 6) (.local 2 7) (rows (.inr .leftHistory)) rfl b21 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b23:Stack→List Bool:=Function.update b22 (rows (.inr .rightHistory)) []
  have h22:Runs program (([]).length+1) (.local 2 7) b22 (.local 2 8) b23:=
    drain_loop (.local 2 7) (.local 2 8) (rows (.inr .rightHistory)) rfl b22 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b24:Stack→List Bool:=Function.update b23 (rows (.inr .leftOutput)) []
  have h23:Runs program (((vectorBits colours)).length+1) (.local 2 8) b23 (.local 2 9) b24:=
    drain_loop (.local 2 8) (.local 2 9) (rows (.inr .leftOutput)) rfl b23 (vectorBits colours) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  let b25:Stack→List Bool:=Function.update b24 (rows (.inr .rightOutput)) []
  have h24:Runs program (((vectorBits colours)).length+1) (.local 2 9) b24 (.local 2 10) b25:=
    drain_loop (.local 2 9) (.local 2 10) (rows (.inr .rightOutput)) rfl b24 (vectorBits colours) (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active])
  have hfinal:b25=(data i todo key (SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours::hist) (true::frame key (frame [SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours] map))):=by
    funext k
    rcases k with k|k|k|k|k|k
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
    · simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
    · by_cases h0:k=.selectedID
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      by_cases h1:k=.jointKey
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      by_cases h2:k=.colourWord
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      by_cases h3:k=.colourReader
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      by_cases h4:k=.colourCursor
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      by_cases h5:k=.flagScratch
      · subst k;simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active]
      simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,h0,h1,h2,h3,h4,h5]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (join h12 (join h13 (join h14 (join h15 (join h16 (join h17 (join h18 (join h19 (join h20 (join h21 (join h22 (join h23 (h24))))))))))))))))))))))))
  rw [hfinal] at hwhole
  refine ⟨_,?_,hwhole⟩
  dsimp only [budget]
  simp only [List.length_cons,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCleanup
