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
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLog
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the same literal component/cleanup clocks; no clock is a runtime operand. -/
def budget (i:Inputs) (key:List Bool) (coordinate:Nat) (colours:List (List Bool)):Nat:=((Col.time coordinate colours))+((5*((Col.result coordinate colours).1).length+4))+((5*(i.group).length+4))+((SemiprimeD1StackWordEqualExecution.executionTime ((Col.result coordinate colours).1++[]) i.group+1))+(3)+((6*([(SemiprimeD1StackChildGroupFactoryActivationView.active i coordinate colours)]).length+5))+((6*(key).length+5))+(1)
/-- Complete actual block; its trace and real returns come from the literal source. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool) (coordinate:Nat) (selected:List Bool) (colours:List (List Bool)):
    ∃t≤budget i key coordinate colours,Runs program t (.local 0 28) (rowData i todo key hist map selected coordinate colours) (.local 1 17) (loggedData i todo key hist map selected coordinate colours):=by
  let active:=decide (SemiprimeBitArithmetic.bitValue (Col.result coordinate colours).1=
    SemiprimeBitArithmetic.bitValue i.group)
  let b0:Stack→List Bool:=rowData i todo key hist map selected coordinate colours
  let b1:Stack→List Bool:=Col.view b0 [] (Col.result coordinate colours).2 (Col.result coordinate colours).1
  have h0view:Col.view b0 (List.replicate coordinate true) (vectorBits colours) []=b0:=by
    have hc:b0 (aux .colourCursor)=List.replicate coordinate true:=(by simp [b0,aux,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
    have hr:b0 (aux .colourReader)=vectorBits colours:=(by simp [b0,aux,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
    have hw:b0 (aux .colourWord)=[]:=(by simp [b0,data,input,aux,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
    unfold Col.view
    rw [←hc,Function.update_eq_self,←hr,Function.update_eq_self,←hw,Function.update_eq_self]
  have h0:Runs program (Col.time coordinate colours) (.local 0 28) b0 (.local 1 6) b1:=by
    have h:=Col.source_trace b0 coordinate colours (by simp [b0,data,input,aux,field,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,data,input,aux,field,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
    rw [h0view] at h
    exact h
  let b2:Stack→List Bool:=Function.update b1 (arithmetic .left) ((Col.result coordinate colours).1++[])
  have h1:Runs program (5*((Col.result coordinate colours).1).length+4) (.local 1 6) b1 (.local 1 7) b2:=
    copy_call 10 (.local 1 6) (.local 1 7) rfl b1 (Col.result coordinate colours).1 [] (by simp [b0,b1,aux,arithmetic,copyStack,copyPorts,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,data,input,aux,arithmetic,copyStack,copyPorts,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,data,input,aux,copyStack,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  let b3:Stack→List Bool:=Function.update b2 (arithmetic .right) (i.group++[])
  have h2:Runs program (5*(i.group).length+4) (.local 1 7) b2 (.local 1 8) b3:=
    copy_call 11 (.local 1 7) (.local 1 8) rfl b2 i.group [] (by simp [b0,b1,b2,data,input,aux,arithmetic,copyStack,copyPorts,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,data,input,aux,arithmetic,copyStack,copyPorts,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,data,input,aux,arithmetic,copyStack,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  let b4:Stack→List Bool:=withArithmetic b3 (SemiprimeD1StackAdder.store [] [] [] [decide (SemiprimeBitArithmetic.bitValue ((Col.result coordinate colours).1++[])=SemiprimeBitArithmetic.bitValue i.group)])
  have h3:Runs program (SemiprimeD1StackWordEqualExecution.executionTime ((Col.result coordinate colours).1++[]) i.group+1) (.local 1 8) b3 (.local 1 9) b4:=
    equal_call (.local 1 8) (.local 1 9) rfl b3 ((Col.result coordinate colours).1++[]) i.group (by intro k;cases k <;> simp [b0,b1,b2,b3,data,input,aux,arithmetic,withRows,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,rowData])
  let b5:Stack→List Bool:=Function.update (Function.update (Function.update b4 (arithmetic .output) []) (aux .flagScratch) [active]) (aux .activationHistory) (active::hist)
  have h4f:b4 (arithmetic .output)=[active]:=by simp [b0,b1,b2,b3,b4,aux,arithmetic,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,rowData,active]
  have h4s:b4 (aux .flagScratch)=[]:=(by simp [b0,b1,b2,b3,b4,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  have h4h:b4 (aux .activationHistory)=hist:=(by simp [b0,b1,b2,b3,b4,data,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  have h4:Runs program 3 (.local 1 9) b4 (.local 1 14) b5:=by
    simpa only [h4s,h4h] using flag_trace b4 active h4f
  let b6:Stack→List Bool:=Function.update b5 (aux .activationMap) (frame [active] map)
  have h5:Runs program (6*([active]).length+5) (.local 1 14) b5 (.local 1 15) b6:=
    frame_call 1 (.local 1 14) (.local 1 15) rfl b5 [active] map (by simp [b0,b1,b2,b3,b4,b5,aux,arithmetic,frameStack,framePorts,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,b3,b4,b5,data,aux,arithmetic,frameStack,framePorts,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,b3,b4,b5,data,input,aux,arithmetic,frameStack,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  let b7:Stack→List Bool:=Function.update b6 (aux .activationMap) (frame key (frame [active] map))
  have h6:Runs program (6*(key).length+5) (.local 1 15) b6 (.local 1 16) b7:=
    frame_call 2 (.local 1 15) (.local 1 16) rfl b6 key (frame [active] map) (by simp [b0,b1,b2,b3,b4,b5,b6,data,aux,arithmetic,frameStack,framePorts,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,b3,b4,b5,b6,aux,arithmetic,frameStack,framePorts,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData]) (by simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,frameStack,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  let b8:Stack→List Bool:=Function.update b7 (aux .activationMap) (true::(frame key (frame [active] map)))
  have h7p:b7 (aux .activationMap)=(frame key (frame [active] map)):=(by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,arithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData])
  have h7a:=push_run (.local 1 16) (.local 1 17) (aux .activationMap) true b7 rfl
  have h7:Runs program 1 (.local 1 16) b7 (.local 1 17) b8:=by
    simpa only [h7p] using h7a
  have hfinal:b8=(loggedData i todo key hist map selected coordinate colours):=by
    funext k
    rcases k with k|k|k|k|k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
      · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,data,input,aux,arithmetic,withRows,withArithmetic,Col.view,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,loggedData,SemiprimeD1StackChildGroupFactoryActivationView.active,active]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (h7)))))))
  rw [hfinal] at hwhole
  refine ⟨_,?_,hwhole⟩
  dsimp only [budget]
  simp only [List.length_cons,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLog
