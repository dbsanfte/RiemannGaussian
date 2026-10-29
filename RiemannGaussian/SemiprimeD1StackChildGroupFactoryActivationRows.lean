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
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRows
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the same literal component/cleanup clocks; no clock is a runtime operand. -/
def budget (i:Inputs) (selected:List Bool) (catalogue:List (List Bool×List Bool)) (colours:List (List Bool)):Nat:=((5*(selected).length+4))+((6*(selected).length+5))+((5*((frame selected selected)).length+4))+((5*(i.catalogue).length+4))+((SemiprimeD1StackPacketRowsExecution.timeBound selected selected catalogue colours colours+1))+(1)+((5*((vectorBits colours)).length+4))+((5*(i.colourIndex).length+4))
/-- Complete actual block; its trace and real returns come from the literal source. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool) (coordinate:Nat) (catalogue:List (List Bool×List Bool)) (selected:List Bool) (colours:List (List Bool)) (hk:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue []) (hi:i.colourIndex=List.replicate coordinate true) (hp:SemiprimeD1StackPacketRowsEncoding.present selected catalogue=true) (hr:SemiprimeD1StackPacketRowsAcquire.payload selected catalogue=SemiprimeD1PacketRows.serialize colours):
    ∃t≤budget i selected catalogue colours,Runs program t (.local 0 20) (selectedData i todo key hist map selected) (.local 0 28) (rowData i todo key hist map selected coordinate colours):=by
  let b0:Stack→List Bool:=selectedData i todo key hist map selected
  let b1:Stack→List Bool:=Function.update b0 (aux .jointKey) (selected++[])
  have h0:Runs program (5*(selected).length+4) (.local 0 20) b0 (.local 0 21) b1:=
    copy_call 5 (.local 0 20) (.local 0 21) rfl b0 selected [] (by simp [b0,aux,copyStack,copyPorts,selectedData]) (by simp [b0,data,input,aux,copyStack,copyPorts,selectedData]) (by simp [b0,data,input,aux,copyStack,selectedData])
  let b2:Stack→List Bool:=Function.update b1 (aux .jointKey) (frame selected selected)
  have h1:Runs program (6*(selected).length+5) (.local 0 21) b1 (.local 0 22) b2:=
    frame_call 0 (.local 0 21) (.local 0 22) rfl b1 selected selected (by simp [b0,b1,aux,frameStack,framePorts,selectedData]) (by simp [b0,b1,aux,frameStack,framePorts,selectedData]) (by simp [b0,b1,data,input,aux,frameStack,selectedData])
  let b3:Stack→List Bool:=Function.update b2 (rows (.inr .key)) ((frame selected selected)++[])
  have h2:Runs program (5*((frame selected selected)).length+4) (.local 0 22) b2 (.local 0 23) b3:=
    copy_call 6 (.local 0 22) (.local 0 23) rfl b2 (frame selected selected) [] (by simp [b0,b1,b2,aux,rows,copyStack,copyPorts,selectedData]) (by simp [b0,b1,b2,data,input,aux,rows,copyStack,copyPorts,selectedData]) (by simp [b0,b1,b2,data,input,aux,copyStack,selectedData])
  let b4:Stack→List Bool:=Function.update b3 (rows (.inr .catalogue)) (i.catalogue++[])
  have h3:Runs program (5*(i.catalogue).length+4) (.local 0 23) b3 (.local 0 24) b4:=
    copy_call 7 (.local 0 23) (.local 0 24) rfl b3 i.catalogue [] (by simp [b0,b1,b2,b3,data,input,aux,rows,copyStack,copyPorts,selectedData,hk]) (by simp [b0,b1,b2,b3,data,input,aux,rows,copyStack,copyPorts,selectedData]) (by simp [b0,b1,b2,b3,data,input,aux,rows,copyStack,selectedData])
  let b5:Stack→List Bool:=withRows b4 (SemiprimeD1StackPacketRowsExecution.result (frame selected selected) (SemiprimeD1StackOwnerLookup.records catalogue []) colours colours)
  obtain ⟨rowTime,hrowTime,h4⟩:=rows_call (.local 0 24) (.local 0 25) rfl b4 selected selected catalogue colours colours hp hp hr hr rfl (by
    intro k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,data,input,aux,rows,SemiprimeD1StackPacketRows.initial,selectedData,SemiprimeD1StackPacketRows.input,hk]
    · cases k <;> simp [b0,b1,b2,b3,b4,data,input,aux,rows,SemiprimeD1StackPacketRows.initial,selectedData,SemiprimeD1StackPacketRows.input,hk])
  have h5a:=peek_run (.local 0 25) (.local 15 14) (.local 15 14) (.local 0 26) (rows (.inl (.inl .output))) b5 [true] rfl (by simp [b0,b1,b2,b3,b4,b5,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,hk])
  have h5:Runs program 1 (.local 0 25) b5 (.local 0 26) b5:=by
    simpa only [List.head?_cons,SemiprimeD1StackBytecode.choose] using h5a
  let b6:Stack→List Bool:=Function.update b5 (aux .colourReader) ((vectorBits colours)++[])
  have h6:Runs program (5*((vectorBits colours)).length+4) (.local 0 26) b5 (.local 0 27) b6:=
    copy_call 8 (.local 0 26) (.local 0 27) rfl b5 (vectorBits colours) [] (by simp [b0,b1,b2,b3,b4,b5,aux,rows,copyStack,copyPorts,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk]) (by simp [b0,b1,b2,b3,b4,b5,data,input,aux,rows,copyStack,copyPorts,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk]) (by simp [b0,b1,b2,b3,b4,b5,data,input,aux,rows,copyStack,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk])
  let b7:Stack→List Bool:=Function.update b6 (aux .colourCursor) (i.colourIndex++[])
  have h7:Runs program (5*(i.colourIndex).length+4) (.local 0 27) b6 (.local 0 28) b7:=
    copy_call 9 (.local 0 27) (.local 0 28) rfl b6 i.colourIndex [] (by simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,rows,copyStack,copyPorts,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk,hi]) (by simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,rows,copyStack,copyPorts,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk]) (by simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,rows,copyStack,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,hk])
  have hfinal:b7=(rowData i todo key hist map selected coordinate colours):=by
    funext k
    rcases k with k|k|k|k|k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,rows,withRows,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,SemiprimeD1StackAdder.store,selectedData,rowData,hk,hi]
      · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,data,input,aux,rows,withRows,SemiprimeD1StackPacketRowsExecution.result,SemiprimeD1StackPacketRowsView.view,selectedData,rowData,hk,hi]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (h7)))))))
  rw [hfinal] at hwhole
  refine ⟨_,?_,hwhole⟩
  dsimp only [budget]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRows
