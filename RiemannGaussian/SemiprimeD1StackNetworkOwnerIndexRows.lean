/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexSetup
/-! # Actual vertex-tag, ports/table fields and complete paid table cleanup
The record port vector and serialized table are literal physical field bytes.
The source parses and copies the ENTIRE table then physically drains it, keeping
the original record tape untouched. No table callback or unit-price parse is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexRows
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackNetworkOwnerIndexSetup SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Clearing an actually parsed validation flag changes no retained source/port/counter word. -/
theorem clear_view_valid (vertices count reader todo ports owner history:List Bool) :
    Function.update (Function.update (view vertices count reader todo ports owner history) .valid [true])
      .valid []=view vertices count reader todo ports owner history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- A copied whole table survives its true-flag pop; every other work word remains empty. -/
theorem clear_table_valid (vertices count reader todo ports owner history table:List Bool) :
    Function.update (Function.update (Function.update (view vertices count reader todo ports owner history)
      .table table) .valid [true]) .valid []=
        Function.update (view vertices count reader todo ports owner history) .table table :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Actually draining the copied table restores the exact clean source boundary. -/
theorem clear_view_table (vertices count reader todo ports owner history table:List Bool) :
    Function.update (Function.update (view vertices count reader todo ports owner history) .table table)
      .table []=view vertices count reader todo ports owner history :=by
  funext k;cases k <;> simp [view,Function.update]
/-- Whole real vertex-field acquisition, including every table byte and its actual cleanup. -/
theorem vertex_fields (vertices count todo owner history portTape tableTape tail:List Bool) :
    Runs program (8*portTape.length+9*tableTape.length+18) (ctl .vertexTag)
      (view vertices count (true::frame portTape (frame tableTape tail)) todo [] owner history) (ctl .portLoop)
      (view vertices count tail todo portTape owner history) :=by
  have h0:=pop_run .vertexTag (ctl .abort) (ctl .abort) (ctl .parsePorts) .reader
    (view vertices count (true::frame portTape (frame tableTape tail)) todo [] owner history)
    (true::frame portTape (frame tableTape tail)) rfl rfl
  change Runs program 1 (ctl .vertexTag) _ (ctl .parsePorts)
    (Function.update (view vertices count (true::frame portTape (frame tableTape tail)) todo [] owner history)
      .reader (frame portTape (frame tableTape tail))) at h0
  rw [view_reader] at h0
  have h1:=field_call .ports .parsePorts .portsValid rfl
    (view vertices count (frame portTape (frame tableTape tail)) todo [] owner history)
    portTape (frame tableTape tail) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update
      (view vertices count (frame portTape (frame tableTape tail)) todo [] owner history)
      .reader (frame tableTape tail)) .ports portTape) .valid [true]) at h1
  rw [view_reader,view_ports] at h1
  have h2:=pop_run .portsValid (ctl .abort) (ctl .abort) (ctl .parseTable) .valid
    (Function.update (view vertices count (frame tableTape tail) todo portTape owner history) .valid [true])
    [true] rfl (Function.update_self _ _ _)
  change Runs program 1 (ctl .portsValid) _ (ctl .parseTable)
    (Function.update (Function.update (view vertices count (frame tableTape tail) todo portTape owner history)
      .valid [true]) .valid []) at h2
  rw [clear_view_valid] at h2
  have h3:=field_call .table .parseTable .tableValid rfl
    (view vertices count (frame tableTape tail) todo portTape owner history) tableTape tail rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update
      (view vertices count (frame tableTape tail) todo portTape owner history) .reader tail)
      .table tableTape) .valid [true]) at h3
  rw [view_reader] at h3
  have h4:=pop_run .tableValid (ctl .abort) (ctl .abort) (ctl .clearTable) .valid
    (Function.update (Function.update (view vertices count tail todo portTape owner history) .table tableTape)
      .valid [true]) [true] rfl (Function.update_self _ _ _)
  change Runs program 1 (ctl .tableValid) _ (ctl .clearTable)
    (Function.update (Function.update (Function.update (view vertices count tail todo portTape owner history)
      .table tableTape) .valid [true]) .valid []) at h4
  rw [clear_table_valid] at h4
  have h5:=drain_loop .clearTable (ctl .portLoop) .table rfl
    (Function.update (view vertices count tail todo portTape owner history) .table tableTape) tableTape
    (Function.update_self _ _ _)
  rw [clear_view_table] at h5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  have hc:((((1+(8*portTape.length+7))+1)+(8*tableTape.length+7))+1)+(tableTape.length+1)=
      8*portTape.length+9*tableTape.length+18 :=by omega
  simpa only [hc] using h
/-- Complete record-field read/cleanup time is linear in its actual two physical field lengths. -/
theorem vertex_fields_le (ports table:List Bool) :
    8*ports.length+9*table.length+18 ≤20*(ports.length+table.length+1) :=by omega
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexRows
