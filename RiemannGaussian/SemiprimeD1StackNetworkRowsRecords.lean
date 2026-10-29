/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsView
/-! # Actual right-vertex tag, ports/table fields and WHOLEtable cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsRecords
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Consuming a real true-valid word restores the clean boundary literally. -/
theorem clear_valid (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences:List Bool) :
    Function.update (Function.update (view index reader ports rowHistory history factors occurrences) (aux .valid) [true]) (aux .valid) []=
      view index reader ports rowHistory history factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Whole table bytes survive the real validity pop before their physical drain. -/
theorem clear_table_valid (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences table:List Bool) :
    Function.update (Function.update (Function.update (view index reader ports rowHistory history factors occurrences) (aux .table) table)
      (aux .valid) [true]) (aux .valid) []=
        Function.update (view index reader ports rowHistory history factors occurrences) (aux .table) table :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Draining the ACTUALcopied whole table restores every clean boundary role, including all17index caches. -/
theorem clear_table (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences table:List Bool) :
    Function.update (Function.update (view index reader ports rowHistory history factors occurrences) (aux .table) table) (aux .table) []=
      view index reader ports rowHistory history factors occurrences :=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual factor tag +both FULLfield parses/truevalid pops +whole table drain, before any port lookup. -/
theorem factor_fields (index:I.Stack→List Bool) (history factors occurrences ports table tail:List Bool) :
    Runs program (8*ports.length+9*table.length+18) (ctl .factorLoop)
      (view index (true::frame ports (frame table tail)) [] [] history factors occurrences) (ctl .portLoop)
      (view index tail ports [] history factors occurrences) :=by
  have h0:=pop_run .factorLoop (ctl .abort) (ctl .finish) (ctl .portsField) (aux .reader)
    (view index (true::frame ports (frame table tail)) [] [] history factors occurrences)
    (true::frame ports (frame table tail)) rfl rfl
  change Runs program 1 (ctl .factorLoop) _ (ctl .portsField)
    (Function.update (view index (true::frame ports (frame table tail)) [] [] history factors occurrences)
      (aux .reader) (frame ports (frame table tail))) at h0
  rw [view_reader] at h0
  have h1:=field_call .ports .portsField .portsValid rfl (view index (frame ports (frame table tail)) [] [] history factors occurrences)
    ports (frame table tail) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (view index (frame ports (frame table tail)) [] [] history factors occurrences)
      (aux .reader) (frame table tail)) (aux .ports) ports) (aux .valid) [true]) at h1
  rw [view_reader,view_ports] at h1
  have h2:=pop_run .portsValid (ctl .abort) (ctl .abort) (ctl .tableField) (aux .valid)
    (Function.update (view index (frame table tail) ports [] history factors occurrences) (aux .valid) [true]) [true] rfl rfl
  change Runs program 1 (ctl .portsValid) _ (ctl .tableField)
    (Function.update (Function.update (view index (frame table tail) ports [] history factors occurrences) (aux .valid) [true]) (aux .valid) []) at h2
  rw [clear_valid] at h2
  have h3:=field_call .table .tableField .tableValid rfl (view index (frame table tail) ports [] history factors occurrences)
    table tail rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (view index (frame table tail) ports [] history factors occurrences)
      (aux .reader) tail) (aux .table) table) (aux .valid) [true]) at h3
  rw [view_reader] at h3
  have h4:=pop_run .tableValid (ctl .abort) (ctl .abort) (ctl .clearTable) (aux .valid)
    (Function.update (Function.update (view index tail ports [] history factors occurrences) (aux .table) table) (aux .valid) [true])
    [true] rfl rfl
  change Runs program 1 (ctl .tableValid) _ (ctl .clearTable)
    (Function.update (Function.update (Function.update (view index tail ports [] history factors occurrences)
      (aux .table) table) (aux .valid) [true]) (aux .valid) []) at h4
  rw [clear_table_valid] at h4
  have h5:=drain_loop .clearTable (ctl .portLoop) (aux .table) rfl
    (Function.update (view index tail ports [] history factors occurrences) (aux .table) table) table rfl
  rw [clear_table] at h5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  have hc:1+(8*ports.length+7)+1+(8*table.length+7)+1+(table.length+1)=8*ports.length+9*table.length+18:=by omega
  rw [hc] at h
  exact h
/-- The final actual false factor-vector tag is consumed, rather than supplied as a factor-count answer. -/
theorem factors_end (index:I.Stack→List Bool) (history factors occurrences:List Bool) :
    Runs program 1 (ctl .factorLoop) (view index [false] [] [] history factors occurrences) (ctl .finish)
      (view index [] [] [] history factors occurrences) :=by
  have h:=pop_run .factorLoop (ctl .abort) (ctl .finish) (ctl .portsField) (aux .reader)
    (view index [false] [] [] history factors occurrences) [false] rfl rfl
  rw [view_reader] at h
  exact h
end RiemannGaussian.SemiprimeD1StackNetworkRowsRecords
