/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTree

/-! # Actual literal Boolean leaf writes and recursive tree control steps -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBooleanTreeParts
open SemiprimeD1StackBooleanTree SemiprimeD1StackProcedureTrace
open SemiprimeD1BooleanTreeStream (leafBytes)
/-- Literal emitted bit at one fixed finite codec location. -/
def emitBit (b : Bool) (i : Fin 6) : Bool := if i=0 then false else if i=1 then true else if i=2 ∨ i=3 then b else false
/-- Next fixed finite codec location; zero leaves have four actual pushes. -/
def emitNext (b : Bool) (i : Fin 6) : Label :=
  if i=0 then .emit b 1 else if i=1 then .emit b 2 else if i=2 then .emit b 3
  else if i=3 then (if b then .emit b 4 else .returnPC) else if i=4 then .emit b 5 else .returnPC
/-- One actual literal push changes only the physical reverse-history stack. -/
theorem emit_step (b : Bool) (i : Fin 6) (raw depth hist out : List Bool) :
    Runs program 1 (.emit b i) (store raw depth hist out) (emitNext b i)
      (store raw depth (emitBit b i::hist) out) := by
  apply one_base program (.emit b i) (emitNext b i) (.push .history (emitBit b i) (emitNext b i)) _ _
  · fin_cases i <;> cases b <;> rfl
  · rfl
  · funext k;cases k <;> rfl
/-- Complete real literal leaf payload, including EVERY codec/vector/end byte. -/
theorem emit_run (b : Bool) (raw depth hist out : List Bool) :
    Runs program (leafBytes b).length (.emit b 0) (store raw depth hist out) .returnPC
      (store raw depth ((leafBytes b).reverse++hist) out) := by
  cases b with
  | false=>
    have h0:=emit_step false 0 raw depth hist out
    have h1:=emit_step false 1 raw depth (false::hist) out
    have h2:=emit_step false 2 raw depth (true::false::hist) out
    have h3:=emit_step false 3 raw depth (false::true::false::hist) out
    exact runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  | true=>
    have h0:=emit_step true 0 raw depth hist out
    have h1:=emit_step true 1 raw depth (false::hist) out
    have h2:=emit_step true 2 raw depth (true::false::hist) out
    have h3:=emit_step true 3 raw depth (true::true::false::hist) out
    have h4:=emit_step true 4 raw depth (true::true::true::false::hist) out
    have h5:=emit_step true 5 raw depth (false::true::true::true::false::hist) out
    exact runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5
/-- EOF on actual depth enters the actual scalar-entry read. -/
theorem visit_leaf (raw hist out : List Bool) :
    Runs program 1 .visit (store raw [] hist out) .read (store raw [] hist out) := by
  apply one_base program .visit .read (.pop .depth .read (.node false) (.node true)) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl
/-- Actual scalar-entry read, including EOF/default false and exact source suffix. -/
theorem read_leaf (raw hist out : List Bool) :
    Runs program 1 .read (store raw [] hist out) (.emit (raw.head?.getD false) 0) (store raw.tail [] hist out) := by
  apply one_base program .read (.emit (raw.head?.getD false) 0)
    (.pop .input (.emit false 0) (.emit false 0) (.emit true 0)) _ _ rfl
  · cases raw with
    | nil=>rfl
    | cons b raw=>cases b <;> rfl
  · funext k;cases k <;> rfl
/-- One actual depth marker is consumed and held only as a finite Boolean label. -/
theorem visit_node (b : Bool) (raw depth hist out : List Bool) :
    Runs program 1 .visit (store raw (b::depth) hist out) (.node b) (store raw depth hist out) := by
  apply one_base program .visit (.node b) (.pop .depth .read (.node false) (.node true)) _ _ rfl
  · cases b <;> rfl
  · funext k;cases k <;> rfl
/-- The original branch marker is physically pushed before either actual child. -/
theorem push_node (b : Bool) (raw depth hist out : List Bool) :
    Runs program 1 (.node b) (store raw depth hist out) (.left b) (store raw depth (true::hist) out) := by
  apply one_base program (.node b) (.left b) (.push .history true (.left b)) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl
/-- The EXACT arbitrary original marker bit is restored after both children. -/
theorem restore_node (b : Bool) (raw depth hist out : List Bool) :
    Runs program 1 (.restore b) (store raw depth hist out) .returnPC (store raw (b::depth) hist out) := by
  apply one_base program (.restore b) .returnPC (.push .depth b .returnPC) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackBooleanTreeParts
