/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexOriginal
/-! # Whole physical vertex acquisition costs a fixed quadratic per assignment
The framing charge uses the semantic byte cap of the newly acquired table.
No elapsed child-clock is raised to a new power to bound an operand width.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexBounds
open SemiprimeD1StackChildLiftVertex SemiprimeD1StackChildLiftVertexOriginal
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace R
export SemiprimeD1StackChildLiftTableResources (resource resource_pos template_bytes)
end R
variable {d : ℕ}
/-- Same physically acquired resource as the actual whole table, with real unary port-ID words. -/
def resource (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ :=
  R.resource old extra oldp newp parent order (ports.map unary)
/-- Complete child table byte cap from original Good and positive extra axes alone. -/
theorem table_bytes (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (parent : SemiprimeD1TensorTables.Table d)
    (hg : SemiprimeD1TensorTables.Good old parent) (order ports : List ℕ) :
    (tape (vertex old extra newp parent order ports).table).length≤
      10*(resource old extra oldp newp parent order ports)^2*2^ports.length := by
  let r:=resource old extra oldp newp parent order ports
  have hr : 1≤r:=R.resource_pos old extra oldp newp parent order (ports.map unary)
  have hrank : (extra++old.axes).prod≤r := by
    dsimp [r,resource,R.resource,SemiprimeD1StackChildTableEntryBounds.resource]
    omega
  have hp : SemiprimeBitArithmetic.bitValue newp≤r := by
    dsimp [r,resource,R.resource,SemiprimeD1StackChildTableEntryBounds.resource]
    omega
  have hm:=Nat.mul_le_mul hrank (show 3*SemiprimeBitArithmetic.bitValue newp+4≤3*r+4 by omega)
  have hc : (extra++old.axes).prod*(3*SemiprimeBitArithmetic.bitValue newp+4)+3≤10*r^2 := by
    nlinarith only [hm,hr]
  have hg':=SemiprimeD1StackChildLiftTableMeaning.table_good old extra
    (SemiprimeBitArithmetic.bitValue newp) ports.length parent order hg he
  have ht:=SemiprimeD1TensorTables.storage_bound ⟨extra++old.axes,SemiprimeBitArithmetic.bitValue newp⟩ _ hg'
  have hb:=SemiprimeD1TensorTapeCodec.tape_le_storage (vertex old extra newp parent order ports).table
  have hsmall : (tape (vertex old extra newp parent order ports).table).length≤
      ((extra++old.axes).prod*(3*SemiprimeBitArithmetic.bitValue newp+4)+3)*2^ports.length := by
    change SemiprimeD1TensorTables.storage (vertex old extra newp parent order ports).table+1≤
      ((extra++old.axes).prod*(3*SemiprimeBitArithmetic.bitValue newp+4)+3)*2^ports.length at ht
    omega
  exact hsmall.trans (Nat.mul_le_mul_right _ hc)
/-- One fixed whole-source coefficient and degree before every original operand. -/
def polynomial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ :=
  10^24*(resource old extra oldp newp parent order ports)^2*2^ports.length
/-- Actual table source call plus both actual field frames have this SAME fixed quadratic clock. -/
theorem timeBound_le (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (parent : SemiprimeD1TensorTables.Table d)
    (hg : SemiprimeD1TensorTables.Good old parent) (order ports : List ℕ) :
    timeBound old extra oldp newp parent order ports≤polynomial old extra oldp newp parent order ports := by
  let r:=resource old extra oldp newp parent order ports
  let e:=2^ports.length
  have hr : 1≤r:=R.resource_pos old extra oldp newp parent order (ports.map unary)
  have he' : 1≤e:=Nat.one_le_pow _ _ (by decide : 1≤(2:ℕ))
  have hr2 : r≤r^2:=Nat.le_pow (by decide : 0<2)
  have hscale : r^2≤r^2*e:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he'
  have hscope : (SemiprimeD1StackVertexReadExecution.portTape ports).length≤r:=Nat.le_add_left _ _
  have hs:=hscope.trans (hr2.trans hscale)
  have h1:=hr.trans (hr2.trans hscale)
  have ht:=table_bytes old extra he oldp newp parent hg order ports
  change (tape (vertex old extra newp parent order ports).table).length≤10*r^2*e at ht
  rw [Nat.mul_assoc] at ht
  unfold polynomial
  rw [Nat.mul_assoc]
  change timeBound old extra oldp newp parent order ports≤10^24*(r^2*e)
  dsimp only [timeBound,B.polynomial,SemiprimeD1StackChildLiftTableBounds.polynomial]
  rw [List.length_map,Nat.mul_assoc]
  change 10^20*(r^2*e)+6*(tape (vertex old extra newp parent order ports).table).length+
    6*(SemiprimeD1StackVertexReadExecution.portTape ports).length+14≤10^24*(r^2*e)
  omega
/-- SAME actual136-role source, seven original operands, exact canonical record and closed own clock. -/
theorem source_run_bounded (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) :
    ∃t≤polynomial old extra oldp newp parent order ports,
      SemiprimeD1StackCalls.run program t (originalInitial old extra oldp newp parent order ports)=
        some (done old extra oldp newp parent order ports) := by
  obtain ⟨t,ht,hr⟩:=source_run old ho extra he oldp newp hp parent hg order ports
  exact ⟨t,ht.trans (timeBound_le old extra he oldp newp parent hg order ports),hr⟩
/-- The actual compiled finite machine has exactly this whole-source prepared entry and fixed clock. -/
noncomputable def machineSource (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (originalInitial old extra oldp newp parent order ports))
      (some (SemiprimeD1StackCalls.configuration (done old extra oldp newp parent order ports)))
      (polynomial old extra oldp newp parent order ports) := by
  apply SemiprimeD1StackCalls.evalsCorrect scopeInput (aux .record) (.local .start) program
  let h:=source_run_bounded old ho extra he oldp newp hp parent hg order ports
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackChildLiftVertexBounds
