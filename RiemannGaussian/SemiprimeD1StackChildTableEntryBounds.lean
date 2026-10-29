/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryExecution
import RiemannGaussian.SemiprimeD1StackChildTableEntryLoopCost
/-! # Own whole/ready polynomial in actual source words and acquired VALUE caches
Ranks and precision VALUES below name the sizes of actually acquired unary
caches. No polynomial in binary precision bytes alone is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryBounds
open SemiprimeD1StackChildTableEntryEncoding SemiprimeD1StackChildTableEntryPrepare
open SemiprimeD1StackChildTableEntryExecution SemiprimeD1StackChildTableEntryLoopCost
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Seven actual input word lengths, actual acquired old/new rank-marker counts and actual acquired precision-marker counts. -/
def resource {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d)
    (order:List Nat) (assignment:List Bool):Nat:=
  (tape table).length+(orderTape order).length+assignment.length+
    (vectorBits (oldAxes.map unary)).length+(vectorBits (newAxes.map unary)).length+oldp.length+newp.length+
    oldAxes.prod+newAxes.prod+bitValue oldp+bitValue newp+1
/-- Every coordinate returned by the actual tree read is a literal physical slice of the supplied parent table tape. -/
theorem selected_length {d:Nat} (table:SemiprimeD1TensorTables.Table d) (assignment:List Bool) (order:List Nat):
    (vectorBits (selected table assignment order)).length  ≤ (tape table).length:=
  SemiprimeD1TensorTapeTreeBounds.selected_length_le table (gathered assignment order)
/-- Actual gather output count is exactly the physically encoded requested-port count, repeats included. -/
theorem gathered_length (assignment:List Bool) (order:List Nat):(gathered assignment order).length=order.length:=by
  simp only [gathered,SemiprimeD1StackBitGather.values,List.length_map]
/-- Own ready copies and real backend source calls have a fixed quadratic bound. -/
theorem prepare_budget_le {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):
    SemiprimeD1StackChildTableEntryPrepare.budget oldAxes newAxes table order assignment  ≤
      1000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  let S:=resource oldAxes newAxes oldp newp table order assignment
  have hS:1 ≤ S:=by dsimp [S,resource];omega
  have ht:(tape table).length ≤ S:=by dsimp [S,resource];omega
  have ho:(orderTape order).length ≤ S:=by dsimp [S,resource];omega
  have ha:assignment.length ≤ S:=by dsimp [S,resource];omega
  have hr:oldAxes.prod+newAxes.prod ≤ S:=by dsimp [S,resource];omega
  have hv: (vectorBits (selected table assignment order)).length ≤ S:=(selected_length table assignment order).trans ht
  have h2:S ≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have hg:SemiprimeD1StackGatherBytecode.budget assignment.length (orderTape order).length ≤ 200*S^2:=by
    unfold SemiprimeD1StackGatherBytecode.budget SemiprimeD1StackBitGatherBounds.budget
    have hp:=Nat.mul_le_mul (show 5*(3*assignment.length+8) ≤ 55*S by omega)
      (show (orderTape order).length+1 ≤ 2*S by omega)
    nlinarith only [hp]
  change SemiprimeD1StackChildTableEntryPrepare.budget oldAxes newAxes table order assignment ≤1000*S^2
  unfold SemiprimeD1StackChildTableEntryPrepare.budget SemiprimeD1StackTreeBytecode.budget
  simp only [unary,List.length_replicate]
  omega
/-- The SAME actual coefficient-loop cap is quadratic, including all rank-driven zero words and complete output reversal. -/
theorem loop_budget_le {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod ≤ newAxes.prod):
    SemiprimeD1StackChildTableEntryLoop.timeBound newp (selected table assignment order)
      (newAxes.prod-oldAxes.prod) ((gathered assignment order).drop d)  ≤
      10000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  let S:=resource oldAxes newAxes oldp newp table order assignment
  let ws:=selected table assignment order
  let z:=newAxes.prod-oldAxes.prod
  have hS:1 ≤ S:=by dsimp [S,resource];omega
  have h2:S ≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have ht:(tape table).length ≤ S:=by dsimp [S,resource];omega
  have ho:(orderTape order).length ≤ S:=by dsimp [S,resource];omega
  have hn:newAxes.prod ≤ S:=by dsimp [S,resource];omega
  have hp:newp.length+bitValue newp+1 ≤ S:=by dsimp [S,resource];omega
  have hv:(vectorBits ws).length ≤ S:=(selected_length table assignment order).trans ht
  have hc:ws.length+z=newAxes.prod:=by dsimp only [ws,z];omega
  have hmass:(ws.map List.length).sum ≤ S:=by have h:=SemiprimeD1TensorTapeCodec.vectorBits_length ws;omega
  have hold:=old_budget_le newp ws
  have hprod:=Nat.mul_le_mul (show ws.length ≤ S by omega) hp
  have hold':Old.budget newp ws ≤ 500*S^2:=by nlinarith only [hold,hprod,hmass,h2,hS]
  have hz:=zero_budget_le newp z
  have hzprod:=Nat.mul_le_mul (show z ≤ S by omega) hp
  have hz':Zero.budget newp z ≤ 300*S^2:=by nlinarith only [hz,hzprod,hS]
  have hh:=lifted_history_length newp ws z
  have hhprod:=Nat.mul_le_mul (show bitValue newp+1 ≤ S by omega) (show ws.length+z ≤ S by omega)
  have hh':(history (lifted newp ws z)).length ≤ 2*S^2:=by nlinarith only [hh,hhprod]
  have hpath:((gathered assignment order).drop d).length ≤ S:=by
    have hlen:=gathered_length assignment order
    have hcount:=SemiprimeD1StackBitGatherBounds.count_le_tape (order.map unary)
    have hcount':order.length ≤ (orderTape order).length:=by simpa only [List.length_map,orderTape] using hcount
    simp only [List.length_drop]
    omega
  change SemiprimeD1StackChildTableEntryLoop.timeBound newp ws z _ ≤ 10000*S^2
  unfold SemiprimeD1StackChildTableEntryLoop.timeBound
  omega
/-- Complete SAME ready-source clock is bounded without a context replay or external report. -/
theorem readyBound_le {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod ≤ newAxes.prod):
    readyBound oldAxes newAxes newp table order assignment  ≤ 1000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  have h0:=prepare_budget_le oldAxes newAxes oldp newp table order assignment
  have h1:=loop_budget_le oldAxes newAxes oldp newp table order assignment hshape hrank
  unfold readyBound
  omega
/-- Every actual unary-axis field is counted by its literal vector bytes, including all empty lists. -/
theorem axes_count (axes:List Nat):axes.length ≤ (vectorBits (axes.map unary)).length:=by
  have h:=SemiprimeD1StackBitGatherBounds.count_le_tape (axes.map unary)
  simpa only [List.length_map] using h
/-- Both actual context source budgets are quadratic in the actual VALUE-aware resource. -/
theorem acquisition_budget_le {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):
    SemiprimeD1StackChildTableEntryAcquisition.budget oldAxes newAxes oldp newp  ≤
      20000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  let S:=resource oldAxes newAxes oldp newp table order assignment
  have hS:1 ≤ S:=by dsimp [S,resource];omega
  have hOld:=axes_count oldAxes
  have hNew:=axes_count newAxes
  have hoR:SemiprimeD1StackJetContextBounds.resource oldAxes oldp+1 ≤ 3*S:=by
    dsimp [SemiprimeD1StackJetContextBounds.resource,S,resource];omega
  have hnR:SemiprimeD1StackJetContextBounds.resource newAxes newp+1 ≤ 3*S:=by
    dsimp [SemiprimeD1StackJetContextBounds.resource,S,resource];omega
  have h0:SemiprimeD1StackJetContextCorrectness.budget oldAxes oldp ≤ 9000*S^2:=by
    have h:=SemiprimeD1StackJetContextBounds.budget_polynomial oldAxes ho oldp
    have hp:=Nat.pow_le_pow_left hoR 2
    nlinarith only [h,hp]
  have h1:SemiprimeD1StackJetContextCorrectness.budget newAxes newp ≤ 9000*S^2:=by
    have h:=SemiprimeD1StackJetContextBounds.budget_polynomial newAxes hn newp
    have hp:=Nat.pow_le_pow_left hnR 2
    nlinarith only [h,hp]
  change SemiprimeD1StackChildTableEntryAcquisition.budget oldAxes newAxes oldp newp ≤20000*S^2
  unfold SemiprimeD1StackChildTableEntryAcquisition.budget
  have h2:1 ≤ S^2:=by nlinarith only [hS]
  omega
/-- Complete actual whole seven-input source has one fixed quadratic cap, fully paying rank and precision VALUE materialization. -/
theorem wholeBound_le {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod ≤ newAxes.prod):
    wholeBound oldAxes newAxes oldp newp table order assignment  ≤
      100000000*(resource oldAxes newAxes oldp newp table order assignment)^2:=by
  have h0:=acquisition_budget_le oldAxes newAxes ho hn oldp newp table order assignment
  have h1:=readyBound_le oldAxes newAxes oldp newp table order assignment hshape hrank
  unfold wholeBound
  omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryBounds
