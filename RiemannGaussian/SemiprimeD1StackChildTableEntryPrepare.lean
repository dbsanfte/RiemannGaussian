/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryContexts
import RiemannGaussian.SemiprimeD1StackChildTableEntryBackend
import RiemannGaussian.SemiprimeD1StackChildTableEntryRows
/-! # Actual cached-context ready path: paid rank/order/table copies and real reads -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryPrepare
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackChildTableEntryFields SemiprimeD1StackChildTableEntryRows
open SemiprimeD1StackChildTableEntryBackend SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Exact acquired unary port vector, kept as a source word and really copied before gather. -/
def orderTape (order:List Nat):List Bool:=vectorBits (order.map unary)
/-- Exact raw gathered assignment, including repeats and physical out-of-range defaults. -/
def gathered (assignment:List Bool) (order:List Nat):List Bool:=SemiprimeD1StackBitGather.values assignment (order.map unary)
/-- The real gather's stopped bits are exactly the original cached-order gather. -/
theorem gathered_original (assignment:List Bool) (order:List Nat):
    gathered assignment order=(SemiprimeD1ChildTableCopy.gather assignment order).value:=by
  simp only [gathered,SemiprimeD1StackBitGather.values,List.map_map,Function.comp_def,unary,List.length_replicate,
    SemiprimeD1ChildTableCopy.gather_value]
/-- Exact current integer coefficient vector acquired by the real parent-tree source. -/
def selected {d:Nat} (table:SemiprimeD1TensorTables.Table d) (assignment:List Bool) (order:List Nat):List (List Bool):=
  (SemiprimeD1TensorTables.lookup table (gathered assignment order)).words
/-- Positive actual context rank contains a true marker; no decoded-rank advice is used by the source. -/
theorem unary_positive (n:Nat) (hp:0<n):unary n=true::unary (n-1):=by cases n <;> first | omega | rfl
/-- A literal gather input update preserves its assignment and all other5 words. -/
theorem gather_input (assignment path xs:List Bool):
    Function.update (G.contents [] assignment [] [] [] path) .input xs=G.contents xs assignment [] [] [] path:=by
  funext k;cases k <;> rfl
/-- A literal serialized-table copy writes only the real lookup input. -/
theorem tree_input (reader xs:List Bool):
    Function.update (T.contents [] [] [] [] reader) .input xs=T.contents xs [] [] [] reader:=by
  funext k;cases k <;> rfl
/-- Sum of the SAME actual two positive-rank peeks, five copies, gather and tree call caps. -/
def budget {d:Nat} (oldAxes newAxes:List Nat) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):Nat:=
  2+(5*(unary oldAxes.prod).length+4)+(5*(unary newAxes.prod).length+4)+(5*(orderTape order).length+4)+
    (SemiprimeD1StackGatherBytecode.budget assignment.length (orderTape order).length+1)+
    (5*(tape table).length+4)+(SemiprimeD1StackTreeBytecode.budget (tape table).length+1)+
    (5*(vectorBits (selected table assignment order)).length+4)
/-- SAME ready path obtains both counters, actual ordered assignment, actual parent value and paid parentEntry cache without replaying context acquisition. -/
theorem prepare_run {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):
    ∃q ≤ budget oldAxes newAxes table order assignment,Runs program q (.local .ready)
      (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment).data (.local .header)
      (state (Context.finalData oldAxes oldp) (Context.finalData newAxes newp) assignment ((gathered assignment order).drop d)
        (tape table) (orderTape order) (vectorBits (selected table assignment order)) (vectorBits (selected table assignment order))
        (unary oldAxes.prod) (unary newAxes.prod) []):=by
  let old:=Context.finalData oldAxes oldp
  let child:=Context.finalData newAxes newp
  let g0:=G.contents [] assignment [] [] [] []
  let t0:=T.contents [] [] [] [] []
  let r0:=scalarBank [] []
  let w0:=loopWords (tape table) (orderTape order) [] [] [] []
  have h0:=peek_run .ready (.local .abort) (.local .abort) (.local .newPositive) (context false J.rankCache)
    (bank old child g0 t0 r0 (words w0)) (true::unary (oldAxes.prod-1)) rfl (unary_positive _ ho)
  have h1:=peek_run .newPositive (.local .abort) (.local .abort) (.local .copyOldRank) (context true J.rankCache)
    (bank old child g0 t0 r0 (words w0)) (true::unary (newAxes.prod-1)) rfl (unary_positive _ hn)
  have h2:=copy_call .oldRank .copyOldRank .copyNewRank rfl (bank old child g0 t0 r0 (words w0)) (unary oldAxes.prod) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank old child g0 t0 r0 (words w0)) (aux .oldRemaining) (unary oldAxes.prod++[])) at h2
  rw [List.append_nil,update_aux,words_update] at h2
  let w1:Words:={w0 with oldRemaining:=unary oldAxes.prod}
  have h3:=copy_call .newRank .copyNewRank .copyOrder rfl (bank old child g0 t0 r0 (words w1)) (unary newAxes.prod) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank old child g0 t0 r0 (words w1)) (aux .remaining) (unary newAxes.prod++[])) at h3
  rw [List.append_nil,update_aux,words_update] at h3
  let w2:Words:={w1 with remaining:=unary newAxes.prod}
  have h4:=copy_call .order .copyOrder .gather rfl (bank old child g0 t0 r0 (words w2)) (orderTape order) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank old child g0 t0 r0 (words w2)) (gather .input) (orderTape order++[])) at h4
  rw [List.append_nil,update_gather,gather_input] at h4
  obtain ⟨q5,hq5,h5⟩:=gather_call assignment (order.map unary) old child t0 r0 (words w2)
  let path:=gathered assignment order
  let g1:=G.contents [] assignment [] [] [] path
  have h6:=copy_call .table .copyTable .lookup rfl (bank old child g1 t0 r0 (words w2)) (tape table) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank old child g1 t0 r0 (words w2)) (treeAllocation .input) (tape table++[])) at h6
  rw [List.append_nil,update_tree,tree_input] at h6
  obtain ⟨q7,hq7,h7⟩:=tree_call table path assignment old child r0 (words w2)
  let ws:=selected table assignment order
  let g2:=G.contents [] assignment [] [] [] (path.drop d)
  let t2:=T.contents [] [] [] [] (vectorBits ws)
  have h8:=copy_call .entry .copyEntry .header rfl (bank old child g2 t2 r0 (words w2)) (vectorBits ws) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank old child g2 t2 r0 (words w2)) (aux .parentEntry) (vectorBits ws++[])) at h8
  rw [List.append_nil,update_aux,words_update] at h8
  have h:=join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  refine ⟨_,?_,h⟩
  unfold budget
  dsimp only [orderTape,ws] at hq5 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryPrepare
