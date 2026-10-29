/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductValue
/-! # Closed actual startup and whole original assignment-product execution -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductExecution
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProductMoves SemiprimeD1StackVertexProductSetup
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Explicit sum of actual startup traces and the reached record-loop bound. -/
def preparedBudget (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values) : ℕ :=
  let unit:=vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words
  let ready:=Function.update (Function.update (Function.update (Function.update v .result unit)
    .product unit) .result []) .reader (records vertices)
  SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)+1+
    (5*unit.length+4)+(unit.length+1)+(5*(v .vertices).length+4)+
    SemiprimeD1StackVertexProductLoop.loopBudget ctx vertices ready (SemiprimeD1JetAffineCoefficient.one ctx).words

/-- Real literal unit, record-cache copy and all actual record rounds. This
internal prepared entry is used only after actual context acquisition. -/
theorem prepared_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values)
    (hvertices : v .vertices=records vertices)
    (hreader : v .reader=[]) (hleft : v .left=[]) (hprod : v .product=[])
    (hports : v .ports=[]) (htable : v .table=[]) (hvalid : v .valid=[]) (hout : v .result=[])
    (haxes : v .axes=vectorBits (ctx.axes.map unary))
    (hw : (v .width).length=ctx.precision) (hr : v .rank=unary ctx.rank) :
    ∃ m ≤ preparedBudget ctx vertices v, Runs program m .prepared (data v) .done
      (data (Function.update v .product
        (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices (v .assignment)).words))) := by
  let unit:=vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words
  let v1:=Function.update v .result unit
  let v2:=Function.update v1 .product unit
  let v3:=Function.update v2 .result []
  let v4:=Function.update v3 .reader (records vertices)
  have h1:=unit_call ctx v hw (by simp [hr,unary]) hleft hprod hout
  have h2 : Runs program (5*unit.length+4) .unitDone (data v1) .clearUnitOut (data v2) := by
    simpa [v1,v2,copySource,copyTarget,hprod] using copy_call v1 false .unitDone .clearUnitOut rfl
  have h3:=drain_current v2 .result .clearUnitOut .copyVertices rfl
  have h4 : Runs program (5*(v .vertices).length+4) .copyVertices (data v3) .vertexTag (data v4) := by
    simpa [v4,v3,v2,v1,copySource,copyTarget,hvertices,hreader] using copy_call v3 true .copyVertices .vertexTag rfl
  obtain ⟨n,hnb,hn⟩:=SemiprimeD1StackVertexProductLoop.loop_run ctx hp vertices v4
    (SemiprimeD1JetAffineCoefficient.one ctx).words (by simp [v4])
    (by simpa [v4,v3,v2,v1] using hleft) (by simpa [v4,v3,v2,v1] using hports)
    (by simpa [v4,v3,v2,v1] using htable) (by simpa [v4,v3,v2,v1] using hvalid)
    (by simp [v4,v3]) (by simp [v4,v3,v2,unit])
    (by simpa [v4,v3,v2,v1] using haxes) (by simpa [v4,v3,v2,v1] using hw)
    (by simpa [v4,v3,v2,v1] using hr)
  have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h3
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h4
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc hn
  refine ⟨SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)+1+
    (5*unit.length+4)+((v2 .result).length+1)+(5*(v .vertices).length+4)+n,?_,?_⟩
  · simpa only [preparedBudget,←show v4=Function.update (Function.update (Function.update
        (Function.update v .result unit) .product unit) .result []) .reader (records vertices) from rfl,
      v2,v1,Function.update_of_ne (by decide : Slot.result ≠ .product),Function.update_self] using
      Nat.add_le_add_left hnb (SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)+1+
        (5*unit.length+4)+(unit.length+1)+(5*(v .vertices).length+4))
  · convert hc using 1
    apply congrArg data
    funext s
    cases s <;> simp [v4,v3,v2,v1,SemiprimeD1StackVertexProductValue.folded_original ctx hp,
      hreader,hout]

/-- Whole actual prepared procedure, with literal return/halt and exact cleared
workspace, for callers that already executed the context supplier. -/
theorem prepared_source (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values)
    (hvertices : v .vertices=records vertices)
    (hreader : v .reader=[]) (hleft : v .left=[]) (hprod : v .product=[])
    (hports : v .ports=[]) (htable : v .table=[]) (hvalid : v .valid=[]) (hout : v .result=[])
    (haxes : v .axes=vectorBits (ctx.axes.map unary))
    (hw : (v .width).length=ctx.precision) (hr : v .rank=unary ctx.rank) :
    ∃ m ≤ preparedBudget ctx vertices v+1,
      SemiprimeD1StackCalls.run program m
        (⟨some .prepared,none,none,data v,[]⟩:SemiprimeD1StackCalls.State Stack Label)=
      some (⟨none,none,none,data (Function.update v .product
        (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices (v .assignment)).words)),[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,h⟩:=prepared_run ctx hp vertices v hvertices hreader hleft hprod hports htable hvalid hout haxes hw hr
  obtain ⟨finish,hfinish,hout⟩:=h [] (⟨some .prepared,none,none,data v,[]⟩:
    SemiprimeD1StackCalls.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hh:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl _ [] finish hout
  refine ⟨m+1,Nat.add_le_add_right hm 1,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

/-- Original physical input and acquired context caches at the clean product exit. -/
def finalData (ctx : SemiprimeD1JetAxes.Context) (precisionBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (assignment : List Bool) : Stack→List Bool :=
  data (values (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment
    (unary ctx.rank) (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
    [] (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices assignment).words)
    [] [] [] [] [])

/-- Complete original-input transition bound, retaining context acquisition and
all actual reached product-round bounds. -/
def sourceBudget (ctx : SemiprimeD1JetAxes.Context) (precisionBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (assignment : List Bool) : ℕ :=
  let ready:=Function.update (Function.update
    (values (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment
      [] [] [] [] [] [] [] [] []) .rank (unary ctx.rank)) .width
      (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
  1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes precisionBits+1)^2+1+
    preparedBudget ctx vertices ready+1

/-- Closed actual execution from encoded original axes, binary precision, literal
vertex records and the physical assignment; no prepared rank or entry answer. -/
theorem source_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (precisionBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue precisionBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (assignment : List Bool) :
    ∃ m ≤ sourceBudget ctx precisionBits vertices assignment, SemiprimeD1StackCalls.run program m
      (initial (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment)=
      some (⟨none,none,none,finalData ctx precisionBits vertices assignment,[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  let v:=values (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment
    [] [] [] [] [] [] [] [] []
  let w:=Function.update (Function.update v .rank (unary ctx.rank)) .width
    (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
  obtain ⟨m,hmb,hm⟩:=context_call v ctx.axes hp rfl rfl rfl
  have hm' : Runs program m .start (data v) .prepared (data w) := by
    simpa only [w,SemiprimeD1JetAxes.Context.rank,v,values,hprecision] using hm
  obtain ⟨n,hnb,hn⟩:=prepared_run ctx hp vertices w (by simp [w,v,values]) (by simp [w,v,values])
    (by simp [w,v,values]) (by simp [w,v,values]) (by simp [w,v,values]) (by simp [w,v,values])
    (by simp [w,v,values]) (by simp [w,v,values]) (by simp [w,v,values])
    (by simp [w,SemiprimeD1StackUnaryCounterExecution.markers]) (by simp [w])
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hm' hn
  have hi : (initial (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment).data=data v :=
    initial_data _ _ _ _
  obtain ⟨finish,hfinish,hout⟩:=hc []
    (initial (vectorBits (ctx.axes.map unary)) precisionBits (records vertices) assignment) ⟨rfl,hi,rfl⟩
  have hd : data (Function.update w .product
      (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices (w .assignment)).words))=
      finalData ctx precisionBits vertices assignment := by
    apply congrArg data
    funext s
    cases s <;> simp [w,v,values]
  rw [hd] at hout
  have hh:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl
    (finalData ctx precisionBits vertices assignment) [] finish hout
  refine ⟨m+n+1,?_,?_⟩
  · change m+n+1 ≤ 1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes precisionBits+1)^2+1+
        preparedBudget ctx vertices w+1
    simpa only [v,values] using Nat.add_le_add_right (Nat.add_le_add hmb hnb) 1
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

end RiemannGaussian.SemiprimeD1StackVertexProductExecution
