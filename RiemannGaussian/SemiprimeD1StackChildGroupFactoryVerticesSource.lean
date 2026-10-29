/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopView
/-! # Actual complete owner/factor marker acquisition and final scope/order reversal
Both retained marker words are physically copied. Every byte drives the real
whole-vertex loop, followed by two paid reversals of its actual row logs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Loop
export SemiprimeD1StackChildGroupFactoryVerticesLoop
  (popped popped_ready result timeBound source_trace)
end Loop
namespace Points
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end Points
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready)
end Body
namespace View
export SemiprimeD1StackChildGroupFactoryVerticesLoopView
  (scopeRows orderRows result_vertexHistory result_factorHistory result_other)
end View
namespace BodyView
export SemiprimeD1StackChildGroupFactoryVertexBodyView (Protected)
end BodyView
/-- Actual two preserving marker copies prepend factors to the copied owners. -/
def copied (before:Stack→List Bool) (owners factors:List Bool):Stack→List Bool:=
  Function.update before (aux .vertexTodo) (factors++owners)
/-- Whole physical bank after all actual original-vertex iterations. -/
def loopBank (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Stack→List Bool:=
  Loop.result (factors++owners) (copied before owners factors) points buckets key
/-- Actual bank after the paid final chronological scope reversal. -/
def scopeDone (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Stack→List Bool:=
  Function.update (Function.update (loopBank before owners factors points buckets key) (aux .vertexHistory) [])
    (aux .leftPorts) (View.scopeRows (factors++owners) buckets key++[false])
/-- Whole actual output bank after both final stream reversals. -/
def result (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Stack→List Bool:=
  Function.update (Function.update (scopeDone before owners factors points buckets key) (aux .factorHistory) [])
    (aux .orders) (View.orderRows (factors++owners) points buckets key++[false])
/-- Own whole-loop clock including both marker copies and chronological reversals. -/
def timeBound (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Nat:=
  (5*owners.length+4)+(5*factors.length+4)+
    Loop.timeBound (factors++owners) (copied before owners factors) points buckets key+
    1+(2*(View.scopeRows (factors++owners) buckets key).length+3)+
    1+(2*(View.orderRows (factors++owners) points buckets key).length+3)
/-- Whole actual source from the first marker copy to the six-field final frame entry. -/
theorem source_trace (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool)
    (ho:before (aux .owners)=owners) (hf:before (aux .factors)=factors)
    (ht:before (aux .vertexTodo)=[]) (hc:before (aux .copyScratch)=[])
    (hp:before (aux .oldEndpoints)=Points.records points)
    (hb:before (aux .buckets)=SemiprimeD1StackChildGroupFactoryLeftPortsLoop.records buckets)
    (hk:before (aux .vertexKey)=key)
    (hr:Body.Ready before)
    (hvh:before (aux .vertexHistory)=[]) (hfh:before (aux .factorHistory)=[])
    (hl:before (aux .leftPorts)=[]) (hord:before (aux .orders)=[]):
    ∃t≤timeBound before owners factors points buckets key,
      Runs program t (.local 9 2) before (.local 15 7) (result before owners factors points buckets key):=by
  have h0:=copy_call 0 (.local 9 2) (.local 9 3) rfl before owners [] ho ht hc
  simp only [List.append_nil] at h0
  let first:=Function.update before (aux .vertexTodo) owners
  have h1:=copy_call 1 (.local 9 3) (.local 9 4) rfl first factors owners
    (by simpa [first,aux,copyStack,copyPorts] using hf) (Function.update_self _ _ _)
    (by simpa [first,aux,copyStack,copyPorts] using hc)
  change Runs program _ _ first _ (Function.update first (aux .vertexTodo) (factors++owners)) at h1
  have hcopy:Function.update first (aux .vertexTodo) (factors++owners)=copied before owners factors:=by
    exact Function.update_idem _ _ _
  rw [hcopy] at h1
  have hready:Body.Ready (copied before owners factors):=Loop.popped_ready before (factors++owners) hr
  obtain ⟨x,hx,h2⟩:=Loop.source_trace (factors++owners) (copied before owners factors) points buckets key rfl
    (by simpa [copied,aux] using hp) (by simpa [copied,aux] using hb)
    (by simpa [copied,aux] using hk) hready
  let bank:=loopBank before owners factors points buckets key
  have hv:bank (aux .vertexHistory)=(View.scopeRows (factors++owners) buckets key).reverse:=by
    dsimp only [bank,loopBank]
    rw [View.result_vertexHistory]
    simpa [copied,aux] using congrArg (fun tail=>(View.scopeRows (factors++owners) buckets key).reverse++tail) hvh
  have hfo:bank (aux .factorHistory)=(View.orderRows (factors++owners) points buckets key).reverse:=by
    dsimp only [bank,loopBank]
    rw [View.result_factorHistory]
    simpa [copied,aux] using congrArg (fun tail=>(View.orderRows (factors++owners) points buckets key).reverse++tail) hfh
  have retained (k:Stack) (hprotect:BodyView.Protected k) (hne:k≠aux .vertexTodo):bank k=before k:=by
    dsimp only [bank,loopBank]
    rw [View.result_other _ _ _ _ _ _ hprotect hne]
    exact Function.update_of_ne hne _ _
  have hleft:bank (aux .leftPorts)=[]:=(retained _ (by
    constructor
    all_goals first | (intro j;fin_cases j <;> decide) | decide) (by decide)).trans hl
  have horders:bank (aux .orders)=[]:=(retained _ (by
    constructor
    all_goals first | (intro j;fin_cases j <;> decide) | decide) (by decide)).trans hord
  let seeded:=Function.update bank (aux .leftPorts) [false]
  have h3:=push_run (.local 15 3) (.local 15 4) (aux .leftPorts) false bank rfl
  rw [hleft] at h3
  have h4:=reverse_call 14 (.local 15 4) (.local 15 5) rfl seeded
    (View.scopeRows (factors++owners) buckets key).reverse [false]
    (by simpa [seeded,aux,reverseStack,reversePorts] using hv) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h4
  change Runs program _ _ seeded _ (Function.update (Function.update seeded (aux .vertexHistory) [])
    (aux .leftPorts) (View.scopeRows (factors++owners) buckets key++[false])) at h4
  have hs:Function.update (Function.update seeded (aux .vertexHistory) []) (aux .leftPorts)
      (View.scopeRows (factors++owners) buckets key++[false])=scopeDone before owners factors points buckets key:=by
    dsimp only [seeded,scopeDone,bank]
    rw [Function.update_comm (by decide:aux .leftPorts≠aux .vertexHistory),Function.update_idem]
  rw [hs] at h4
  let left:=scopeDone before owners factors points buckets key
  have hf':left (aux .factorHistory)=(View.orderRows (factors++owners) points buckets key).reverse:=by
    simpa [left,scopeDone,aux,bank] using hfo
  have ho':left (aux .orders)=[]:=by simpa [left,scopeDone,aux,bank] using horders
  let seededOrder:=Function.update left (aux .orders) [false]
  have h5:=push_run (.local 15 5) (.local 15 6) (aux .orders) false left rfl
  rw [ho'] at h5
  have h6:=reverse_call 15 (.local 15 6) (.local 15 7) rfl seededOrder
    (View.orderRows (factors++owners) points buckets key).reverse [false]
    (by simpa [seededOrder,aux,reverseStack,reversePorts] using hf') (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h6
  change Runs program _ _ seededOrder _ (Function.update (Function.update seededOrder (aux .factorHistory) [])
    (aux .orders) (View.orderRows (factors++owners) points buckets key++[false])) at h6
  have hs':Function.update (Function.update seededOrder (aux .factorHistory) []) (aux .orders)
      (View.orderRows (factors++owners) points buckets key++[false])=result before owners factors points buckets key:=by
    dsimp only [seededOrder,result,left]
    rw [Function.update_comm (by decide:aux .orders≠aux .factorHistory),Function.update_idem]
  rw [hs'] at h6
  refine ⟨(5*owners.length+4)+(5*factors.length+4)+x+1+
      (2*(View.scopeRows (factors++owners) buckets key).length+3)+1+
      (2*(View.orderRows (factors++owners) points buckets key).length+3),?_,?_⟩
  · dsimp only [timeBound];omega
  · have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 h6)))))
    simpa only [Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSource
