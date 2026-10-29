/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinalFrames
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinish
/-! # Complete actual all-vertex scope/order/output/cleanup suffix
Starting at the actual post-bucket continuation, this source executes both
marker copies, all vertex queries/conversions, six output frames, exhaustive
115-role cleanup, the real success push and true halt. No result tape or
port-order permutation is provided as a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactorySuffix
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace V
export SemiprimeD1StackChildGroupFactoryVerticesSource (result timeBound source_trace)
end V
namespace Points
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end Points
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready)
end Body
namespace F
export SemiprimeD1StackChildGroupFactoryFinalFrames (result timeBound source_trace)
end F
namespace Halt
export SemiprimeD1StackChildGroupFactoryFinish (result timeBound source_run)
end Halt
/-- Exact stopped physical bank of the complete actual suffix. -/
def result (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Stack→List Bool:=
  Halt.result (F.result (V.result before owners factors points buckets key))
/-- Every actual loop, conversion, frame, drain and return is included. -/
def timeBound (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):Nat:=
  V.timeBound before owners factors points buckets key+
    F.timeBound (V.result before owners factors points buckets key)+
    Halt.timeBound (F.result (V.result before owners factors points buckets key))
/-- Actual copied/query bank boundaries, derived from the real complete loop. -/
theorem vertex_copyScratch (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool) (hr:Body.Ready before):
    V.result before owners factors points buckets key (aux .copyScratch)=[]:=by
  have h:=SemiprimeD1StackChildGroupFactoryVerticesLoopView.result_ready (factors++owners)
    (SemiprimeD1StackChildGroupFactoryVerticesSource.copied before owners factors) points buckets key
    (SemiprimeD1StackChildGroupFactoryVerticesLoop.popped_ready before (factors++owners) hr)
  have hc:=h.work (19:Fin 20) (by decide)
  simpa [V.result,SemiprimeD1StackChildGroupFactoryVerticesSource.scopeDone,
    SemiprimeD1StackChildGroupFactoryVerticesSource.loopBank,
    SemiprimeD1StackChildGroupFactoryOldPortsLoop.freshRole,aux] using hc
/-- Whole actual suffix source, with arbitrary real outer returns and transient flags. -/
theorem source_run (before:Stack→List Bool) (owners factors:List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool)
    (ho:before (aux .owners)=owners) (hf:before (aux .factors)=factors)
    (ht:before (aux .vertexTodo)=[]) (hc:before (aux .copyScratch)=[])
    (hp:before (aux .oldEndpoints)=Points.records points)
    (hb:before (aux .buckets)=Buckets.records buckets) (hk:before (aux .vertexKey)=key)
    (hr:Body.Ready before)
    (hvh:before (aux .vertexHistory)=[]) (hfh:before (aux .factorHistory)=[])
    (hl:before (aux .leftPorts)=[]) (hord:before (aux .orders)=[]):
    ∃t≤timeBound before owners factors points buckets key,∀frames (start:C.State Stack Label),
      At (.local 9 2) before frames start→
      C.run program t start=some (⟨none,none,none,result before owners factors points buckets key,frames⟩:C.State Stack Label):=by
  obtain ⟨x,hx,h0⟩:=V.source_trace before owners factors points buckets key ho hf ht hc hp hb hk hr hvh hfh hl hord
  have h1:=F.source_trace (V.result before owners factors points buckets key)
    (vertex_copyScratch _ _ _ _ _ _ hr)
  obtain ⟨y,hy,h2⟩:=Halt.source_run (F.result (V.result before owners factors points buckets key))
  refine ⟨x+F.timeBound (V.result before owners factors points buckets key)+y,?_,?_⟩
  · dsimp only [timeBound];omega
  · intro frames start hs
    obtain ⟨mid,hm,hat⟩:=(join h0 h1) frames start hs
    have hh:=h2 frames mid hat
    rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some]
    exact hh
end RiemannGaussian.SemiprimeD1StackChildGroupFactorySuffix
