/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
/-! # Exact retention of all thirteen real structural/header input words
This follows the actual composed postbanks through every whole loop and final
physical cleanup. It does not assume preservation or regenerate any producer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputRetention
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
namespace EV
export SemiprimeD1StackChildGroupFactoryEndpointSourceView (Protected result_other)
end EV
namespace BV
export SemiprimeD1StackChildGroupFactoryBucketsSourceView (Protected result_other)
end BV
namespace VV
export SemiprimeD1StackChildGroupFactoryVertexBodyView (Protected)
end VV
/-- Static input-port mark; this finite role classifier is proof notation only. -/
def sourceMark :Stack→Bool
  | .inr (.inr (.inr (.inr (.inr k))))=>inputRole k
  | _=>false
/-- Every noninput fixed workspace/output address differs from all actual input roles. -/
theorem input_ne (k:Aux) (hi:inputRole k=true) (r:Stack) (hr:sourceMark r=false):aux k≠r:=by
  intro he
  have h:=congrArg sourceMark he
  change inputRole k=sourceMark r at h
  rw [hi,hr] at h
  cases h
/-- Actual endpoint-source work and outputs are disjoint from every initial source operand. -/
theorem endpoint_protected (k:Aux) (hi:inputRole k=true):EV.Protected (aux k):=by
  constructor
  all_goals first
    | (intro j;exact Ne.symm (input_ne k hi _ (by fin_cases j <;> decide)))
    | exact input_ne k hi _ (by decide)
/-- All actual packet/converter work and outputs are disjoint from real inputs. -/
theorem bucket_protected (k:Aux) (hi:inputRole k=true):BV.Protected (aux k):=by
  constructor
  all_goals first
    | (intro j;exact Ne.symm (input_ne k hi _ (by fin_cases j <;> decide)))
    | exact input_ne k hi _ (by decide)
/-- All actual per-vertex parser/counter/logging work is disjoint from real inputs. -/
theorem vertex_protected (k:Aux) (hi:inputRole k=true):VV.Protected (aux k):=by
  constructor
  all_goals first
    | (intro j;exact Ne.symm (input_ne k hi _ (by fin_cases j <;> decide)))
    | exact input_ne k hi _ (by decide)
/-- The whole all-vertex source preserves actual source operands, including all retained headers. -/
theorem vertices_input (before:Stack→List Bool) (owners factors:List Bool)
    (points:List SemiprimeD1StackChildGroupFactoryOldPortParse.Point)
    (buckets:List SemiprimeD1StackChildGroupFactoryLeftPortsLoop.Bucket) (key:List Bool)
    (k:Aux) (hi:inputRole k=true):
    SemiprimeD1StackChildGroupFactoryVerticesSource.result before owners factors points buckets key (aux k)=before (aux k):=by
  simp only [SemiprimeD1StackChildGroupFactoryVerticesSource.result,
    SemiprimeD1StackChildGroupFactoryVerticesSource.scopeDone,
    Function.update_of_ne (input_ne k hi _ (by decide : sourceMark (aux .orders)=false)),
    Function.update_of_ne (input_ne k hi _ (by decide : sourceMark (aux .factorHistory)=false)),
    Function.update_of_ne (input_ne k hi _ (by decide : sourceMark (aux .leftPorts)=false)),
    Function.update_of_ne (input_ne k hi _ (by decide : sourceMark (aux .vertexHistory)=false)),
    SemiprimeD1StackChildGroupFactoryVerticesSource.loopBank]
  rw [SemiprimeD1StackChildGroupFactoryVerticesLoopView.result_other _ _ _ _ _ _
    (vertex_protected k hi) (input_ne k hi _ (by decide))]
  exact Function.update_of_ne (input_ne k hi _ (by decide)) _ _
/-- Complete actual activation stop retains every initial source word literally. -/
theorem activation_input (i:Inputs) (coordinate:Nat)
    (rows:List SemiprimeD1StackChildGroupFactoryActivationLoop.Row) (k:Aux) (hi:inputRole k=true):
    SemiprimeD1StackChildGroupFactoryActivationSource.result i coordinate rows (aux k)=input i (aux k):=by
  cases k <;> simp only [inputRole,Bool.false_eq_true] at hi
  all_goals rfl
/-- ALL thirteen input operands remain exact at the whole true halt; no cache has been reacquired. -/
theorem result_input (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields) (k:Aux) (hi:inputRole k=true):
    SemiprimeD1StackChildGroupFactoryExecution.result i a coordinate ids packets fields (aux k)=input i (aux k):=by
  unfold SemiprimeD1StackChildGroupFactoryExecution.result SemiprimeD1StackChildGroupFactorySuffix.result
  rw [SemiprimeD1StackChildGroupFactoryFinish.result_retained _ _
    (by simp only [retained,aux,hi,Bool.true_or]) (input_ne k hi _ (by decide)),
    SemiprimeD1StackChildGroupFactoryFinalFrames.result_other _ _ (input_ne k hi _ (by decide)),
    vertices_input _ _ _ _ _ _ k hi]
  unfold SemiprimeD1StackChildGroupFactoryForwardBucketsSource.result
  rw [BV.result_other _ _ _ _ _ (bucket_protected k hi)]
  unfold SemiprimeD1StackChildGroupFactoryForwardSource.result
  rw [EV.result_other _ _ _ (endpoint_protected k hi)]
  exact activation_input _ _ _ k hi
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputRetention
