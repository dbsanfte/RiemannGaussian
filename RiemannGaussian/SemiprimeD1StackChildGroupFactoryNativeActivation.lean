/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBounds
import RiemannGaussian.SemiprimeD1ChildActivationOriginal
/-! # Exact original all-vertex activation at the actual whole factory halt
Every original vertex is included, also isolated/inactive vertices. Arbitrarily
padded binary group operands are interpreted numerically; colourIndex remains
the colour coordinate, never the distinct NEW context jetAxis.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeActivation
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (result)
end E
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows)
end Forward
namespace A
export SemiprimeD1StackChildGroupFactoryActivationSource (result)
export SemiprimeD1StackChildGroupFactoryActivationMap (flags)
end A
namespace M
export SemiprimeD1StackChildGroupFactoryActivationMeaning (plan_flags active_original)
end M
namespace V
export SemiprimeD1StackChildGroupFactoryVerticesSource (result scopeDone loopBank copied)
export SemiprimeD1StackChildGroupFactoryVerticesLoopView (result_other)
end V
namespace EV
export SemiprimeD1StackChildGroupFactoryEndpointSourceView (result_other)
end EV
namespace BV
export SemiprimeD1StackChildGroupFactoryBucketsSourceView (result_other)
end BV
namespace Native
export SemiprimeD1ChildActivation (acquire fromReplay fromReplay_bits readOne)
end Native
open SemiprimeBitArithmetic (bitValue)
/-- Actual all-vertex activation output survives every later source and the full physical sweep. -/
theorem result_flags (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool))
    (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields):
    E.result i a coordinate ids packets fields (aux .activation)=A.flags i coordinate (Forward.activation a ids):=by
  unfold E.result SemiprimeD1StackChildGroupFactorySuffix.result
  rw [SemiprimeD1StackChildGroupFactoryFinish.result_retained _ _ (by decide) (by decide),
    SemiprimeD1StackChildGroupFactoryFinalFrames.result_other _ _ (by decide)]
  dsimp only [V.result,V.scopeDone]
  rw [Function.update_of_ne (by decide:aux .activation≠aux .orders),
    Function.update_of_ne (by decide:aux .activation≠aux .factorHistory),
    Function.update_of_ne (by decide:aux .activation≠aux .leftPorts),
    Function.update_of_ne (by decide:aux .activation≠aux .vertexHistory)]
  unfold V.loopBank
  rw [V.result_other _ _ _ _ _ _ (by
      constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide) (by decide)]
  rw [show V.copied (SemiprimeD1StackChildGroupFactoryForwardBucketsSource.result i a coordinate ids packets fields)
      i.owners i.factors (aux .activation)=
      SemiprimeD1StackChildGroupFactoryForwardBucketsSource.result i a coordinate ids packets fields (aux .activation) from
        Function.update_of_ne (by decide) _ _]
  unfold SemiprimeD1StackChildGroupFactoryForwardBucketsSource.result
  rw [BV.result_other _ _ _ _ _ (by
    constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)]
  unfold SemiprimeD1StackChildGroupFactoryForwardSource.result
  rw [EV.result_other _ _ _ (by
    constructor;all_goals first | (intro j;fin_cases j <;> decide) | decide)]
  simp only [A.result,Function.update_self,SemiprimeD1StackChildGroupFactoryActivationResults.finish_history,
    List.append_nil,List.reverse_reverse,A.flags]
/-- Proof-side original selected IDs, acquired by the actual original finite search. -/
def originalIDs (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n):List (List Bool):=
  (SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value
/-- The exact actual computed flag vector equals the legacy original activation producer. -/
theorem flags_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:bitValue i.group=g.val):
    A.flags i q.val (Forward.activation a (originalIDs n F a arity owner))=
      (Native.acquire n F 64 a arity owner q g).bits:=by
  let ids:=originalIDs n F a arity owner
  let canonical:Inputs:={i with group:=(SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits}
  have hactive (colours:List (List Bool)):
      SemiprimeD1StackChildGroupFactoryActivationView.active i q.val colours=
        SemiprimeD1StackChildGroupFactoryActivationView.active canonical q.val colours:=by
    simp only [SemiprimeD1StackChildGroupFactoryActivationView.active,canonical,
      SemiprimeSourceHistogramPortKeys.encodeKey_value,hg]
  rw [A.flags,Forward.activation,M.plan_flags]
  change ids.reverse.map (fun id=>SemiprimeD1StackChildGroupFactoryActivationView.active i q.val
    (SemiprimeD1StackPacketRowsMeaning.fields 64 a id))=(Native.fromReplay _ q g).bits
  rw [Native.fromReplay_bits]
  change ids.reverse.map (fun id=>SemiprimeD1StackChildGroupFactoryActivationView.active i q.val
    (SemiprimeD1StackPacketRowsMeaning.fields 64 a id))=ids.reverse.map (fun id=>
      (Native.readOne (SemiprimeSourceHistogramRows.acquire 64 a) a q.val
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits id).value)
  apply List.map_congr_left
  intro id hi
  have hmem:=SemiprimeD1IncidenceSearch.run_valid n F 64 a arity owner id (List.mem_reverse.mp hi)
  rw [hactive]
  exact M.active_original canonical a q.val id hmem
/-- The actual whole halt contains exactly every original colour activation bit. -/
theorem result_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (packets:List (List Bool)) (fields:List SemiprimeD1StackChildGroupFactoryEndpointParse.Fields)
    (hg:bitValue i.group=g.val):
    E.result i a q.val (originalIDs n F a arity owner) packets fields (aux .activation)=
      (Native.acquire n F 64 a arity owner q g).bits:=
  (result_flags i a q.val (originalIDs n F a arity owner) packets fields).trans
    (flags_original i n F a arity owner q g hg)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeActivation
