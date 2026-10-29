/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
/-! # Actual computed first-index answer logger and complete local counter reuse
The real answer word is logged before three actual erases. The original-port
reader and every other caller/cache tape are retained byte for byte.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagAnswer
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row timeBound source_trace)
end Log
/-- Complete actual ordered-answer log and physically emptied three search words. -/
def result (before:Stack→List Bool) (answer:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update before (aux .orderHistory)
    ((Log.row answer).reverse++before (aux .orderHistory))) (aux .answerPosition) []) (aux .localPosition) []) (aux .tagWord) []
/-- All actual logger, answer/counter/target-tag bytes and EOF instructions are paid. -/
def timeBound (answer position tag:List Bool):Nat:=Log.timeBound answer+(answer.length+1)+(position.length+1)+(tag.length+1)
/-- Complete actual answer emission from the actual physical answer/local/tag words only. -/
theorem source_trace (before:Stack→List Bool) (answer position tag:List Bool)
    (ha:before (aux .answerPosition)=answer) (hp:before (aux .localPosition)=position)
    (ht:before (aux .tagWord)=tag) (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound answer position tag) (.local 14 0) before (.local 11 7) (result before answer):=by
  have h0:=Log.source_trace 1 before answer ha hb hc
  let b1:=Function.update before (aux .orderHistory) ((Log.row answer).reverse++before (aux .orderHistory))
  change Runs program _ (.local 14 0) before (.local 14 3) b1 at h0
  let b2:=Function.update b1 (aux .answerPosition) []
  have h1:=drain_loop (.local 14 3) (.local 14 4) (aux .answerPosition) rfl b1 answer
    (by simpa [b1,aux] using ha)
  change Runs program _ _ b1 _ b2 at h1
  let b3:=Function.update b2 (aux .localPosition) []
  have h2:=drain_loop (.local 14 4) (.local 14 5) (aux .localPosition) rfl b2 position
    (by simpa [b2,b1,aux] using hp)
  change Runs program _ _ b2 _ b3 at h2
  have h3:=drain_loop (.local 14 5) (.local 11 7) (aux .tagWord) rfl b3 tag
    (by simpa [b3,b2,b1,aux] using ht)
  change Runs program _ _ b3 _ (result before answer) at h3
  have hwhole:=join h0 (join h1 (join h2 h3))
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagAnswer
