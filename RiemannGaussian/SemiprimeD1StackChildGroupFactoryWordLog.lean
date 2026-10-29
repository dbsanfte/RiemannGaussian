/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Actual ordered word logging at four literal port/order source sites
Each use performs its real preserving Frame, TRUE tag and consuming reverse.
The theorem index names four fixed code families, never an input logger mode.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Four fixed preserving-frame sources. -/
def wordRole (site:Fin 4):Stack:=match site.val with
  | 0=>aux .globalPosition | 1=>aux .answerPosition | _=>ordinal .output
/-- Four fixed actual reverse-log targets. -/
def historyRole (site:Fin 4):Stack:=match site.val with
  | 0=>aux .portHistory | 1=>aux .orderHistory | 2=>aux .vertexHistory | _=>aux .factorHistory
/-- Actual fixed frame component locations. -/
def frameSite (site:Fin 4):Fin 25:=match site.val with | 0=>12 | 1=>18 | _=>15
/-- Actual fixed consuming-reversal component locations. -/
def reverseSite (site:Fin 4):Fin 16:=match site.val with | 0=>6 | 1=>12 | 2=>11 | _=>9
/-- Four literal three-instruction source blocks and their actual continuations. -/
def pc (site:Fin 4) (slot:Fin 4):Label:=match site.val,slot.val with
  | 0,0=>.local 10 15 | 0,1=>.local 10 16 | 0,2=>.local 10 17 | 0,3=>.local 10 9
  | 1,0=>.local 14 0 | 1,1=>.local 14 1 | 1,2=>.local 14 2 | 1,3=>.local 14 3
  | 2,0=>.local 10 22 | 2,1=>.local 10 23 | 2,2=>.local 10 24 | 2,3=>.local 10 25
  | 3,0=>.local 14 13 | 3,1=>.local 14 14 | 3,2=>.local 14 15 | 3,3=>.local 14 16
  | _,_=>.local 10 15
/-- Exact one-word vector record put on the actual reversed history. -/
def row (word:List Bool):List Bool:=true::frame word []
/-- Every physical primitive step and its real return is included. -/
def timeBound (word:List Bool):Nat:=(6*word.length+5)+1+(2*(row word).length+3)
/-- Complete actual logger with full115-word postcondition. -/
theorem source_trace (site:Fin 4) (before:Stack→List Bool) (word:List Bool)
    (hw:before (wordRole site)=word) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound word) (pc site 0) before (pc site 3)
      (Function.update before (historyRole site) ((row word).reverse++before (historyRole site))):=by
  let b1:=Function.update before (aux .frameBuffer) (frame word [])
  have h0a:=frame_call (frameSite site) (pc site 0) (pc site 1) (by fin_cases site <;> rfl)
    before word [] (by fin_cases site <;> exact hw) (by fin_cases site <;> exact hb) hc
  have h0:Runs program (6*word.length+5) (pc site 0) before (pc site 1) b1:=by fin_cases site <;> exact h0a
  let b2:=Function.update b1 (aux .frameBuffer) (row word)
  have h1a:=push_run (pc site 1) (pc site 2) (aux .frameBuffer) true b1 (by fin_cases site <;> rfl)
  have h1:Runs program 1 (pc site 1) b1 (pc site 2) b2:=by simpa only [b2,Function.update_self,b1,row] using h1a
  have h2a:=reverse_call (reverseSite site) (pc site 2) (pc site 3) (by fin_cases site <;> rfl) b2
    (row word) (before (historyRole site))
    (by fin_cases site <;> exact Function.update_self _ _ _)
    (by fin_cases site <;> simp [b2,b1,reverseStack,reversePorts,reverseSite,historyRole,aux])
  have h2:Runs program (2*(row word).length+3) (pc site 2) b2 (pc site 3)
      (Function.update (Function.update b2 (aux .frameBuffer) []) (historyRole site)
        ((row word).reverse++before (historyRole site))):=by fin_cases site <;> exact h2a
  have he:Function.update b2 (aux .frameBuffer) []=before:=by
    dsimp only [b2,b1]
    rw [Function.update_idem,Function.update_idem,←hb]
    exact Function.update_eq_self _ _
  rw [he] at h2
  have hwhole:=join h0 (join h1 h2)
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
