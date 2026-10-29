/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePrimitives
/-! # Four real Frames and physically reversed entry logging
Actual selected coefficient bytes retain all padding. Per-block and per-phase
logging does not rescan prior histories; their final real reversals restore order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLogger
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual source Aux role at each fixed preserving-frame site. -/
def frameRole (phase:Bool):Role:=if phase then .rowOutput else .value
/-- Fixed real preserving frame call label. -/
def framePC (phase:Bool):Label:=.local (if phase then .phaseFrame else .coefficientFrame)
/-- Fixed actual next marker push label. -/
def frameNext (phase:Bool):Label:=.local (if phase then .phaseTag else .coefficientTag)
/-- Every source-frame role is the declared physical byte word. -/
theorem frame_address (phase:Bool):frameStack phase 0=address (frameRole phase):=by cases phase <;> rfl
/-- Every real preserving frame includes all byte traversals, delimiter and real call/return. -/
theorem frame_call (phase:Bool) (key:List Bool) (w:Role → List Bool):
    Runs program (6*(w (frameRole phase)).length+5) (framePC phase) (data key w) (frameNext phase)
      (data key (Function.update w .buffer (frame (w (frameRole phase)) (w .buffer)))):=by
  rw [data_update]
  let before:=SemiprimeD1StackFrame.state 0 none (w (frameRole phase)) (w .buffer) []
  let after:=SemiprimeD1StackFrame.done (w (frameRole phase)) (frame (w (frameRole phase)) (w .buffer))
  have hin:SemiprimeD1StackMultiplierLink.DataRel (frameStack phase) (data key w) before.store (data key w):=by
    constructor
    · intro k;fin_cases k
      · change data key w (frameStack phase 0)=w (frameRole phase)
        rw [frame_address,data_get]
      · rfl
      · exact data_scratch key w
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update (frameStack phase) (frame_injective phase)
    (data key w) before.store (data key w) hin (1:Fin 3) (frame (w (frameRole phase)) (w .buffer))
  have he:Function.update before.store 1 (frame (w (frameRole phase)) (w .buffer))=after.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack phase) (Label.frame phase) (frame_injective phase) SemiprimeD1StackFrame.code 0
    (fun _=>rfl) (framePC phase) (frameNext phase) (by cases phase <;> rfl) (6*(w (frameRole phase)).length+4)
    before after _ _ rfl rfl (SemiprimeD1StackFrame.frame_words _ _ none) hin ho
/-- Actual input role of each of the two fixed real reversals. -/
def reverseFrom (site:Fin 4):Role:=if site=0 ∨site=2 then .buffer else if site=1 then .rowHistory else .history
/-- Actual output role of each fixed real reversal. -/
def reverseTo (site:Fin 4):Role:=if site=0 then .rowHistory else if site=1 then .rowOutput else if site=2 then .history else .output
/-- Every reversal source equals its physical role. -/
theorem reverse_source (site:Fin 4):reverseStack site 0=address (reverseFrom site):=by fin_cases site <;> rfl
/-- Every reversal target equals its physical role. -/
theorem reverse_target (site:Fin 4):reverseStack site 1=address (reverseTo site):=by fin_cases site <;> rfl
/-- Both actual reversal operands are distinct. -/
theorem reverse_ne (site:Fin 4):address (reverseFrom site)≠address (reverseTo site):=by fin_cases site <;> decide
/-- Real reversal consumes its entire source and pays every push plus call/return. -/
theorem reverse_call (site:Fin 4) (pc next:Label) (key:List Bool) (w:Role → List Bool)
    (hp:program pc=.call (.reverse site 0) next):
    Runs program (2*(w (reverseFrom site)).length+3) pc (data key w) next
      (data key (Function.update (Function.update w (reverseFrom site) []) (reverseTo site)
        ((w (reverseFrom site)).reverse++w (reverseTo site)))):=by
  simp only [data_update]
  let before:=SemiprimeD1StackReverseWord.state none (w (reverseFrom site)) (w (reverseTo site))
  let after:=SemiprimeD1StackReverseWord.done ((w (reverseFrom site)).reverse++w (reverseTo site))
  have hin:SemiprimeD1StackMultiplierLink.DataRel (reverseStack site) (data key w) before.store (data key w):=by
    constructor
    · intro k;fin_cases k
      · change data key w (reverseStack site 0)=_;rw [reverse_source,data_get];rfl
      · change data key w (reverseStack site 1)=_;rw [reverse_target,data_get];rfl
    · intro k _;rfl
  have h0:=SemiprimeD1StackMultiplierLink.data_update (reverseStack site) (reverse_injective site)
    (data key w) before.store (data key w) hin (0:Fin 2) []
  have h1:=SemiprimeD1StackMultiplierLink.data_update (reverseStack site) (reverse_injective site)
    (data key w) _ _ h0 (1:Fin 2) ((w (reverseFrom site)).reverse++w (reverseTo site))
  have he:Function.update (Function.update before.store 0 []) 1 ((w (reverseFrom site)).reverse++w (reverseTo site))=after.store:=by
    funext k;fin_cases k <;> rfl
  rw [he,reverse_source,reverse_target] at h1
  exact included_call program (reverseStack site) (Label.reverse site) (reverse_injective site) SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) pc next hp (2*(w (reverseFrom site)).length+2) before after _ _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run _ _ none) hin h1
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLogger
