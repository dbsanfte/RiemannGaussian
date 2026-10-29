/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearCalls
/-! # Proof views of all actual fixed kernel-factor roles -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinear
/-- Proof-only names for physical words, never a runtime record operand. -/
structure Words where
  /-- Actual physical a word. -/
  a : List Bool := []
  /-- Actual physical t word. -/
  t : List Bool := []
  /-- Actual physical x word. -/
  x : List Bool := []
  /-- Actual physical y word. -/
  y : List Bool := []
  /-- Actual physical k word. -/
  k : List Bool := []
  /-- Actual physical center word. -/
  center : List Bool := []
  /-- Actual physical j word. -/
  j : List Bool := []
  /-- Actual physical displacement word. -/
  displacement : List Bool := []
  /-- Actual physical alpha word. -/
  alpha : List Bool := []
  /-- Actual physical content word. -/
  content : List Bool := []
  /-- Actual physical constant word. -/
  constant : List Bool := []
  /-- Actual physical sign word. -/
  sign : List Bool := []
  /-- Actual physical slope word. -/
  slope : List Bool := []
  /-- Actual physical remaining word. -/
  remaining : List Bool := []
  /-- Actual physical scan word. -/
  scan : List Bool := []
  /-- Actual physical scratch word. -/
  scratch : List Bool := []
  /-- Actual physical buffer word. -/
  buffer : List Bool := []
  /-- Actual physical valid word. -/
  valid : List Bool := []
/-- Complete physical auxiliary-bank projection. -/
def words (w:Words):Aux→List Bool
  | .a=>w.a
  | .t=>w.t
  | .x=>w.x
  | .y=>w.y
  | .k=>w.k
  | .center=>w.center
  | .j=>w.j
  | .displacement=>w.displacement
  | .alpha=>w.alpha
  | .content=>w.content
  | .constant=>w.constant
  | .sign=>w.sign
  | .slope=>w.slope
  | .remaining=>w.remaining
  | .scan=>w.scan
  | .scratch=>w.scratch
  | .buffer=>w.buffer
  | .valid=>w.valid
/-- Proof-side single physical field replacement. -/
def set (w:Words) (role:Aux) (value:List Bool):Words:=match role with
  | .a=>{w with a:=value}
  | .t=>{w with t:=value}
  | .x=>{w with x:=value}
  | .y=>{w with y:=value}
  | .k=>{w with k:=value}
  | .center=>{w with center:=value}
  | .j=>{w with j:=value}
  | .displacement=>{w with displacement:=value}
  | .alpha=>{w with alpha:=value}
  | .content=>{w with content:=value}
  | .constant=>{w with constant:=value}
  | .sign=>{w with sign:=value}
  | .slope=>{w with slope:=value}
  | .remaining=>{w with remaining:=value}
  | .scan=>{w with scan:=value}
  | .scratch=>{w with scratch:=value}
  | .buffer=>{w with buffer:=value}
  | .valid=>{w with valid:=value}
/-- Field replacement is exactly the physical functional update. -/
theorem words_set (w:Words) (role:Aux) (value:List Bool):
    words (set w role value)=Function.update (words w) role value:=by
  funext r;cases role <;> cases r <;> rfl
/-- Complete real divider/auxiliary physical bank. -/
def bank (d:D.Stack→List Bool) (w:Words):Stack→List Bool:=Sum.elim d (words w)
/-- Actual auxiliary update preserves all eleven arithmetic fields. -/
theorem bank_aux_update (d:D.Stack→List Bool) (w:Words) (role:Aux) (value:List Bool):
    Function.update (bank d w) (aux role) value=bank d (set w role value):=by
  funext r;rcases r with r|r <;> simp [bank,aux,words_set,Function.update_apply]
/-- Real divider-field update preserves all eighteen original/cache/private fields. -/
theorem bank_div_update (d:D.Stack→List Bool) (w:Words) (role:D.Stack) (value:List Bool):
    Function.update (bank d w) (divider role) value=bank (Function.update d role value) w:=by
  funext r;rcases r with r|r <;> simp [bank,divider,Function.update_apply]
/-- Physical source view with the shared divider bank empty. -/
def data (w:Words):Stack→List Bool:=bank (fun _=>[]) w
/-- Actual ripple source/target view with every other divider field empty. -/
def arithmeticData (w:Words) (left right output:List Bool):Stack→List Bool:=
  SemiprimeD1StackKernelLinearPrimitives.view (SemiprimeD1StackAdder.store left right [] output) (fun _=>[]) (words w)
/-- The clean arithmetic boundary is exactly the complete clean source view. -/
theorem arithmeticData_empty (w:Words):arithmeticData w [] [] []=data w:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · cases r <;> rfl
  · rfl
/-- Auxiliary field update commutes with the actual ripple-bank view. -/
theorem arithmeticData_aux_update (w:Words) (left right output:List Bool) (role:Aux) (value:List Bool):
    Function.update (arithmeticData w left right output) (aux role) value=
      arithmeticData (set w role value) left right output:=by
  funext r;rcases r with r|r
  · rcases r with r|r <;> simp [arithmeticData,SemiprimeD1StackKernelLinearPrimitives.view,aux]
  · simp [arithmeticData,SemiprimeD1StackKernelLinearPrimitives.view,aux,words_set,Function.update_apply]
/-- Exact actual output-field update at a completed ripple boundary. -/
theorem arithmeticData_output_update (w:Words) (left right output value:List Bool):
    Function.update (arithmeticData w left right output) (arithmetic .output) value=
      arithmeticData w left right value:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · rfl
  · rfl
/-- Exact actual first-operand copy update. -/
theorem arithmeticData_left_update (w:Words) (left right output value:List Bool):
    Function.update (arithmeticData w left right output) (arithmetic .left) value=
      arithmeticData w value right output:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · rfl
  · rfl
/-- Exact actual second-operand copy update. -/
theorem arithmeticData_right_update (w:Words) (left right output value:List Bool):
    Function.update (arithmeticData w left right output) (arithmetic .right) value=
      arithmeticData w left value output:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · rfl
  · rfl
/-- The actual original-only source word view. -/
def sourceWords (a t x y:List Bool):Words:={a:=a,t:=t,x:=x,y:=y}
/-- Every physical source and every initially empty word is explicit. -/
theorem initial_eq (a t x y:List Bool):input a t x y=data (sourceWords a t x y):=by
  funext r;rcases r with r|r
  · simp [input,aux,data,bank]
  · cases r <;> rfl
end RiemannGaussian.SemiprimeD1StackKernelLinearView
