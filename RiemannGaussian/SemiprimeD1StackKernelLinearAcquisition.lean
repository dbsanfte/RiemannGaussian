/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearPower
import RiemannGaussian.SemiprimeD1StackKernelLinearSum
import RiemannGaussian.SemiprimeD1StackKernelLinearFit
/-! # Actual original-input center, grid and displacement front door -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearAcquisition
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackKernelLinearPower (result source_trace)
end P
namespace Sum
export SemiprimeD1StackKernelLinearSum (value timeBound source_trace)
end Sum
namespace Fit
export SemiprimeD1StackKernelLinearFit (displacement displacementTime displacement_trace grid_trace)
end Fit
/-- Actual stopped binary sum cache, before real displacement subtraction. -/
def sumWords (a t x y:List Bool):Words:={P.result a t x y with buffer:=Sum.value (P.result a t x y)}
/-- Actual fitted displacement cache, before fitting original t. -/
def displacementWords (a t x y:List Bool):Words:=
  {sumWords a t x y with displacement:=Fit.displacement (sumWords a t x y)}
/-- Both actual fitted original index words, retaining every original input. -/
def gridWords (a t x y:List Bool):Words:=
  {displacementWords a t x y with j:=SemiprimeD1StackWordFitExecution.result t (true::a)}
/-- Exact acquired normalization-ready cache; no factor/result is present yet. -/
def readyWords (a t x y:List Bool):Words:={gridWords a t x y with alpha:=false::(P.result a t x y).center}
/-- Real alpha copy and actual binary shift, with every original/cache field retained. -/
theorem alpha_trace (w:Words) (hs:w.scratch=[]) (ha:w.alpha=[]):
    Runs program ((5*w.center.length+4)+1) (.local .alphaCopy) (data w) (.local .normalize)
      (data {w with alpha:=false::w.center}):=by
  have h0:=copy_call .centerAlpha (.local .alphaCopy) (.local .alphaShift) rfl (data w) w.center [] rfl ha hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data w) (aux .alpha) w.center) at h0
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h0
  have h1:=push_run (.local .alphaShift) (.local .normalize) (aux .alpha) false (data {w with alpha:=w.center}) rfl
  change Runs program 1 _ _ _ (Function.update (data {w with alpha:=w.center}) (aux .alpha) (false::w.center)) at h1
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h1
  simpa only [data] using join h0 h1
/-- Own total actual acquisition clock, composed only from real call clocks. -/
def timeBound (a t x y:List Bool):Nat:=
  (12*a.length+11)+Sum.timeBound (P.result a t x y)+Fit.displacementTime (sumWords a t x y)+
    ((5*t.length+4)+SemiprimeD1StackKernelLinearCalls.fitTime t (true::a))+
      ((5*(P.result a t x y).center.length+4)+1)
/-- Original physical x range discharges the actual borrow check, without displacement advice. -/
theorem source_trace (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    Runs program (timeBound a t x y) (.local .start) (data (sourceWords a t x y))
      (.local .normalize) (data (readyWords a t x y)):=by
  have h0:=P.source_trace a t x y
  have h1:=Sum.source_trace (P.result a t x y) rfl rfl
  have hb:(SemiprimeBitDivision.subBits (sumWords a t x y).buffer (sumWords a t x y).x false).borrow=false:=by
    change (SemiprimeD1StackKernelLinearSpec.displaced a.length x y).borrow=false
    exact SemiprimeD1StackKernelLinearSpec.displaced_borrow a.length x y hx
  have h2:=Fit.displacement_trace (sumWords a t x y) rfl rfl rfl hb
  have h3:=Fit.grid_trace (displacementWords a t x y) rfl rfl rfl
  have h4:=alpha_trace (gridWords a t x y) rfl rfl
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  simpa only [timeBound,readyWords,gridWords,displacementWords,sumWords,P.result,
    SemiprimeD1StackKernelLinearPower.result,sourceWords,Nat.add_assoc] using hh
end RiemannGaussian.SemiprimeD1StackKernelLinearAcquisition
