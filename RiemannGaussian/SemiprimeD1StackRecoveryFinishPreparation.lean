/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishFloor
import RiemannGaussian.SemiprimeD1StackRecoveryFinishCache
/-! # Actual floor-residue and Newton cache preparation
Four real WIDTH-copy/reduce/move stages acquire all canonical scalar caches.
Negative one is physically copied from unary WIDTH; two/one are actual constant
pushes followed by real reduction. The loop counter is another paid WIDTH copy.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishPreparation
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishWords
open SemiprimeD1StackRecoveryFinishStrip SemiprimeD1StackRecoveryFinishSetup
open SemiprimeD1StackRecoveryFinishRound SemiprimeD1StackRecoveryFinishFloor SemiprimeD1StackProcedureTrace
open SemiprimeBitIndexClipping (SignedWord)
namespace K
export SemiprimeD1StackRecoveryFinishCache (Kind target word time cached cache_run)
end K
local notation "ctl"=>Label.local
/-- Exact retained source/strip words; all scalar operands/results/private work are physically clear. -/
def common (n:SignedWord) (d w:List Bool):Values
  | .width=>w | .aux .numerator=>signedTape n | .aux .denominator=>d | .aux .sign=>[n.negative]
  | .aux .denominatorWork=>odd d | .aux .content=>content d | .aux .lost=>[lost d n.magnitude] | _=>[]
/-- Exact raw corrected floor word in the real reducer input, before any precision reduction. -/
def floorBank (n:SignedWord) (d w:List Bool):Values:=
  Function.update (common n d w) .reduceInput (corrected n.negative d n.magnitude)
/-- Actual floor source boundary matches this simple full-store invariant. -/
theorem floorBank_eq (n:SignedWord) (d w:List Bool):floorValues n d w=floorBank n d w:=by
  funext s
  cases s with
  | aux a=>cases a <;> simp [floorValues,rounded,stripped,view,base,initialValues,floorBank,common]
  | _=>simp [floorValues,rounded,stripped,view,base,initialValues,floorBank,common]
/-- Generic actual reduction-cache effect from an initially empty reducer input role. -/
theorem cached_input (v:Values) (hv:v .reduceInput=[]) (kind:K.Kind) (bits:List Bool):
    K.cached (Function.update v .reduceInput bits) kind=
      Function.update v (K.target kind) (SemiprimeD1JetScalarBits.reduce (v .width).length bits).bits:=by
  simp only [K.cached,K.word,Function.update_same,
    Function.update_of_ne (by decide:Slot.width≠.reduceInput),Function.update_idem]
  have he:Function.update v .reduceInput []=v:=Function.update_eq_self_iff.mpr hv.symm
  rw [he]
/-- Actual canonical signed-floor magnitude cache. -/
def first (n:SignedWord) (d w:List Bool):Values:=Function.update (common n d w) (.aux .numeratorResidue)
  (SemiprimeD1JetScalarBits.reduce w.length (corrected n.negative d n.magnitude)).bits
/-- Actual odd suffix copied into the reused real reducer input. -/
def oddBank (n:SignedWord) (d w:List Bool):Values:=Function.update (first n d w) .reduceInput (odd d)
/-- Actual canonical odd scalar cache. -/
def second (n:SignedWord) (d w:List Bool):Values:=Function.update (first n d w) (.aux .inverseInput)
  (SemiprimeD1JetScalarBits.reduce w.length (odd d)).bits
/-- Actual copied all-WIDTH negative-one cache; no numeric two-power is computed. -/
def third (n:SignedWord) (d w:List Bool):Values:=Function.update (second n d w) (.aux .negative) w
/-- Real two constant after its two actual pushes into the reused reducer input. -/
def twoBank (n:SignedWord) (d w:List Bool):Values:=Function.update (third n d w) .reduceInput [false,true]
/-- Actual canonically reduced two scalar cache. -/
def fourth (n:SignedWord) (d w:List Bool):Values:=Function.update (third n d w) (.aux .two)
  (SemiprimeD1JetScalarBits.reduce w.length [false,true]).bits
/-- Real one constant after its actual push into the reused reducer input. -/
def oneBank (n:SignedWord) (d w:List Bool):Values:=Function.update (fourth n d w) .reduceInput [true]
/-- Actual canonically reduced initial inverse iterate. -/
def fifth (n:SignedWord) (d w:List Bool):Values:=Function.update (fourth n d w) (.aux .current)
  (SemiprimeD1JetScalarBits.reduce w.length [true]).bits
/-- Entire actual loop-ready bank includes a physically copied WIDTH counter. -/
def result (n:SignedWord) (d w:List Bool):Values:=Function.update (fifth n d w) (.aux .todo) w
/-- Own exact preparation clock is the sum of the SAME real reducer/copy/constant stages. -/
def time (n:SignedWord) (d w:List Bool):Nat:=
  K.time (floorBank n d w)+(5*(odd d).length+4)+K.time (oddBank n d w)+(5*w.length+4)+1+1+
    K.time (twoBank n d w)+1+K.time (oneBank n d w)+(5*w.length+4)
/-- The SAME actual recovery program physically acquires every scalar cache before its precision-marker loop. -/
theorem preparation_run (n:SignedWord) (d w:List Bool):
    Runs program (time n d w) (ctl .qWidth) (data (floorBank n d w)) (ctl .loop) (data (result n d w)):=by
  have h0:=K.cache_run .quotient (floorBank n d w) rfl rfl rfl rfl
  have he0:K.cached (floorBank n d w) .quotient=first n d w:=by
    rw [floorBank,cached_input (common n d w) rfl]
    rfl
  rw [he0] at h0
  have h1:=copy_view .odd (ctl .oddInput) (ctl .aWidth) (first n d w) rfl rfl
  change Runs program (5*(odd d).length+4) _ _ _
    (data (Function.update (first n d w) .reduceInput (odd d++[]))) at h1
  simp only [List.append_nil] at h1
  have h2:=K.cache_run .odd (oddBank n d w) rfl rfl rfl rfl
  have he2:K.cached (oddBank n d w) .odd=second n d w:=by
    rw [oddBank,cached_input (first n d w) rfl]
    rfl
  rw [he2] at h2
  have h3:=copy_view .negative (ctl .negativeWord) (ctl .twoHigh) (second n d w) rfl rfl
  change Runs program (5*w.length+4) _ _ _
    (data (Function.update (second n d w) (.aux .negative) (w++[]))) at h3
  simp only [List.append_nil] at h3
  have h4:=push_view (ctl .twoHigh) (ctl .twoLow) .reduceInput true (third n d w) rfl
  change Runs program 1 _ _ _ (data (Function.update (third n d w) .reduceInput [true])) at h4
  have h5:=push_view (ctl .twoLow) (ctl .twoWidth) .reduceInput false
    (Function.update (third n d w) .reduceInput [true]) rfl
  simp only [Function.update_same,Function.update_idem] at h5
  change Runs program 1 _ _ _ (data (twoBank n d w)) at h5
  have h6:=K.cache_run .two (twoBank n d w) rfl rfl rfl rfl
  have he6:K.cached (twoBank n d w) .two=fourth n d w:=by
    rw [twoBank,cached_input (third n d w) rfl]
    rfl
  rw [he6] at h6
  have h7:=push_view (ctl .one) (ctl .oneWidth) .reduceInput true (fourth n d w) rfl
  change Runs program 1 _ _ _ (data (oneBank n d w)) at h7
  have h8:=K.cache_run .one (oneBank n d w) rfl rfl rfl rfl
  have he8:K.cached (oneBank n d w) .one=fifth n d w:=by
    rw [oneBank,cached_input (fourth n d w) rfl]
    rfl
  rw [he8] at h8
  have h9:=copy_view .todo (ctl .copyTodo) (ctl .loop) (fifth n d w) rfl rfl
  change Runs program (5*w.length+4) _ _ _
    (data (Function.update (fifth n d w) (.aux .todo) (w++[]))) at h9
  simp only [List.append_nil] at h9
  exact join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
/-- Whole original three-input frontend and physical cache preparation reach the actual Newton loop. -/
theorem source_prepared (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (w:List Bool):
    Runs program (floorTime n d+time n d w) (ctl .start) (initial (signedTape n) d w).data
      (ctl .loop) (data (result n d w)):=by
  have h0:=source_floor n d hd w
  rw [floorBank_eq] at h0
  exact join h0 (preparation_run n d w)
end RiemannGaussian.SemiprimeD1StackRecoveryFinishPreparation
