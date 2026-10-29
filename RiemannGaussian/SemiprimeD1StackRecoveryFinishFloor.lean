/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishSetup
import RiemannGaussian.SemiprimeD1StackRecoveryFinishRound
/-! # Complete actual three-input source through arbitrary signed floor correction
Source copies, sign extraction, paired low-bit shifts, actual loss detection,
negative full increment and result movement are one trace of the literal program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishFloor
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishWords
open SemiprimeD1StackRecoveryFinishStrip SemiprimeD1StackRecoveryFinishSetup
open SemiprimeD1StackRecoveryFinishRound SemiprimeD1StackProcedureTrace
open SemiprimeBitIndexClipping (SignedWord)
local notation "ctl"=>Label.local
/-- Exact actual source bank after the real zero-strip loop. -/
def stripped (n:SignedWord) (d w:List Bool):Values:=
  view (base n d w) (odd d) (dropped d n.magnitude) (content d) [lost d n.magnitude]
/-- Exact actual full floor magnitude has reached the real modular-reducer input; all raw arithmetic work is clear. -/
def floorValues (n:SignedWord) (d w:List Bool):Values:=
  rounded (stripped n d w) (corrected n.negative d n.magnitude)
/-- Same-source actual frontend clock: two real source copies, bit/sign/loss tests, and actual chosen correction branch. -/
def floorTime (n:SignedWord) (d:List Bool):Nat:=
  5*(signedTape n).length+5*d.length+3*zeros d+14+
    roundTime n.negative (lost d n.magnitude) (dropped d n.magnitude)
/-- All actual frontend operations from the three physical inputs reach the exact full signed-floor boundary. -/
theorem source_floor (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (w:List Bool):
    Runs program (floorTime n d) (ctl .start) (initial (signedTape n) d w).data
      (ctl .qWidth) (data (floorValues n d w)):=by
  have h0:=source_strip n d hd w
  have h1:=round_run (stripped n d w) n.negative (lost d n.magnitude)
    (by simp [stripped,view,base]) rfl
    (by simp [stripped,view,base,initialValues])
    (by simp [stripped,view,base,initialValues])
    (by simp [stripped,view,base,initialValues])
    (by simp [stripped,view,base,initialValues])
    (by simp [stripped,view,base,initialValues])
  change Runs program (roundTime n.negative (lost d n.magnitude) (dropped d n.magnitude))
    (ctl .signFloor) (data (stripped n d w)) (ctl .qWidth) (data (floorValues n d w)) at h1
  exact join h0 h1
/-- The actual binary magnitude stored by the full source is the actual raw corrected word. -/
theorem floor_magnitude (n:SignedWord) (d w:List Bool):
    data (floorValues n d w) (reduceStack .left)=(quotient n d).magnitude:=by
  change data (floorValues n d w) (address .reduceInput)=_
  rw [data_get]
  rfl
/-- Actual three-input floor source agrees with the exact original signed quotient VALUE without a divisibility assumption. -/
theorem floor_original (n:SignedWord) (d w:List Bool):
    (⟨n.negative,data (floorValues n d w) (reduceStack .left)⟩:SignedWord).value=
      (SemiprimeBitIndexClipping.floorSignedBits n (Old.acquire d).content).word.value:=by
  rw [floor_magnitude]
  exact quotient_floor_original n d
/-- The original complete signed binary numerator survives byte for byte through actual floor correction. -/
theorem numerator_retained (n:SignedWord) (d w:List Bool):
    data (floorValues n d w) (aux .numerator)=signedTape n:=by
  rw [show aux .numerator=address (.aux .numerator) from rfl,data_get]
  simp [floorValues,rounded,stripped,view,base,initialValues]
/-- The original binary denominator survives byte for byte through actual floor correction. -/
theorem denominator_retained (n:SignedWord) (d w:List Bool):
    data (floorValues n d w) (aux .denominator)=d:=by
  rw [show aux .denominator=address (.aux .denominator) from rfl,data_get]
  simp [floorValues,rounded,stripped,view,base,initialValues]
/-- The actual unary precision cache is untouched by the entire floor frontend. -/
theorem width_retained (n:SignedWord) (d w:List Bool):data (floorValues n d w) width=w:=by
  rw [show width=address .width from rfl,data_get]
  simp [floorValues,rounded,stripped,view,base,initialValues]
end RiemannGaussian.SemiprimeD1StackRecoveryFinishFloor
