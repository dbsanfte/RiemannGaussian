/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishStrip
/-! # Actual three-input source reaches the exact signed-floor strip boundary
Both binary source words are physically copied. The sign is physically popped
from the numerator copy and stored, and the content seed is a real constant push.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishSetup
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishWords SemiprimeD1StackRecoveryFinishStrip
open SemiprimeD1StackProcedureTrace
open SemiprimeBitIndexClipping (SignedWord)
local notation "ctl"=>Label.local
/-- The only physical numerator input codec is one actual sign cell followed by binary magnitude cells. -/
def signedTape (n:SignedWord):List Bool:=n.negative::n.magnitude
/-- Finite Boolean control site selected by the actually popped numerator sign. -/
def signControl (negative:Bool):Control:=if negative then .signTrue else .signFalse
/-- Proof-side untouched source bank plus the actual acquired one-bit sign cache. -/
def base (n:SignedWord) (denominator widthWord:List Bool):Values:=
  Function.update (initialValues (signedTape n) denominator widthWord) (.aux .sign) [n.negative]
/-- Exact physical strip-entry bank reached after the two real copies and sign/content writes. -/
def prepared (n:SignedWord) (denominator widthWord:List Bool):Values:=
  view (base n denominator widthWord) denominator n.magnitude [true] []
/-- Exact actual pre-strip clock of the real two-copy/sign/content setup. -/
def setupTime (n:SignedWord) (denominator:List Bool):Nat:=5*(signedTape n).length+5*denominator.length+11
/-- Original three-input entry really copies/parses/seeds before its low-bit strip loop. -/
theorem setup_run (n:SignedWord) (d w:List Bool):
    Runs program (setupTime n d) (ctl .start) (initial (signedTape n) d w).data
      (ctl (.strip false)) (data (prepared n d w)):=by
  let v0:=initialValues (signedTape n) d w
  let v1:=Function.update v0 (.aux .numeratorWork) (signedTape n)
  let v2:=Function.update v1 (.aux .numeratorWork) n.magnitude
  let v3:=Function.update v2 (.aux .sign) [n.negative]
  let v4:=Function.update v3 (.aux .content) [true]
  let v5:=Function.update v4 (.aux .denominatorWork) d
  have h0:=copy_view .numerator (ctl .start) (ctl .sign) v0 rfl (by simp [v0,initialValues])
  have hv0:v0 (.aux .numerator)=signedTape n:=by simp [v0,initialValues]
  have hz0:v0 (.aux .numeratorWork)=[]:=by simp [v0,initialValues]
  simp only [copyFrom,copyTo,hv0,hz0,List.append_nil] at h0
  change Runs program (5*(signedTape n).length+4) (ctl .start) (data v0) (ctl .sign) (data v1) at h0
  have h1:=pop_view (ctl .sign) (ctl .abort) (ctl .signFalse) (ctl .signTrue)
    (.aux .numeratorWork) v1 (signedTape n) rfl (by simp [v1])
  have h1':Runs program 1 (ctl .sign) (data v1) (ctl (signControl n.negative)) (data v2):=by
    cases hn:n.negative <;> simpa only [signedTape,List.head?_cons,List.tail_cons,signControl,hn,
      Bool.false_eq_true,ite_false,ite_true,SemiprimeD1StackBytecode.choose] using h1
  have hc:program (ctl (signControl n.negative))=.base (.push (address (.aux .sign)) n.negative (ctl .content)):=by
    cases n.negative <;> rfl
  have h2:=push_view (ctl (signControl n.negative)) (ctl .content) (.aux .sign) n.negative v2 hc
  have hz2:v2 (.aux .sign)=[]:=by simp [v2,v1,v0,initialValues]
  simp only [hz2] at h2
  change Runs program 1 _ (data v2) _ (data v3) at h2
  have h3:=push_view (ctl .content) (ctl .copyDen) (.aux .content) true v3 rfl
  have hz3:v3 (.aux .content)=[]:=by simp [v3,v2,v1,v0,initialValues]
  simp only [hz3] at h3
  change Runs program 1 _ (data v3) _ (data v4) at h3
  have h4:=copy_view .denominator (ctl .copyDen) (ctl (.strip false)) v4 rfl
    (by simp [v4,v3,v2,v1,v0,initialValues])
  have hd4:v4 (.aux .denominator)=d:=by simp [v4,v3,v2,v1,v0,initialValues]
  have hz4:v4 (.aux .denominatorWork)=[]:=by simp [v4,v3,v2,v1,v0,initialValues]
  simp only [copyFrom,copyTo,hd4,hz4,List.append_nil] at h4
  change Runs program (5*d.length+4) _ (data v4) _ (data v5) at h4
  have he:v5=prepared n d w:=by
    funext s
    cases s with
    | aux a=>cases a <;> simp [v5,v4,v3,v2,v1,v0,prepared,base,view,initialValues]
    | _=>simp [v5,v4,v3,v2,v1,v0,prepared,base,view,initialValues]
  rw [he] at h4
  have h:=join (join (join (join h0 h1') h2) h3) h4
  rw [initial_data]
  convert h using 1
  unfold setupTime
  omega
/-- Exact actual source reaches original content/odd/shifted-magnitude/lost fields, paying every source copy and bit test. -/
theorem source_strip (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (w:List Bool):
    Runs program (5*(signedTape n).length+5*d.length+3*zeros d+14)
      (ctl .start) (initial (signedTape n) d w).data (ctl .signFloor)
      (data (view (base n d w) (odd d) (dropped d n.magnitude) (content d) [lost d n.magnitude])):=by
  have h0:=setup_run n d w
  have h1:=strip_run (base n d w) d hd n.magnitude [true] false
  have h:=join h0 h1
  have hc:setupTime n d+(3*zeros d+3)=5*(signedTape n).length+5*d.length+3*zeros d+14:=by
    unfold setupTime
    omega
  rw [hc] at h
  simpa only [prepared,content,Bool.false_or] using h
end RiemannGaussian.SemiprimeD1StackRecoveryFinishSetup
