/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersView
/-! # All four actual cached-power operands are acquired before destination erasure -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationInput
open SemiprimeD1StackRecoveryPowers SemiprimeD1StackRecoveryPowersView SemiprimeD1StackProcedureTrace
namespace PTrace
export SemiprimeD1StackRecoveryPowersPrimitives (join copy_call push_run pop_run drain_loop frame_call reverse_call)
end PTrace
/-- Literal four-front-field update, corresponding exactly to the four executed preserving copies. -/
def filled (width ls ld rs rd:List Bool) :R.Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (emptyRational width)
    (SemiprimeD1StackRationalOperation.aux .leftSigned) ls) (SemiprimeD1StackRationalOperation.aux .leftDen) ld)
    (SemiprimeD1StackRationalOperation.aux .rightSigned) rs) (SemiprimeD1StackRationalOperation.aux .rightDen) rd
/-- The actual four writes form EXACTLY the sealed R36 source's honest five-tape input bank. -/
theorem filled_input (width ls ld rs rd:List Bool) :
    filled width ls ld rs rd=SemiprimeD1StackRationalOperation.input ls ld rs rd width:=by
  rw [filled,emptyRational_input]
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- Four actual preserving copies include all input bytes, restoration loops and real caller returns. -/
def inputsTime (ls ld rs rd:List Bool) :Nat:=5*(ls.length+ld.length+rs.length+rd.length)+16
/-- Actual cached operands initialize R36 before an aliased output register may be changed. -/
theorem inputs_run (w:Words) (width ls ld rs rd:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.added .copyScratch=[])
    (hls:w.added .currentSigned=ls) (hld:w.added .currentDen=ld)
    (hrs:w.added .argumentSigned=rs) (hrd:w.added .argumentDen=rd) :
    Runs program (inputsTime ls ld rs rd) (.local (.input false false)) (bank w)
      (.local .multiply) (bank {w with rational:=SemiprimeD1StackRationalOperation.input ls ld rs rd width}):=by
  let rls:=SemiprimeD1StackRationalOperation.aux .leftSigned
  let rld:=SemiprimeD1StackRationalOperation.aux .leftDen
  let rrs:=SemiprimeD1StackRationalOperation.aux .rightSigned
  let rrd:=SemiprimeD1StackRationalOperation.aux .rightDen
  let w1:Words:={w with rational:=Function.update w.rational rls ls}
  let w2:Words:={w1 with rational:=Function.update w1.rational rld ld}
  let w3:Words:={w2 with rational:=Function.update w2.rational rrs rs}
  let w4:Words:={w3 with rational:=Function.update w3.rational rrd rd}
  have hz0:bank w (copyTarget (.input false false))=[]:=by
    change w.rational rls=[]
    rw [hr]
    rfl
  have h0:=PTrace.copy_call (.input false false) (.local (.input false false))
    (.local (.input false true)) rfl (bank w) ls [] hls hz0 hs
  change Runs _ _ _ _ _ (Function.update (bank w) (rational rls) (ls++[])) at h0
  rw [List.append_nil,update_rational] at h0
  have hz1:bank w1 (copyTarget (.input false true))=[]:=by
    change Function.update w.rational rls ls rld=[]
    rw [hr]
    rfl
  have h1:=PTrace.copy_call (.input false true) (.local (.input false true))
    (.local (.input true false)) rfl (bank w1) ld [] hld hz1 hs
  change Runs _ _ _ _ _ (Function.update (bank w1) (rational rld) (ld++[])) at h1
  rw [List.append_nil,update_rational] at h1
  have hz2:bank w2 (copyTarget (.input true false))=[]:=by
    change Function.update (Function.update w.rational rls ls) rld ld rrs=[]
    rw [hr]
    rfl
  have h2:=PTrace.copy_call (.input true false) (.local (.input true false))
    (.local (.input true true)) rfl (bank w2) rs [] hrs hz2 hs
  change Runs _ _ _ _ _ (Function.update (bank w2) (rational rrs) (rs++[])) at h2
  rw [List.append_nil,update_rational] at h2
  have hz3:bank w3 (copyTarget (.input true true))=[]:=by
    change Function.update (Function.update (Function.update w.rational rls ls) rld ld) rrs rs rrd=[]
    rw [hr]
    rfl
  have h3:=PTrace.copy_call (.input true true) (.local (.input true true))
    (.local .multiply) rfl (bank w3) rd [] hrd hz3 hs
  change Runs _ _ _ _ _ (Function.update (bank w3) (rational rrd) (rd++[])) at h3
  rw [List.append_nil,update_rational] at h3
  have hw:w4={w with rational:=SemiprimeD1StackRationalOperation.input ls ld rs rd width}:=by
    change {w with rational:=Function.update (Function.update (Function.update (Function.update w.rational rls ls) rld ld) rrs rs) rrd rd}=_
    rw [hr]
    change {w with rational:=filled width ls ld rs rd}=_
    rw [filled_input]
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  change Runs program _ _ _ _ (bank w4) at h
  rw [hw] at h
  convert h using 1
  unfold inputsTime
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationInput
