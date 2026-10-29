/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCalls
/-! # Four real operand copies before every grid rational operation
Copies finish before any aliased destination register is erased. The fixed
operation site chooses only actual source/destination addresses, never values.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationInput
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackProcedureTrace
/-- Real operation bank with only the actual supplied W template retained. -/
def emptyRational (width:List Bool) :R.Stack→List Bool:=SemiprimeD1StackRationalOperation.input [] [] [] [] width
/-- Literal four-front-field update, corresponding exactly to the four executed preserving copies. -/
def filled (width ls ld rs rd:List Bool) :R.Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (emptyRational width)
    (SemiprimeD1StackRationalOperation.aux .leftSigned) ls) (SemiprimeD1StackRationalOperation.aux .leftDen) ld)
    (SemiprimeD1StackRationalOperation.aux .rightSigned) rs) (SemiprimeD1StackRationalOperation.aux .rightDen) rd
/-- The actual four writes form EXACTLY the sealed R36 source's honest five-tape input bank. -/
theorem filled_input (width ls ld rs rd:List Bool) :
    filled width ls ld rs rd=SemiprimeD1StackRationalOperation.input ls ld rs rd width:=by
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
theorem inputs_run (site:Site) (w:Words) (width ls ld rs rd:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hls:w.registers (operand site false,false)=ls) (hld:w.registers (operand site false,true)=ld)
    (hrs:w.registers (operand site true,false)=rs) (hrd:w.registers (operand site true,true)=rd) :
    Runs program (inputsTime ls ld rs rd) (.operation site (.copyInput false false)) (bank w)
      (.operation site .call) (bank {w with rational:=SemiprimeD1StackRationalOperation.input ls ld rs rd width}):=by
  let rls:=SemiprimeD1StackRationalOperation.aux .leftSigned
  let rld:=SemiprimeD1StackRationalOperation.aux .leftDen
  let rrs:=SemiprimeD1StackRationalOperation.aux .rightSigned
  let rrd:=SemiprimeD1StackRationalOperation.aux .rightDen
  let w1:Words:={w with rational:=Function.update w.rational rls ls}
  let w2:Words:={w1 with rational:=Function.update w1.rational rld ld}
  let w3:Words:={w2 with rational:=Function.update w2.rational rrs rs}
  let w4:Words:={w3 with rational:=Function.update w3.rational rrd rd}
  have hz0:bank w (copyTarget (.input site false false))=[]:=by
    change w.rational rls=[]
    rw [hr]
    rfl
  have h0:=PTrace.copy_call (.input site false false) (.operation site (.copyInput false false))
    (.operation site (.copyInput false true)) rfl (bank w) ls [] hls hz0 hs
  change Runs _ _ _ _ _ (Function.update (bank w) (rational rls) (ls++[])) at h0
  rw [List.append_nil,update_rational] at h0
  have hz1:bank w1 (copyTarget (.input site false true))=[]:=by
    change Function.update w.rational rls ls rld=[]
    rw [hr]
    rfl
  have h1:=PTrace.copy_call (.input site false true) (.operation site (.copyInput false true))
    (.operation site (.copyInput true false)) rfl (bank w1) ld [] hld hz1 hs
  change Runs _ _ _ _ _ (Function.update (bank w1) (rational rld) (ld++[])) at h1
  rw [List.append_nil,update_rational] at h1
  have hz2:bank w2 (copyTarget (.input site true false))=[]:=by
    change Function.update (Function.update w.rational rls ls) rld ld rrs=[]
    rw [hr]
    rfl
  have h2:=PTrace.copy_call (.input site true false) (.operation site (.copyInput true false))
    (.operation site (.copyInput true true)) rfl (bank w2) rs [] hrs hz2 hs
  change Runs _ _ _ _ _ (Function.update (bank w2) (rational rrs) (rs++[])) at h2
  rw [List.append_nil,update_rational] at h2
  have hz3:bank w3 (copyTarget (.input site true true))=[]:=by
    change Function.update (Function.update (Function.update w.rational rls ls) rld ld) rrs rs rrd=[]
    rw [hr]
    rfl
  have h3:=PTrace.copy_call (.input site true true) (.operation site (.copyInput true true))
    (.operation site .call) rfl (bank w3) rd [] hrd hz3 hs
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
end RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationInput
