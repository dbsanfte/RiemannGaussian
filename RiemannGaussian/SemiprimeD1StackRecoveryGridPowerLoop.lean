/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSeed
/-! # Actual internal unary-counted rational power, accumulator FIRST/base SECOND
All counters here are actual marker tapes supplied only by originala copies or
actual acquired multiplicities in the enclosing whole-grid program. Prefix
indices and pure state functions occur only in this executed-trace induction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPowerLoop
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridRegisters SemiprimeD1StackRecoveryGridOperationInput
open SemiprimeD1StackRecoveryGridPowerSeed SemiprimeD1StackProcedureTrace
namespace Op
export SemiprimeD1StackRecoveryGridOperation (operation_run_legacy timeBound)
end Op
namespace Old
export SemiprimeD1RecoveryPowerBits (power)
end Old
/-- Physically popped remaining original/multiplicity markers. -/
def afterPop (w:Words) (remaining:Nat) :Words:=
  {w with auxiliary:=Function.update w.auxiliary .powerTodo (List.replicate remaining true)}
/-- Actual next accumulator obtained by the same original prefix multiplication. -/
def afterStep (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord)
    (k remaining:Nat) (w:Words) :Words:=
  putReg (afterPop w remaining) (powerDestination part) (Old.power width x (k+1)).word
/-- Exact complete internal power output preserves all other actual caller data and clears its consumed marker tape. -/
def finish (w:Words) (part:PowerSite) (out:SemiprimeRationalBits.RationalWord) :Words:=
  {putReg w (powerDestination part) out with auxiliary:=Function.update w.auxiliary .powerTodo []}
/-- Writing two already acquired identical register words changes no actual data. -/
theorem putReg_eq_self (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord)
    (hs:w.registers (r,false)=signed x) (hd:w.registers (r,true)=x.denominator) :putReg w r x=w:=by
  have h0:Function.update w.registers (r,false) (signed x)=w.registers:=by rw [←hs];exact Function.update_eq_self _ _
  have h1:Function.update w.registers (r,true) x.denominator=w.registers:=by rw [←hd];exact Function.update_eq_self _ _
  unfold putReg
  rw [h0,h1]
/-- Final actual accumulator replacement overwrites only the earlier accumulator, not any base/source word. -/
theorem finish_putReg (w:Words) (part:PowerSite) (old out:SemiprimeRationalBits.RationalWord) :
    finish (putReg w (powerDestination part) old) part out=finish w part out:=by
  unfold finish
  rw [putReg_idem,putReg_auxiliary]
/-- Counter updates and earlier power prefixes do not survive the actual final clear/replacement. -/
theorem finish_afterStep (w:Words) (part:PowerSite) (old out:SemiprimeRationalBits.RationalWord) (n:Nat) :
    finish (putReg (afterPop w n) (powerDestination part) old) part out=finish w part out:=by
  rw [finish_putReg]
  unfold finish afterPop
  simp only [Function.update_idem]
  rfl
/-- Own actual loop budget sums actual counter reads, real fitted-operation calls and real returns; no legacy power clock is used. -/
def loopTime (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) :Nat→Nat→Words→Nat
  | _,0,_=>1
  | k,n+1,w=>
    let acc:=(Old.power width x k).word
    1+(Op.timeBound (.power part) (afterPop w n) acc.numerator.negative acc.numerator.magnitude acc.denominator
      x.numerator.negative x.numerator.magnitude x.denominator width+2)+
      loopTime part width x (k+1) n (afterStep part width x k n w)
/-- Every actual unary marker triggers ONE real normalized/twice-fitted multiplication in the original exact operand order. -/
theorem loop_run (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (k n:Nat) (w:Words)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hc:w.auxiliary .powerTodo=List.replicate n true)
    (ha:w.registers (powerDestination part,false)=signed (Old.power width x k).word)
    (had:w.registers (powerDestination part,true)=(Old.power width x k).word.denominator)
    (hx:w.registers (powerBase part,false)=signed x) (hxd:w.registers (powerBase part,true)=x.denominator) :
    ∃q ≤ loopTime part width x k n w,Runs program q (.power part .loop) (bank w) (.power part .done)
      (bank (finish w part (Old.power width x (k+n)).word)):=by
  induction n generalizing k w with
  | zero=>
    have h0:=PTrace.pop_run (.power part .loop) (.power part .done) (.local .abort) (.power part .multiply)
      (aux .powerTodo) (bank w) [] rfl hc
    change Runs program 1 _ _ _ (Function.update (bank w) (aux .powerTodo) []) at h0
    rw [update_auxiliary] at h0
    change Runs program 1 _ _ (.power part .done) _ at h0
    have hself:=putReg_eq_self w (powerDestination part) (Old.power width x k).word ha had
    refine ⟨1,le_rfl,?_⟩
    simpa only [finish,Nat.add_zero,hself] using h0
  | succ n ih=>
    let acc:=(Old.power width x k).word
    let w1:=afterPop w n
    let w2:=afterStep part width x k n w
    have h0:=PTrace.pop_run (.power part .loop) (.power part .done) (.local .abort) (.power part .multiply)
      (aux .powerTodo) (bank w) (List.replicate (n+1) true) rfl hc
    change Runs program 1 _ _ (.power part .multiply)
      (Function.update (bank w) (aux .powerTodo) (List.replicate n true)) at h0
    rw [update_auxiliary] at h0
    have hr1:w1.rational=emptyRational width:=hr
    have hs1:w1.auxiliary .copyScratch=[]:=by
      change Function.update w.auxiliary .powerTodo (List.replicate n true) .copyScratch=[]
      rw [Function.update_of_ne (by decide)]
      exact hs
    obtain ⟨q,hq,hqrun⟩:=Op.operation_run_legacy (.power part) w1 acc.numerator.negative acc.numerator.magnitude acc.denominator
      x.numerator.negative x.numerator.magnitude x.denominator width hr1 hs1 ha had hx hxd
    change Runs program q _ _ _ (bank w2) at hqrun
    have hcall:=PTrace.local_call (.power part .multiply) (.operation (.power part) (.copyInput false false))
      (.operation (.power part) .done) (.power part .loop) rfl rfl q (bank w1) (bank w2) hqrun
    have hr2:w2.rational=emptyRational width:=hr1
    have hs2:w2.auxiliary .copyScratch=[]:=hs1
    have hc2:w2.auxiliary .powerTodo=List.replicate n true:=by
      change Function.update w.auxiliary .powerTodo (List.replicate n true) .powerTodo=_
      exact Function.update_self _ _ _
    have ha2:w2.registers (powerDestination part,false)=signed (Old.power width x (k+1)).word:=
      (putReg_fields w1 (powerDestination part) (Old.power width x (k+1)).word).1
    have hd2:w2.registers (powerDestination part,true)=(Old.power width x (k+1)).word.denominator:=
      (putReg_fields w1 (powerDestination part) (Old.power width x (k+1)).word).2
    have hx2:w2.registers (powerBase part,false)=signed x:=
      (power_base_retained w1 part (Old.power width x (k+1)).word false).trans hx
    have hxd2:w2.registers (powerBase part,true)=x.denominator:=
      (power_base_retained w1 part (Old.power width x (k+1)).word true).trans hxd
    obtain ⟨r,hrunBound,hrun⟩:=ih (k+1) w2 hr2 hs2 hc2 ha2 hd2 hx2 hxd2
    have hout:finish w2 part (Old.power width x (k+1+n)).word=finish w part (Old.power width x (k+(n+1))).word:=by
      change finish (putReg (afterPop w n) (powerDestination part) (Old.power width x (k+1)).word) part _=_
      rw [finish_afterStep]
      rw [show k+1+n=k+(n+1) by omega]
    rw [hout] at hrun
    refine ⟨1+(q+2)+r,?_,PTrace.join (PTrace.join h0 hcall) hrun⟩
    change 1+(q+2)+r ≤1+(Op.timeBound (.power part) w1 acc.numerator.negative acc.numerator.magnitude acc.denominator
      x.numerator.negative x.numerator.magnitude x.denominator width+2)+loopTime part width x (k+1) n w2
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridPowerLoop
