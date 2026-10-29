/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersExecution
import RiemannGaussian.SemiprimeD1StackRecoveryPowersCost
/-! # Whole SAME-source fixed polynomial from the four actual input byte lengths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersBounds
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersSpec (signed row next suffix array)
open SemiprimeD1StackRecoveryPowersEncoding SemiprimeD1StackRecoveryPowersExecution
open SemiprimeD1StackRecoveryPowersCost
open SemiprimeRationalBits (RationalWord)
/-- All complete row/successor/cleanup iterations are charged from the actual fitted current and history payload, never elapsed operand widths. -/
theorem loopBound_le (argument current:RationalWord) (q:Nat) (width hist:List Bool) (n s:Nat)
    (hs:1 ≤ s) (ha:argument.numerator.magnitude.length ≤ s) (hd:argument.denominator.length ≤ s)
    (hq:q ≤ s) (hn:n ≤ s) (hw:width.length ≤ s)
    (hc:current.numerator.magnitude.length ≤ s) (hcd:current.denominator.length ≤ s)
    (hh:hist.length+(n+1)*(4*s+5) ≤ 10*s^2):
    loopBound argument q width current hist n ≤ (n+1)*(10^34*s^6):=by
  induction n generalizing current hist with
  | zero=>
    have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
    rw [loopBound,SemiprimeD1StackRecoveryPowersRow.timeBound_eq]
    simp only [signed,List.length_cons,Nat.zero_add,Nat.one_mul]
    omega
  | succ n ih=>
    have hr:=row_cap current s hc hcd
    have hinv:((row current).reverse++hist).length+(n+1)*(4*s+5) ≤ 10*s^2:=by
      simp only [List.length_append,List.length_reverse]
      nlinarith only [hh,hr]
    have hl:=SemiprimeD1StackRecoveryPowersSpec.next_lengths width argument current
    have ht:=ih (next width argument current) ((row current).reverse++hist) (by omega)
      (hl.1.le.trans hw) (hl.2.le.trans hw) hinv
    have hop:=operation_cost argument current q n width ((row current).reverse++hist) s hs ha hd hq (by omega) hw hc hcd (by omega)
    have hs6:s ≤ s^6:=Nat.le_pow (by decide:0<6)
    have hrow:=SemiprimeD1StackRecoveryPowersRow.timeBound_eq current
    rw [loopBound]
    nlinarith only [ht,hop,hrow,hc,hcd,hs,hs6]
/-- Uniform clock polynomial, whose coefficient/degree precede every actual argument, q and paid W. -/
def polynomial (argument:RationalWord) (q:Nat) (width:List Bool):Nat:=10^40*(resource argument q width)^10
/-- Own complete entry/halt clock pays binary operands, q markers, W cells, every row and every private-role drain. -/
theorem timeBound_le (argument:RationalWord) (q:Nat) (width:List Bool):
    timeBound argument width q ≤ polynomial argument q width:=by
  let s:=resource argument q width
  have hs:1 ≤ s:=resource_pos argument q width
  have ha:argument.numerator.magnitude.length ≤ s:=by dsimp [s,resource,signed];omega
  have hd:argument.denominator.length ≤ s:=by dsimp [s,resource];omega
  have hw:width.length ≤ s:=by dsimp [s,resource];omega
  have hq:q ≤ s:=by dsimp [s,resource];omega
  have hs10:1 ≤ s^10:=one_le_pow₀ hs
  have hs110:s ≤ s^10:=Nat.le_pow (by decide:0<10)
  have hs210:s^2 ≤ s^10:=Nat.pow_le_pow_right hs (by decide:2 ≤ 10)
  have hs710:s^7 ≤ s^10:=Nat.pow_le_pow_right hs (by decide:7 ≤ 10)
  have hm:q*(4*s+5) ≤ 10*s^2:=by
    have h:=Nat.mul_le_mul_right (4*s+5) hq
    nlinarith
  cases q with
  | zero=>
    unfold timeBound polynomial
    change 10 ≤ 10^40*s^10
    omega
  | succ n=>
    have hl:=loopBound_le argument SemiprimeJetBits.oneWord (n+1) width [] n s hs ha hd hq (by omega) hw hs hs (by simpa using hm)
    have hp:=payload_cap argument SemiprimeJetBits.oneWord width (n+1) s hw hs hs
    change (payload (array width argument (n+1))).length ≤ (n+1)*(4*s+5) at hp
    have ht:(n+1)*(10^34*s^6) ≤ 10^34*s^7:=by
      have h:=Nat.mul_le_mul_right (10^34*s^6) hq
      nlinarith only [h]
    change timeBound argument width (n+1) ≤ 10^40*s^10
    rw [timeBound]
    nlinarith only [hl,hp,hm,ht,hq,hs10,hs110,hs210,hs710]
/-- The SAME proved actual whole source runs within the closed four-input polynomial. -/
theorem source_run_bounded (argument:RationalWord) (q:Nat) (width:List Bool):
    ∃time ≤ polynomial argument q width,SemiprimeD1StackCalls.run program time
      (initial (signed argument) argument.denominator (List.replicate q true) width)=some (done argument q width):=by
  obtain ⟨time,ht,hr⟩:=source_run argument q width
  exact ⟨time,ht.trans (timeBound_le argument q width),hr⟩
/-- Genuine finite47-role machine follows that same actual source and clock. -/
noncomputable def machinePowers (argument:RationalWord) (q:Nat) (width:List Bool):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (signed argument) argument.denominator (List.replicate q true) width))
      (some (SemiprimeD1StackCalls.configuration (done argument q width))) (polynomial argument q width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .argumentSigned) (aux .output) (.local .start) program
  let h:=source_run_bounded argument q width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryPowersBounds
