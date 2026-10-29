/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersBounds
/-! # ALL47 data roles and actual return cells at every genuine compiled source prefix
This prepared source has exactly four physical input words; it makes no N-only
initialization claim. Every scratch/shadow and retained input is included.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersStorage
open SemiprimeD1StackRecoveryPowers SemiprimeD1StackRecoveryPowersBounds
open SemiprimeD1StackRecoveryPowersEncoding
open SemiprimeD1StackRecoveryPowersSpec (signed)
open SemiprimeRationalBits (RationalWord)
/-- All four initialized input words are bounded by their actual total byte resource. -/
theorem initial_role_bound (argument:RationalWord) (q:Nat) (width:List Bool) (slot:Stack):
    ((initial (signed argument) argument.denominator (List.replicate q true) width).data slot).length ≤ resource argument q width:=by
  rcases slot with slot|slot
  · change (if slot=SemiprimeD1StackRationalOperation.aux .template then width else []).length ≤ resource argument q width
    split
    · unfold resource;omega
    · simp only [List.length_nil];omega
  · cases slot <;> simp only [initial,input,Sum.elim_inr,List.length_replicate,List.length_nil] <;> unfold resource <;> omega
/-- Every genuine actual source prefix stops before the SAME program's own proved whole halt. -/
theorem prefix_fuel (argument:RationalWord) (q:Nat) (width:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel
      (initial (signed argument) argument.denominator (List.replicate q true) width)=some out):
    fuel≤ polynomial argument q width:=by
  obtain ⟨s,hs,hstop⟩:=source_run_bounded argument q width
  have hbefore:fuel≤ s:=by
    by_contra hn
    have he:fuel=s+(1+(fuel-(s+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done argument q width)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hbefore.trans hs
/-- Whole47-role mass counts every retained Grid word, every actual array/count buffer and every displaced shadow. -/
theorem word_sum (data:Stack→List Bool) (cap:Nat) (h:∀slot,(data slot).length≤ cap):
    (∑slot:Stack,(data slot).length)≤ 47*cap:=SemiprimeD1StackRecoveryPowersOperation.word_sum data cap h
/-- Every actual data cell and every saved real return at the SAME whole-program prefix is paid. -/
theorem prefix_cells (argument:RationalWord) (q:Nat) (width:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel
      (initial (signed argument) argument.denominator (List.replicate q true) width)=some out):
    (∑slot:Stack,(out.data slot).length)+out.frames.length≤ 48*(resource argument q width+polynomial argument q width):=by
  have hf:=prefix_fuel argument q width fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource argument q width)
    (initial (signed argument) argument.denominator (List.replicate q true) width) out (initial_role_bound argument q width) hr
  have hm:=word_sum out.data (resource argument q width+fuel) hd
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel
    (initial (signed argument) argument.denominator (List.replicate q true) width) out hr
  change out.frames.length≤ 0+fuel at hframes
  omega
/-- Fixed whole physical-storage polynomial precedes every actual input and every selected node. -/
def spacePolynomial (argument:RationalWord) (q:Nat) (width:List Bool):Nat:=10^43*(resource argument q width)^10
/-- Same source clock and actual input word mass give a fixed complete47-plus-return cap. -/
theorem cells_le (argument:RationalWord) (q:Nat) (width:List Bool):
    48*(resource argument q width+polynomial argument q width)≤ spacePolynomial argument q width:=by
  have hp:resource argument q width≤ (resource argument q width)^10:=Nat.le_pow (by decide:0<10)
  unfold polynomial spacePolynomial
  omega
/-- All47 Boolean roles plus the actual finite return-cell alphabet are counted at EVERY genuine compiled prefix. -/
theorem machine_prefix_cells (argument:RationalWord) (q:Nat) (width:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (signed argument) argument.denominator (List.replicate q true) width)))=some cfg):
    (∑slot:Stack,(cfg.stk (some slot)).length)+(cfg.stk none).length≤ spacePolynomial argument q width:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .argumentSigned) (aux .output) (.local .start) program fuel
    (initial (signed argument) argument.denominator (List.replicate q true) width)
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel
      (initial (signed argument) argument.denominator (List.replicate q true) width) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact (prefix_cells argument q width fuel out hout).trans (cells_le argument q width)
end RiemannGaussian.SemiprimeD1StackRecoveryPowersStorage
