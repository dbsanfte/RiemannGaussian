/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineBounds
/-! # All112 actual affine data words and real return cells at every compiled prefix
The initial configuration has the honest five acquired physical input words.
This does not assert N-only initList for a prepared metadata/template source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineStorage
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineBounds
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos)
end R
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (done)
end E
/-- Exactly five actual words start populated; all additional affine words start empty. -/
theorem initial_role_bound (a M u:Nat) (t width:List Bool) (slot:Stack):
    ((initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width).data slot).length≤ R.resource a M u t width:=by
  rcases slot with slot|slot
  · exact SemiprimeD1StackRecoveryGridStorage.initial_role_bound a M u t width slot
  · exact Nat.zero_le _
/-- Every genuine actual source prefix stops before the SAME program's own proved whole halt. -/
theorem prefix_fuel (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some out):
    fuel≤ polynomial a M u t width:=by
  obtain ⟨s,hs,hstop⟩:=source_run_bounded a M u selected t width ht
  have hbefore:fuel≤ s:=by
    by_contra hn
    have he:fuel=s+(1+(fuel-(s+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (E.done a M u selected t width)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hbefore.trans hs
/-- Whole112-role mass counts every retained Grid word, every actual array/count buffer and every displaced shadow. -/
theorem word_sum (data:Stack→List Bool) (cap:Nat) (h:∀slot,(data slot).length≤ cap):
    (∑slot:Stack,(data slot).length)≤ 112*cap:=SemiprimeD1StackRecoveryAffineCleanup.word_sum data cap h
/-- Every actual data cell and every saved real return at the SAME whole-program prefix is paid. -/
theorem prefix_cells (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some out):
    (∑slot:Stack,(out.data slot).length)+out.frames.length≤ 113*(R.resource a M u t width+polynomial a M u t width):=by
  have hf:=prefix_fuel a M u selected t width ht fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (R.resource a M u t width)
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) out (initial_role_bound a M u t width) hr
  have hm:=word_sum out.data (R.resource a M u t width+fuel) hd
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) out hr
  change out.frames.length≤ 0+fuel at hframes
  omega
/-- Fixed whole physical-storage polynomial precedes every actual input and every selected node. -/
def spacePolynomial (a M u:Nat) (t width:List Bool):Nat:=10^78*(R.resource a M u t width)^14
/-- Same source clock and actual input word mass give a fixed complete112-plus-return cap. -/
theorem cells_le (a M u:Nat) (t width:List Bool):
    113*(R.resource a M u t width+polynomial a M u t width)≤ spacePolynomial a M u t width:=by
  have hp:R.resource a M u t width≤ (R.resource a M u t width)^14:=Nat.le_pow (by decide:0<14)
  unfold polynomial spacePolynomial
  omega
/-- All112 Boolean roles plus the actual finite return-cell alphabet are counted at EVERY genuine compiled prefix. -/
theorem machine_prefix_cells (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)))=some cfg):
    (∑slot:Stack,(cfg.stk (some slot)).length)+(cfg.stk none).length≤ spacePolynomial a M u t width:=by
  have he:=SemiprimeD1StackCalls.run_correct (oldAux .originalA) (aux .array) (.local .start) program fuel
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact (prefix_cells a M u selected t width ht fuel out hout).trans (cells_le a M u t width)
end RiemannGaussian.SemiprimeD1StackRecoveryAffineStorage
