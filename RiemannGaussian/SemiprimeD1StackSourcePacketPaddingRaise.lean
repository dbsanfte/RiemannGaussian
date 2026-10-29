/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingCalls
/-! # Optional physically computed compact high-suffix increment -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingRaise
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingPrimitives SemiprimeD1StackSourcePacketPaddingCalls
open SemiprimeD1StackProcedureTrace
/-- Both branches pay the actual high suffix and preserve every retained source/cache/exponent word. -/
theorem raise_run (src:List Bool) (s:FE.Summary) (a:Nat) :
    ∃q≤50*(s.maximum.length+1),Runs program q (.cutDone (SemiprimeD1PacketRoundBits.cut a s.maximum).low)
      (bank {readyWords src s a with prefixTodo:=List.replicate a true,frequency:={ (readyWords src s a).frequency with oldCount:=high a s.maximum}}) .prefix
      (bank {readyWords src s a with prefixTodo:=List.replicate a true,frequency:={ (readyWords src s a).frequency with count:=roundedHigh a s.maximum}}) :=by
  let w0:Words:={readyWords src s a with prefixTodo:=List.replicate a true,frequency:={ (readyWords src s a).frequency with oldCount:=high a s.maximum}}
  have hl:(high a s.maximum).length≤ s.maximum.length:=SemiprimeD1PacketRoundBits.cut_length a s.maximum
  cases ha:(SemiprimeD1PacketRoundBits.cut a s.maximum).low with
  | false=>
    have h0:=copy_call .high (.cutDone false) .clearHigh rfl (bank w0) (high a s.maximum) [] rfl rfl rfl
    change Runs program (5*(high a s.maximum).length+4) (.cutDone false) (bank w0) .clearHigh
      (Function.update (bank w0) (frequencyStack (F.aux .count)) (high a s.maximum++[])) at h0
    rw [List.append_nil,update_count] at h0
    have h1:=drain_loop .clearHigh .prefix (frequencyStack F.oldCount) rfl
      (bank {w0 with frequency:={w0.frequency with count:=high a s.maximum}}) (high a s.maximum) rfl
    rw [update_oldCount] at h1
    have h:=join h0 h1
    refine ⟨(5*(high a s.maximum).length+4)+((high a s.maximum).length+1),by omega,?_⟩
    simp only [ha,roundedHigh,ite_false,Bool.false_eq_true]
    convert h using 1
    funext k;rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  | true=>
    obtain ⟨q,hq,hr⟩:=counter_call (bank w0) (high a s.maximum) rfl rfl rfl rfl rfl rfl rfl
    rw [update_oldCount,update_count] at hr
    refine ⟨q,by omega,?_⟩
    simp only [ha,roundedHigh,ite_true]
    convert hr using 1
    funext k;rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingRaise
