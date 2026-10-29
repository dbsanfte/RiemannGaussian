/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingCalls
/-! # Two actual exponent copies and the physically acquired maximum copy -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingSetup
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingPrimitives SemiprimeD1StackSourcePacketPaddingCalls
open SemiprimeD1StackProcedureTrace
/-- The paid copies, including actual source restoration and returns, precede every low-bit scan. -/
def setupTime (a:Nat) (bits:List Bool) :Nat:=10*a+5*bits.length+12
/-- All exponent and maximum bytes come from retained actual source words, never from an advised a/maximum cache. -/
theorem setup_run (src:List Bool) (s:FE.Summary) (a:Nat) :
    Runs program (setupTime a s.maximum) .copyCut (bank (readyWords src s a)) (.cut false)
      (bank {readyWords src s a with cutTodo:=List.replicate a true,prefixTodo:=List.replicate a true,frequency:={ (readyWords src s a).frequency with oldCount:=s.maximum}}) :=by
  let w0:=readyWords src s a
  let w1:Words:={w0 with cutTodo:=List.replicate a true}
  let w2:Words:={w1 with prefixTodo:=List.replicate a true}
  let w3:Words:={w2 with frequency:={w2.frequency with oldCount:=s.maximum}}
  have h0:=copy_call .cut .copyCut .copyPrefix rfl (bank w0) (List.replicate a true) [] rfl rfl rfl
  change Runs program (5*(List.replicate a true).length+4) .copyCut (bank w0) .copyPrefix
    (Function.update (bank w0) (aux .cutTodo) (List.replicate a true++[])) at h0
  rw [List.append_nil,update_cutTodo,List.length_replicate] at h0
  have h1:=copy_call .prefix .copyPrefix .copyMaximum rfl (bank w1) (List.replicate a true) [] rfl rfl rfl
  change Runs program (5*(List.replicate a true).length+4) .copyPrefix (bank w1) .copyMaximum
    (Function.update (bank w1) (aux .prefixTodo) (List.replicate a true++[])) at h1
  rw [List.append_nil,update_prefixTodo,List.length_replicate] at h1
  have h2:=copy_call .maximum .copyMaximum (.cut false) rfl (bank w2) s.maximum [] rfl rfl rfl
  change Runs program (5*s.maximum.length+4) .copyMaximum (bank w2) (.cut false)
    (Function.update (bank w2) (frequencyStack F.oldCount) (s.maximum++[])) at h2
  rw [List.append_nil,update_oldCount] at h2
  have h:=join (join h0 h1) h2
  convert h using 1; unfold setupTime;omega
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingSetup
