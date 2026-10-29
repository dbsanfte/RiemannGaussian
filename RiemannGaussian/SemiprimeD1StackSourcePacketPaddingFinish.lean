/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBits
/-! # Actual zero bits, reversal and final compact trim, retaining the whole frequency bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingFinish
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingPrimitives SemiprimeD1StackSourcePacketPaddingBits
open SemiprimeD1StackProcedureTrace
/-- Every marker, output bit, scratch reverse and final compact-trim call/return is counted. -/
def finishTime (a:Nat) (bits:List Bool) :Nat:=2*a+1+(2*(prefixed a bits).length+3)+
  (SemiprimeD1StackReduceExecution.trimTime (prefixed a bits).reverse+1)
/-- The actual binary result is produced from bytes, with no exponentiation/rounded-answer instruction. -/
theorem finish_run (src:List Bool) (s:FE.Summary) (a:Nat) :
    Runs program (finishTime a s.maximum) .prefix
      (bank {readyWords src s a with prefixTodo:=List.replicate a true,frequency:={ (readyWords src s a).frequency with count:=roundedHigh a s.maximum}}) .done
      (bank {readyWords src s a with padding:=rounded a s.maximum}) :=by
  let w0:=readyWords src s a
  let w1:Words:={w0 with frequency:={w0.frequency with count:=prefixed a s.maximum}}
  let w2:Words:={w0 with frequency:={w0.frequency with trimScratch:=(prefixed a s.maximum).reverse}}
  have h0:=prefix_run a (roundedHigh a s.maximum) w0
  change Runs program (2*a+1) .prefix _ .reverse (bank w1) at h0
  have h1:=reverse_call .reverse .trim rfl (bank w1) (prefixed a s.maximum) [] rfl rfl
  change Runs program (2*(prefixed a s.maximum).length+3) .reverse (bank w1) .trim
    (Function.update (Function.update (bank w1) (frequencyStack (F.aux .count)) [])
      (frequencyStack (F.aux .trimScratch)) ((prefixed a s.maximum).reverse++[])) at h1
  rw [List.append_nil,update_count,update_trimScratch] at h1
  change Runs program (2*(prefixed a s.maximum).length+3) .reverse (bank w1) .trim (bank w2) at h1
  have h2:=trim_call .trim .done rfl (bank w2) (prefixed a s.maximum).reverse [] rfl rfl rfl rfl
  change Runs program (SemiprimeD1StackReduceExecution.trimTime (prefixed a s.maximum).reverse+1) .trim (bank w2) .done
    (Function.update (Function.update (bank w2) (frequencyStack (F.aux .trimScratch)) []) (aux .padding)
      (SemiprimeD1StackReduceExecution.trimReverse (prefixed a s.maximum).reverse++[])) at h2
  rw [List.append_nil,update_trimScratch,update_padding] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingFinish
