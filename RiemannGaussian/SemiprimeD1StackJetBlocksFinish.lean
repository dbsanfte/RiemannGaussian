/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksLoop
/-! # Actual final chronological reverse and complete trailing-source drain -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksFinish
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Every acquired context/input word is retained, and all private work is cleared. -/
def result (context:X.Stack→List Bool) (coefficients blocks output:List Bool) :Stack→List Bool :=
  Function.update (data context coefficients blocks [] [] [] [] [] [] []) (aux .output) output
/-- Final physical output construction and extra-field cleanup have their own exact byte clock. -/
theorem finish_run (context:X.Stack→List Bool) (coefficients blocks reader hist:List Bool) :
    Runs program (2*hist.length+reader.length+5) (ctl .finishSeed)
      (data context coefficients blocks [] reader [] [] [] [] hist) (ctl .done)
      (result context coefficients blocks (hist.reverse++[false])) :=by
  let b0:=data context coefficients blocks [] reader [] [] [] [] hist
  let b1:=Function.update b0 (aux .output) [false]
  let b2:=Function.update (data context coefficients blocks [] reader [] [] [] [] [])
    (aux .output) (hist.reverse++[false])
  have h0:=push_run .finishSeed (ctl .outputReverse) (aux .output) false b0 rfl
  change Runs program 1 (ctl .finishSeed) b0 (ctl .outputReverse) b1 at h0
  have h1:=reverse_call .output .outputReverse .clearReader rfl b1 hist [false] rfl rfl
  have he:Function.update (Function.update b1 (reverseStack .output 0) [])
      (reverseStack .output 1) (hist.reverse++[false])=b2:=by
    change Function.update (Function.update (Function.update
      (data context coefficients blocks [] reader [] [] [] [] hist) (aux .output) [false])
      (aux .history) []) (aux .output) (hist.reverse++[false])=
      Function.update (data context coefficients blocks [] reader [] [] [] [] [])
        (aux .output) (hist.reverse++[false])
    rw [Function.update_comm (by decide:aux .output≠aux .history),Function.update_idem,data_history]
  rw [he] at h1
  have h2:=drain_loop .clearReader (ctl .done) (aux .reader) rfl b2 reader rfl
  have he2:Function.update b2 (aux .reader) []=
      result context coefficients blocks (hist.reverse++[false]):=by
    dsimp only [b2,result]
    rw [Function.update_comm (by decide:aux .output≠aux .reader),data_reader]
  rw [he2] at h2
  have h:=join (join h0 h1) h2
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackJetBlocksFinish
