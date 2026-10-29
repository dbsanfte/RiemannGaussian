/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOperation
import RiemannGaussian.SemiprimeD1StackRecoveryPowersRow
/-! # Exact complete-array physical loop and stopped-bank specifications -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersEncoding
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed row next array vector suffix)
open SemiprimeRationalBits (RationalWord)
/-- Payload has no terminal until the one final reversal. -/
def payload (xs:List RationalWord):List Bool:=xs.flatMap row
/-- Two-field vector codec is exactly payload followed by the actual FALSE sentinel. -/
theorem vector_payload (xs:List RationalWord):vector xs=payload xs++[false]:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [vector,payload,List.flatMap_cons,ih,List.append_assoc]
/-- Exact full47-word loop invariant; all parser/helper/shadow work is empty. -/
def loopWords (argument:RationalWord) (q:Nat) (width:List Bool) (current:RationalWord) (remaining:Nat) (history:List Bool):Words:=
  ⟨emptyRational width,fun k=>match k with
    | .argumentSigned=>signed argument | .argumentDen=>argument.denominator | .q=>List.replicate q true
    | .remaining=>List.replicate remaining true | .currentSigned=>signed current | .currentDen=>current.denominator
    | .history=>history | _=>[]⟩
/-- All retained originals survive the source; only the exact complete chronological output is added. -/
def result (argument:RationalWord) (q:Nat) (width:List Bool):Stack→List Bool:=
  Function.update (input (signed argument) argument.denominator (List.replicate q true) width)
    (aux .output) (vector (array width argument q))
/-- Exact actual whole halt has no transient flags or genuine saved returns. -/
def done (argument:RationalWord) (q:Nat) (width:List Bool):C.State Stack Label:=
  ⟨none,none,none,result argument q width,[]⟩
/-- Exact input resource pays numeric words by bytes and unary metadata/template by their actual physical values. -/
def resource (argument:RationalWord) (q:Nat) (width:List Bool):Nat:=
  (signed argument).length+argument.denominator.length+q+width.length+1
/-- All four real source tapes have a positive total-byte budget. -/
theorem resource_pos (argument:RationalWord) (q:Nat) (width:List Bool):1≤resource argument q width:=by
  unfold resource;omega
/-- Updating consumed remaining markers agrees literally with the actual loop state. -/
theorem loop_remaining (argument:RationalWord) (q:Nat) (width:List Bool) (current:RationalWord) (n m:Nat) (hist:List Bool):
    put (loopWords argument q width current n hist) .remaining (List.replicate m true)=loopWords argument q width current m hist:=by
  unfold put loopWords
  congr 1
  funext k
  cases k <;> rfl
/-- One reversed row is logged without altering current rational or any original byte. -/
theorem loop_history (argument:RationalWord) (q:Nat) (width:List Bool) (current:RationalWord) (n:Nat) (hist newHist:List Bool):
    put (loopWords argument q width current n hist) .history newHist=loopWords argument q width current n newHist:=by
  unfold put loopWords
  congr 1
  funext k
  cases k <;> rfl
/-- Real output/sign acquisition updates exactly the two current fields. -/
theorem loop_current (argument:RationalWord) (q:Nat) (width:List Bool) (current out:RationalWord) (n:Nat) (hist:List Bool):
    SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent (loopWords argument q width current n hist) out=
      loopWords argument q width out n hist:=by
  unfold SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent loopWords
  congr 1
  funext k
  cases k <;> rfl
/-- True loop endpoint clears both current fields and every remaining marker. -/
def stoppedWords (argument:RationalWord) (q:Nat) (width hist:List Bool):Words:=
  put (originals (signed argument) argument.denominator (List.replicate q true) width) .history hist
/-- Exact recursive OWN source budget, with actual reached words in every included operation. -/
def loopBound (argument:RationalWord) (q:Nat) (width:List Bool) (current:RationalWord) (hist:List Bool):Nat→Nat
  | 0=>SemiprimeD1StackRecoveryPowersRow.timeBound current+1+(signed current).length+1+current.denominator.length+1
  | n+1=>
    let logged:Words:=loopWords argument q width current n ((row current).reverse++hist)
    SemiprimeD1StackRecoveryPowersRow.timeBound current+1+
      SemiprimeD1StackRecoveryPowersOperation.timeBound logged current.numerator.negative current.numerator.magnitude current.denominator
        argument.numerator.negative argument.numerator.magnitude argument.denominator width+
      loopBound argument q width (next width argument current) ((row current).reverse++hist) n
end RiemannGaussian.SemiprimeD1StackRecoveryPowersEncoding
