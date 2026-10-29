/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixOriginal
import RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
import RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackValidationLink
/-! # Closed physical mixed-radix routing instruction table
Axes, indices, all suffix products and digit tests are actual Boolean stack data.
The included supplier computes its own suffixes. No route/rank/Fits answer is an
argument. Correctness and quantitative wrappers are proved separately.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRoute
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
/-- Nineteen fixed physical argument, cache and scratch stacks. -/
inductive Stack | axes | reverseAxes | axis | radix | product | records | scratch | valid | left | right | result | q | d | copied | divScratch | quotLeft | remLeft | quotRight | remRight deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.axes,.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid,.left,.right,.result,.q,.d,.copied,.divScratch,.quotLeft,.remLeft,.quotRight,.remRight}
  complete := by intro k; cases k <;> simp
/-- Finite fixed copying, parsing, arithmetic, cleanup and return phases. -/
inductive Control | copyLeft | copyRight | suffixCall | suffixDone | clearRank | recordPeek | readQ | qDone | readD | dDone | divideLeft | divideRight | compareCall | compareDone | clearD | moveLeft | pushLeft | moveRight | pushRight | baseLeft | baseRight | success | reject | halt | fail (k : Fin 19) deriving DecidableEq,Inhabited,Repr
instance : Fintype Control := Fintype.ofList
  ([.copyLeft,.copyRight,.suffixCall,.suffixDone,.clearRank,.recordPeek,.readQ,.qDone,.readD,.dDone,.divideLeft,.divideRight,.compareCall,.compareDone,.clearD,.moveLeft,.pushLeft,.moveRight,.pushRight,.baseLeft,.baseRight,.success,.reject,.halt]++(List.finRange 19).map .fail)
  (by intro k; cases k <;> simp)
/-- Fixed disjoint labels of all literal included components and routing control. -/
abbrev Label := SemiprimeD1StackJetSuffix.Label ⊕ (Fin 9 ⊕ (Fin 9 ⊕ (SemiprimeD1TensorTapeFieldBytecode.Label ⊕ (SemiprimeD1TensorTapeFieldBytecode.Label ⊕ (SemiprimeD1StackUnaryDivmodBytecode.Label ⊕ (SemiprimeD1StackUnaryDivmodBytecode.Label ⊕ (SemiprimeD1StackUnarySumLessBytecode.Label ⊕ (Control))))))))
/-- Static inclusion of the internally acquiring suffix procedure. -/
def suffixLabel (l : SemiprimeD1StackJetSuffix.Label) : Label := Sum.inl (l)
/-- Static inclusion of the left-index copy procedure. -/
def copyLeftLabel (l : Fin 9) : Label := Sum.inr (Sum.inl (l))
/-- Static inclusion of the right-index copy procedure. -/
def copyRightLabel (l : Fin 9) : Label := Sum.inr (Sum.inr (Sum.inl (l)))
/-- Static inclusion of the acquired axis-field reader. -/
def fieldQLabel (l : SemiprimeD1TensorTapeFieldBytecode.Label) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inl (l))))
/-- Static inclusion of the acquired divisor-field reader. -/
def fieldDLabel (l : SemiprimeD1TensorTapeFieldBytecode.Label) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l)))))
/-- Static inclusion of actual left quotient/remainder acquisition. -/
def divideLeftLabel (l : SemiprimeD1StackUnaryDivmodBytecode.Label) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l))))))
/-- Static inclusion of actual right quotient/remainder acquisition. -/
def divideRightLabel (l : SemiprimeD1StackUnaryDivmodBytecode.Label) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l)))))))
/-- Static inclusion of physical quotient-sum comparison. -/
def compareLabel (l : SemiprimeD1StackUnarySumLessBytecode.Label) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l))))))))
/-- Fixed outer routing control label. -/
def control (c : Control) : Label := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (c))))))))
/-- Literal suffix-procedure stack inclusion; operand caches are disjoint. -/
def suffixStack : SemiprimeD1StackJetSuffix.Stack→Stack
  | .axes=>.axes | .reverseAxes=>.reverseAxes | .axis=>.axis | .radix=>.radix
  | .product=>.product | .records=>.records | .scratch=>.scratch | .valid=>.valid

/-- Static operand copy wiring; both copies share actual result/scratch stacks. -/
def copyStack (right : Bool) : Fin 3→Stack := fun k=>
  if k=0 then (if right then .right else .left) else if k=1 then .result else .scratch

/-- Static acquired-field reader wiring. -/
def fieldStack (denominator : Bool) : SemiprimeD1TensorTapeFieldBytecode.Stack→Stack
  | .inl .input=>.records | .inl .scratch=>.scratch
  | .inl .output=>if denominator then .d else .q | .inr _=>.valid

/-- Static divmod operand, divisor and quotient/remainder wiring. -/
def divideStack (right : Bool) : SemiprimeD1StackUnaryDivmod.Stack→Stack
  | .input=>if right then .right else .left
  | .divisor=>.d | .copied=>.copied | .scratch=>.divScratch
  | .quotient=>if right then .quotRight else .quotLeft
  | .remainder=>if right then .remRight else .remLeft

/-- Static digit-comparator wiring. -/
def compareStack : SemiprimeD1StackUnarySumLess.Stack→Stack
  | .left=>.quotLeft | .right=>.quotRight | .limit=>.q | .valid=>.valid

/-- The entire fixed bank visited on actual failure cleanup. -/
def clearStack (k : Fin 19) : Stack :=
  if k=0 then .axes else
  if k=1 then .reverseAxes else
  if k=2 then .axis else
  if k=3 then .radix else
  if k=4 then .product else
  if k=5 then .records else
  if k=6 then .scratch else
  if k=7 then .valid else
  if k=8 then .left else
  if k=9 then .right else
  if k=10 then .result else
  if k=11 then .q else
  if k=12 then .d else
  if k=13 then .copied else
  if k=14 then .divScratch else
  if k=15 then .quotLeft else
  if k=16 then .remLeft else
  if k=17 then .quotRight else
  .remRight
/-- Closed literal routing instruction table, fixed before every input and context. -/
def code : Label→C.Instruction Stack Label
  | Sum.inl (l) => SemiprimeD1StackValidationLink.instruction suffixStack suffixLabel (SemiprimeD1StackJetSuffix.code l)
  | Sum.inr (Sum.inl (l)) => SemiprimeD1StackMultiplierLink.instruction (copyStack false) copyLeftLabel (SemiprimeD1StackCopy.code l)
  | Sum.inr (Sum.inr (Sum.inl (l))) => SemiprimeD1StackMultiplierLink.instruction (copyStack true) copyRightLabel (SemiprimeD1StackCopy.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (l)))) => SemiprimeD1StackMultiplierLink.instruction (fieldStack false) fieldQLabel (SemiprimeD1TensorTapeFieldBytecode.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l))))) => SemiprimeD1StackMultiplierLink.instruction (fieldStack true) fieldDLabel (SemiprimeD1TensorTapeFieldBytecode.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l)))))) => SemiprimeD1StackMultiplierLink.instruction (divideStack false) divideLeftLabel (SemiprimeD1StackUnaryDivmodBytecode.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l))))))) => SemiprimeD1StackMultiplierLink.instruction (divideStack true) divideRightLabel (SemiprimeD1StackUnaryDivmodBytecode.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l)))))))) => SemiprimeD1StackMultiplierLink.instruction compareStack compareLabel (SemiprimeD1StackUnarySumLessBytecode.code l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (c)))))))) =>
    match c with
    | .copyLeft=>.call (copyLeftLabel 0) (control .copyRight)
    | .copyRight=>.call (copyRightLabel 0) (control .suffixCall)
    | .suffixCall=>.call (suffixLabel (SemiprimeD1StackJetSuffix.control .vector)) (control .suffixDone)
    | .suffixDone=>.base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .clearRank))
    | .clearRank=>.base (.pop .radix (control .recordPeek) (control .clearRank) (control .clearRank))
    | .recordPeek=>.base (.peek .records (control .baseLeft) (control .readQ) (control .readQ))
    | .readQ=>.call (fieldQLabel (SemiprimeD1TensorTapeFieldBytecode.active .tagPop (none,false))) (control .qDone)
    | .qDone=>.base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .readD))
    | .readD=>.call (fieldDLabel (SemiprimeD1TensorTapeFieldBytecode.active .tagPop (none,false))) (control .dDone)
    | .dDone=>.base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .divideLeft))
    | .divideLeft=>.call (divideLeftLabel SemiprimeD1StackUnaryDivmodBytecode.entry) (control .divideRight)
    | .divideRight=>.call (divideRightLabel SemiprimeD1StackUnaryDivmodBytecode.entry) (control .compareCall)
    | .compareCall=>.call (compareLabel SemiprimeD1StackUnarySumLessBytecode.entry) (control .compareDone)
    | .compareDone=>.base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .clearD))
    | .clearD=>.base (.pop .d (control .moveLeft) (control .clearD) (control .clearD))
    | .moveLeft=>.base (.pop .remLeft (control .moveRight) (control .pushLeft) (control .pushLeft))
    | .pushLeft=>.base (.push .left true (control .moveLeft))
    | .moveRight=>.base (.pop .remRight (control .recordPeek) (control .pushRight) (control .pushRight))
    | .pushRight=>.base (.push .right true (control .moveRight))
    | .baseLeft=>.base (.peek .left (control .baseRight) (control (.fail 0)) (control (.fail 0)))
    | .baseRight=>.base (.peek .right (control .success) (control (.fail 0)) (control (.fail 0)))
    | .success=>.base (.push .valid true (control .halt))
    | .fail k=>.base (.pop (clearStack k)
        (if h:k.val+1<19 then control (.fail ⟨k.val+1,h⟩) else control .reject)
        (control (.fail k)) (control (.fail k)))
    | .reject=>.base (.push .valid false (control .halt))
    | .halt=>.base .halt

/-- Actual finite-control, finite-alphabet routing stack machine. -/
def machine := SemiprimeD1StackCalls.machine Stack.axes Stack.result (control .copyLeft) code

end RiemannGaussian.SemiprimeD1StackJetRoute
