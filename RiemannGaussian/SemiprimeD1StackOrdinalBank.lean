/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAssignmentEnumeration
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual padded ordinal bank from a physical unary tally
One fixed procedure allocates a width from the actual tally, then performs
EXACTLY that many real Body/Increment rounds. It never calls complete 2^M
AssignmentEnumeration. All IDs are binary payload words of the acquired common
width; tally/loop/allocation controls are bounded physical metadata only.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackOrdinalBank
namespace A
export SemiprimeD1StackAssignmentLoop (Stack data)
end A
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
namespace Inc
export SemiprimeD1StackIncrementBytecode (Label code entry)
end Inc
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
/-- Four literal control/cache roles, independent of every tally value. -/
inductive Aux where
  | count | remaining | zeroRemaining | copyScratch
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.count,.remaining,.zeroRemaining,.copyScratch]
  (by intro k; cases k <;> simp)
/-- Nine physical Boolean data stacks, including the actual acquired tally. -/
abbrev Stack := A.Stack ⊕ Aux
/-- Retained actual unary tally. No natural cardinality is an input to the code. -/
def count : Stack := .inr .count
/-- Physically decremented iteration markers. -/
def remaining : Stack := .inr .remaining
/-- Physically consumed zero-allocation markers. -/
def zeroRemaining : Stack := .inr .zeroRemaining
/-- Actual output vector of common-width padded ordinal words. -/
def ids : Stack := .inl .output
/-- Current binary counter, initially physically allocated as all-zero bits. -/
def counter : Stack := .inl .word
/-- Actual generic source-preserving copies of the tally. -/
def copyStack (zero : Bool) (k : Fin 3) : Stack :=
  if k=0 then count else if k=1 then (if zero then zeroRemaining else remaining) else .inr .copyScratch
/-- Actual assignment logger, preserving its input binary counter. -/
def bodyStack : Body.Stack→Stack
  | .word => counter
  | .scratch => .inl .scratch
  | .history => .inl .history
/-- Real fixed-width binary increment operands, not a native counter evaluator. -/
def incrementStack : SemiprimeD1TensorTapeFieldMachine.Stack→Stack
  | .input => counter
  | .scratch => .inl .scratch
  | .output => .inl .next
/-- One final actual history reversal, with literal vector nil already seeded. -/
def reverseStack (k : Fin 2) : Stack := if k=0 then .inl .history else ids
/-- Fixed finite control before every original input or tally. -/
inductive Control where
  | start | makeZero | pushZero | copyRemaining | loop | bodyCall | incrementCall | popOverflow
  | moveDrain | movePush (bit : Bool) | restore | restorePush (bit : Bool)
  | clearCounter | seedOutput | reverse | done | abort
  deriving DecidableEq,Fintype
/-- Literal actual Copy, Body, Increment and Reverse inclusions. -/
abbrev Label := Control ⊕ ((Bool×Fin 9) ⊕ (Body.Label ⊕ (Inc.Label ⊕ Fin 4)))
/-- Static labels for one of two real tally copies. -/
def copyLabel (zero : Bool) (pc : Fin 9) : Label := .inr (.inl (zero,pc))
/-- Static labels for the real logger. -/
def bodyLabel (pc : Body.Label) : Label := .inr (.inr (.inl pc))
/-- Static labels for the real binary incrementer. -/
def incrementLabel (pc : Inc.Label) : Label := .inr (.inr (.inr (.inl pc)))
/-- Static labels for the one final reversal. -/
def reverseLabel (pc : Fin 4) : Label := .inr (.inr (.inr (.inr pc)))
/-- Closed physical ordinal-bank producer. ONLY the remaining-marker stack
controls the number of rounds; overflow never controls enumeration length. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl (zero,pc)) => SemiprimeD1StackMultiplierLink.instruction (copyStack zero) (copyLabel zero) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackMultiplierLink.instruction bodyStack bodyLabel (Body.code pc)
  | .inr (.inr (.inr (.inl pc))) => SemiprimeD1StackMultiplierLink.instruction incrementStack incrementLabel (Inc.code pc)
  | .inr (.inr (.inr (.inr pc))) => SemiprimeD1StackMultiplierLink.instruction reverseStack reverseLabel (SemiprimeD1StackReverseWord.code pc)
  | .inl .start => .call (copyLabel true 0) (.inl .makeZero)
  | .inl .makeZero => .base (.pop zeroRemaining (.inl .copyRemaining) (.inl .pushZero) (.inl .pushZero))
  | .inl .pushZero => .base (.push counter false (.inl .makeZero))
  | .inl .copyRemaining => .call (copyLabel false 0) (.inl .loop)
  | .inl .loop => .base (.pop remaining (.inl .clearCounter) (.inl .bodyCall) (.inl .bodyCall))
  | .inl .bodyCall => .call (bodyLabel Body.entry) (.inl .incrementCall)
  | .inl .incrementCall => .call (incrementLabel Inc.entry) (.inl .popOverflow)
  | .inl .popOverflow => .base (.pop (.inl .next) (.inl .abort) (.inl .moveDrain) (.inl .moveDrain))
  | .inl .moveDrain => .base (.pop (.inl .next) (.inl .restore) (.inl (.movePush false)) (.inl (.movePush true)))
  | .inl (.movePush bit) => .base (.push (.inl .scratch) bit (.inl .moveDrain))
  | .inl .restore => .base (.pop (.inl .scratch) (.inl .loop) (.inl (.restorePush false)) (.inl (.restorePush true)))
  | .inl (.restorePush bit) => .base (.push counter bit (.inl .restore))
  | .inl .clearCounter => .base (.pop counter (.inl .seedOutput) (.inl .clearCounter) (.inl .clearCounter))
  | .inl .seedOutput => .base (.push ids false (.inl .reverse))
  | .inl .reverse => .call (reverseLabel 0) (.inl .done)
  | .inl .done | .inl .abort => .base .halt
/-- Literal nine-stack payload; lists/functions here describe physical stores
in proofs, never an executed ordinal getter or enumeration callback. -/
def data (word scratch next history output tally todo zeroTodo copyScratch : List Bool) : Stack→List Bool :=
  Sum.elim (A.data word scratch next history output) (fun role=>match role with
    | .count => tally | .remaining => todo | .zeroRemaining => zeroTodo | .copyScratch => copyScratch)
/-- Actual input is ONLY the physically acquired tally, no binary M or ID bank. -/
def initial (tally : List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,data [] [] [] [] [] tally [] [] [],[]⟩
/-- One fixed finite machine from unary tally data to the binary padded-ID vector. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine count ids (.inl .start) program
/-- Actual copies never alias their source, destination or work buffers. -/
theorem copyStack_injective (zero : Bool) : Function.Injective (copyStack zero) := by cases zero <;> decide
/-- Logger operands are physically distinct. -/
theorem bodyStack_injective : Function.Injective bodyStack := by decide
/-- Increment input/work/output roles are physically distinct. -/
theorem incrementStack_injective : Function.Injective incrementStack := by decide
/-- Final history and output registers are physically distinct. -/
theorem reverseStack_injective : Function.Injective reverseStack := by decide

end RiemannGaussian.SemiprimeD1StackOrdinalBank
