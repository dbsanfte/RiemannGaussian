/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScopeLeafReady
import RiemannGaussian.SemiprimeD1StackDigitCountBounds
/-! # Actual scope-bank-counted leaf entry, with no M header
The original scope bank is physically copied and every field parsed once. Its
actual count stack aliases the frozen leaf's assignment-width counter directly.
The program then executes the original leaf at makeZero, bypassing binary M
conversion. No supplied cardinality, max-port-index or assignment count occurs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackScopeLeaf
namespace L
export SemiprimeD1StackLeaf (Stack Label program contextStack axes precisionBits vertices aux unaryStack inputData)
end L
namespace D
export SemiprimeD1StackDigitCount (Stack Label program)
end D
namespace X
export SemiprimeD1StackJetContext (Stack Label program)
end X

/-- Fixed leaf bank plus the seven fixed original-cache count roles. -/
abbrev Stack := L.Stack ⊕ D.Stack
/-- Entire literal leaf inclusion, independent of every original input. -/
def leafStack : L.Stack→Stack := Sum.inl
/-- Original immutable scope-bank physical address. -/
def scopes : Stack := .inr .bank
/-- Scope count is written DIRECTLY into the actual leaf counter; all other
scanner registers are distinct actual physical roles. -/
def countStack : D.Stack→Stack
  | .count => leafStack (L.unaryStack .output)
  | k => .inr k
/-- Actual context producer aliases the leaf's original header/cache registers. -/
def contextStack (k : X.Stack) : Stack := leafStack (L.contextStack k)
/-- Fixed finite outer control plus literal real called procedure labels. -/
inductive Label where
  | start | countScopes | callLeaf | done
  | context (pc : X.Label)
  | count (pc : D.Label)
  | leaf (pc : L.Label)
  deriving DecidableEq,Fintype

/-- One fixed closed procedure counts scope records, not used vertex ports;
even unused variables and empty/zero-valued scope fields contribute markers. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label
  | .start => .call (.context .start) .countScopes
  | .countScopes => .call (.count (.inl .main)) .callLeaf
  | .callLeaf => .call (.leaf .makeZero) .done
  | .done => .base .halt
  | .context pc => SemiprimeD1StackValidationLink.instruction contextStack Label.context (X.program pc)
  | .count pc => SemiprimeD1StackValidationLink.instruction countStack Label.count (D.program pc)
  | .leaf pc => SemiprimeD1StackValidationLink.instruction leafStack Label.leaf (L.program pc)

/-- Declarative physical store: literal leaf data plus immutable scope bank;
every other scanner work register is empty between actual called procedures. -/
def data (leaf : L.Stack→List Bool) (scopeBank : List Bool) : Stack→List Bool
  | .inl k => leaf k
  | .inr .bank => scopeBank
  | .inr _ => []
/-- Four actual physical inputs: axes, binary precision, literal records, scope bank.
No binary M/cardinality/counter/assignment answer is initially present. -/
def initial (axisTape pBits vertexTape scopeBank : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨some .start,none,none,data (L.inputData axisTape pBits [] vertexTape) scopeBank,[]⟩
/-- Actual fixed scope-acquiring leaf machine; output is the reached leaf sum. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine scopes (leafStack (L.aux .sum)) Label.start program
/-- Actual count destination and scope/cache/parser registers do not alias. -/
theorem countStack_injective : Function.Injective countStack := by decide
/-- Context acquisition retains genuinely distinct component registers. -/
theorem contextStack_injective : Function.Injective contextStack := by decide

end RiemannGaussian.SemiprimeD1StackScopeLeaf
