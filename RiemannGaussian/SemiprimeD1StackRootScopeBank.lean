/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueBounds
import RiemannGaussian.SemiprimeD1StackEdgeCountLoop
import RiemannGaussian.SemiprimeD1StackOrdinalBank
/-! # Actual N-only canonical occurrence-ordinal scope bank
Edge13 executes ONCE. Its six-field original-wire tape is physically scanned,
acquiring E and M=2E tallies. The generic physical tally engine then generates
plain canonical Fin M ordinals. No wire-pair/incidence-order identification is
claimed: a factor-major port supplier uses its own actual ordinal to read this bank.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackRootScopeBank
namespace E
export SemiprimeD1StackEdgeCatalogue (Stack Label program input catStack aux)
end E
namespace D
export SemiprimeD1StackEdgeCount (Stack Label program)
end D
namespace O
export SemiprimeD1StackOrdinalBank (Stack Label program count ids)
end O
/-- Original metadata source, seven count roles and nine ordinal-engine roles. -/
abbrev Stack := E.Stack ⊕ (D.Stack ⊕ O.Stack)
/-- Every original source/cache register is retained literally. -/
def edgeStack : E.Stack→Stack := Sum.inl
/-- The counter reads the ACTUAL acquired tape, not an advised descriptor list. -/
def countStack (k : D.Stack) : Stack :=
  if k=SemiprimeD1StackDigitCount.Stack.bank then edgeStack (E.aux .output) else .inr (.inl k)
/-- Actual M tally; this is the physical source for width/loop allocation. -/
def count : Stack := .inr (.inl .count)
/-- Actual E tally retained for owner metadata; no E-ID bank is produced. -/
def wireCount : Stack := .inr (.inl .copyScratch)
/-- The engine's readonly tally aliases the actually acquired M count directly. -/
def ordinalStack (k : O.Stack) : Stack := if k=O.count then count else .inr (.inr k)
/-- Actual padded canonical occurrence-ID vector, in ordinal order. -/
def ids : Stack := ordinalStack O.ids
/-- Original binary N is the ONLY initially present data. -/
def originalInput : Stack := edgeStack (E.catStack SemiprimeD1StackVertexCatalogue.originalInput)
/-- Finite literal caller and actual included component labels. -/
inductive Control where
  | start | countTape | buildIds | done
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.countTape,.buildIds,.done]
  (by intro k; cases k <;> simp)
/-- Static fixed procedure labels, never input-sized generated code. -/
abbrev Label := Control ⊕ (E.Label ⊕ (D.Label ⊕ O.Label))
/-- Actual source labels. -/
def edgeLabel (pc : E.Label) : Label := .inr (.inl pc)
/-- Actual six-field counter labels. -/
def countLabel (pc : D.Label) : Label := .inr (.inr (.inl pc))
/-- Actual physical ordinal-bank engine labels. -/
def ordinalLabel (pc : O.Label) : Label := .inr (.inr (.inr pc))
/-- One fixed N-only source→six-field count→M-ordinal-bank program. The buildIds
entry is also a reusable ready stage for already-acquired source/count caches. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label
  | .inl .start => .call (edgeLabel (.inl .main)) (.inl .countTape)
  | .inl .countTape => .call (countLabel (.inl .start)) (.inl .buildIds)
  | .inl .buildIds => .call (ordinalLabel (.inl .start)) (.inl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction edgeStack edgeLabel (E.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction countStack countLabel (D.program pc)
  | .inr (.inr (.inr pc)) => SemiprimeD1StackValidationLink.instruction ordinalStack ordinalLabel (O.program pc)
/-- Exact physical three-bank store; semantic functions describe fixed data
registers in proofs, never runtime descriptor or ordinal getters. -/
def data (source : E.Stack→List Bool) (counts : D.Stack→List Bool) (bank : O.Stack→List Bool) : Stack→List Bool :=
  Sum.elim source (Sum.elim counts bank)
/-- Native-independent physical input store, N alone; all work/caches start empty. -/
def input (bits : List Bool) : Stack→List Bool := data (E.input bits) (fun _=>[]) (fun _=>[])
/-- Actual N-only entry configuration. -/
def initial (bits : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨some (.inl .start),none,none,input bits,[]⟩
/-- One fixed finite machine with original binary N input and actual scope-bank output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput ids (.inl .start) program
/-- Every source register is genuinely distinct. -/
theorem edgeStack_injective : Function.Injective edgeStack := by intro a b h;exact Sum.inl.inj h
/-- Counter source/reader/count/field/work roles do not physically alias. -/
theorem countStack_injective : Function.Injective countStack := by decide
/-- The actual readonly M cache and engine work/output roles are distinct. -/
theorem ordinalStack_injective : Function.Injective ordinalStack := by decide

end RiemannGaussian.SemiprimeD1StackRootScopeBank
