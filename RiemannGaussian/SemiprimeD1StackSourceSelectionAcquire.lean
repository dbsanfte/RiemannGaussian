/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOriginal
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysOriginal
/-! # Actual rows/count/dimension to the complete original selected-key vector
Only the physical owner-row tape, actual unary n and actual unary a enter.
The program really acquires occurrences/F, acquires the complete alphabet and
powers, selects every original variable, then reads every selected joint key.
Eleven preserving copies connect the actual stopped banks. Every154 allocated
role is counted. No graph, selected prefix, dictionary, count, score or key
getter is a runtime operand; original-N acquisition is an upstream caller join.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquire
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Occ
export SemiprimeD1StackSourceOccurrences (Stack Label program initial stack_card)
end Occ
namespace Alpha
export SemiprimeD1StackSourceAlphabet64 (Stack Label program initial aux stack_card)
end Alpha
namespace Select
export SemiprimeD1StackSourceIncidenceSelect
  (Stack Label program queryStack aux dictionary nextKey selected stack_card)
end Select
namespace Keys
export SemiprimeD1StackSourceSelectedKeys (Stack Label program environmentStack aux stack_card)
end Keys
namespace Env
export SemiprimeD1StackSourceEnvironment (Stack aux)
end Env
/-- All21 occurrence,30 alphabet,63 selector,39 selected-key and one actual copy-scratch roles. -/
abbrev Stack :=Occ.Stack⊕(Alpha.Stack⊕(Select.Stack⊕(Keys.Stack⊕Unit)))
/-- Complete actual occurrence acquisition bank. -/
def occurrenceStack :Occ.Stack→Stack :=Sum.inl
/-- Complete actual alphabet acquisition bank. -/
def alphabetStack (k:Alpha.Stack) :Stack :=.inr (.inl k)
/-- Complete actual selector bank, including every actual query/cache field. -/
def selectorStack (k:Select.Stack) :Stack :=.inr (.inr (.inl k))
/-- Complete actual selected-key source bank, including every retained environment field. -/
def keyStack (k:Keys.Stack) :Stack :=.inr (.inr (.inr (.inl k)))
/-- One restoring-copy scratch; every component shadow remains allocated. -/
def copyScratch :Stack :=.inr (.inr (.inr (.inr ())))
/-- Eleven fixed copy code sites, independent of every data count or selected value. -/
inductive Copy where
  | occurrences | catalogue | square | cube | fourth | owners | factors | dictionary | nextKey | prefix | keySource
  deriving DecidableEq,Repr
instance :Fintype Copy :=Fintype.ofList
  [.occurrences,.catalogue,.square,.cube,.fourth,.owners,.factors,.dictionary,.nextKey,.prefix,.keySource]
  (by intro k;cases k <;> simp)
/-- Every handoff reads an actual acquired or selected physical word. -/
def copySource :Copy→Stack
  | .occurrences=>occurrenceStack .output
  | .catalogue=>alphabetStack (Alpha.aux .output)
  | .square=>alphabetStack (Alpha.aux .square)
  | .cube=>alphabetStack (Alpha.aux .cube)
  | .fourth=>alphabetStack (Alpha.aux .fourth)
  | .owners=>occurrenceStack .number
  | .factors=>occurrenceStack .factors
  | .dictionary=>selectorStack Select.dictionary
  | .nextKey=>selectorStack Select.nextKey
  | .prefix=>selectorStack Select.selected
  | .keySource=>selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))
/-- Only the literal source/cache roles required by the next real component are populated. -/
def copyTarget :Copy→Stack
  | .occurrences=>selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))
  | .catalogue=>selectorStack (Select.aux .catalogue)
  | .square=>selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .square))
  | .cube=>selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .cube))
  | .fourth=>selectorStack (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .fourth))
  | .owners=>selectorStack (Select.aux .owners)
  | .factors=>selectorStack (Select.aux .factors)
  | .dictionary=>keyStack (Keys.environmentStack (Env.aux .dictionary))
  | .nextKey=>keyStack (Keys.environmentStack (Env.aux .nextKey))
  | .prefix=>keyStack (Keys.environmentStack (Env.aux .prefix))
  | .keySource=>keyStack (Keys.aux .source)
/-- All actual preserving copies have separate source, destination and restoration scratch. -/
def copyStack (site:Copy) (k:Fin 3) :Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else copyScratch
/-- Whole acquisition/copy/selection/key/halt control is fixed finite before all input families. -/
inductive Control where | start | alphabet | copy (site:Copy) | select | keys | done
  deriving DecidableEq,Fintype
/-- All four actual component and primitive return labels are fixed finite. -/
inductive Label where
  | local (pc:Control) | occurrence (pc:Occ.Label) | alphabet (pc:Alpha.Label)
  | selector (pc:Select.Label) | keys (pc:Keys.Label) | copy (site:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl" => Label.local
/-- The literal next code address at each actual paid copy site. -/
def copyNext :Copy→Label
  | .occurrences=>ctl (.copy .catalogue)
  | .catalogue=>ctl (.copy .square)
  | .square=>ctl (.copy .cube)
  | .cube=>ctl (.copy .fourth)
  | .fourth=>ctl (.copy .owners)
  | .owners=>ctl (.copy .factors)
  | .factors=>ctl .select
  | .dictionary=>ctl (.copy .nextKey)
  | .nextKey=>ctl (.copy .prefix)
  | .prefix=>ctl (.copy .keySource)
  | .keySource=>ctl .keys
/-- One actual three-input source performs every occurrence/alphabet/selector/selected-key stage. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.occurrence (.local .start)) (ctl .alphabet)
  | .local .alphabet=>.call (.alphabet .start) (ctl (.copy .occurrences))
  | .local (.copy site)=>.call (.copy site 0) (copyNext site)
  | .local .select=>.call (.selector (.local .start)) (ctl (.copy .dictionary))
  | .local .keys=>.call (.keys .start) (ctl .done)
  | .local .done=>.base .halt
  | .occurrence pc=>SemiprimeD1StackValidationLink.instruction occurrenceStack Label.occurrence (Occ.program pc)
  | .alphabet pc=>SemiprimeD1StackValidationLink.instruction alphabetStack Label.alphabet (Alpha.program pc)
  | .selector pc=>SemiprimeD1StackValidationLink.instruction selectorStack Label.selector (Select.program pc)
  | .keys pc=>SemiprimeD1StackValidationLink.instruction keyStack Label.keys (Keys.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- Every actual component/cache/shadow word and the one scratch are included in the physical boundary. -/
def data (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool)
    (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) :Stack→List Bool :=
  Sum.elim occurrences (Sum.elim alphabet (Sum.elim selector (Sum.elim keys (fun _=>scratch))))
/-- Exactly three original physical words, with every derived154-role word initially empty. -/
def input (rows number dimension:List Bool) :Stack→List Bool :=
  data (Occ.initial rows number).data (Alpha.initial dimension).data (fun _=>[]) (fun _=>[]) []
/-- Prepared row/count/dimension front door; no graph, F, alphabet, selection, dictionary or answer is supplied. -/
def initial (rows number dimension:List Bool) :C.State Stack Label :=
  ⟨some (ctl .start),none,none,input rows number dimension,[]⟩
/-- Genuine fixed finite154-role three-input acquisition machine. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine
  (occurrenceStack .rows) (keyStack (Keys.aux .output)) (ctl .start) program
/-- No actual preserving-copy operand aliases either its destination or scratch. -/
theorem copy_injective (site:Copy) :Function.Injective (copyStack site) :=by cases site <;> decide
/-- All154 physical data roles, including every empty component helper/shadow, are counted. -/
theorem stack_card :Fintype.card Stack=154 :=by
  rw [Fintype.card_sum,Occ.stack_card,Fintype.card_sum,Alpha.stack_card,Fintype.card_sum,Select.stack_card,
    Fintype.card_sum,Keys.stack_card]
  decide
/-- No natural counter, callback, row getter, selected cache or score enters runtime control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data and return alphabet is fixed finite before the whole infinite input family. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquire
