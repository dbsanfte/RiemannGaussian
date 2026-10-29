/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1StackTransformSelectors
/-! # Actual finite selectors to the real metadata loader and entire record
Six original acquired words are retained. The generic loader's opaque source1/2
are directly wired to the two physically constructed Boolean selectors; source0,
3,4,5 retain binary N and original coord1/coord2/coord3 words. All aliases count.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace D
export SemiprimeD1StackDescriptorRecord (Stack Label program source original history output)
end D
namespace S
export SemiprimeD1StackTransformSelectors (Stack Label program data initial done)
end S
namespace T
export SemiprimeD1StackStaticTable (Static)
end T
/-- All metadata-loader and selector roles, including both unused selector shadows. -/
abbrev Stack (K : Type) :=D.Stack K⊕S.Stack
/-- Actual complete descriptor-to-record component. -/
def descriptorStack {K : Type} (k : D.Stack K) : Stack K :=.inl k
/-- Two directly acquired selector outputs feed the actual loader source fields. -/
def selectorStack {K : Type} : S.Stack→Stack K
  | .stage=>descriptorStack (D.source 1)
  | .inverse=>descriptorStack (D.source 2)
  | k=>.inr k
/-- Every original acquired field has one retained physical location. -/
def rawSource {K : Type} (i : Fin 6) : Stack K :=
  if i=1 then selectorStack .tag else if i=2 then selectorStack .transform else descriptorStack (D.source i)
/-- Actual caller reverse row history. -/
def history {K : Type} : Stack K :=descriptorStack D.history
/-- Actual caller final output suffix. -/
def output {K : Type} : Stack K :=descriptorStack D.output
/-- Five literal caller stages, including a real empty-selector rejection gate. -/
inductive Control where | start | guard | record | done | abort
  deriving DecidableEq
instance : Fintype Control :=Fintype.ofList [.start,.guard,.record,.done,.abort] (by intro k;cases k <;> simp)
/-- Every actual nested return label is fixed before original N. -/
abbrev Label (L : Type) (size : Nat) :=Control⊕(S.Label⊕D.Label L size)
/-- Included finite selector source label. -/
def selectorLabel {L : Type} {n : Nat} (pc : S.Label) : Label L n :=.inr (.inl pc)
/-- Included actual metadata/template/table/serializer/logger label. -/
def descriptorLabel {L : Type} {n : Nat} (pc : D.Label L n) : Label L n :=.inr (.inr pc)
variable {K L : Type} [DecidableEq K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Actual selector call and success peek BEFORE the actual metadata-record call.
Unknown codes return empty selectors and take the real abort branch. -/
def program : Label L s.roles.length→C.Instruction (Stack K) (Label L s.roles.length)
  | .inl .start=>.call (selectorLabel .start) (.inl .guard)
  | .inl .guard=>.base (.peek (selectorStack .stage) (.inl .abort) (.inl .record) (.inl .record))
  | .inl .record=>.call (descriptorLabel (.inl .start)) (.inl .done)
  | .inl .done|.inl .abort=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction selectorStack selectorLabel (S.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction descriptorStack descriptorLabel (D.program s sourceMap pc)
/-- Proof-only loader-source view: two actual selector cells replace opaque slots1/2. -/
def fields (raw : Fin 6→List Bool) (stage inverse : List Bool) : Fin 6→List Bool :=
  fun i=>if i=1 then stage else if i=2 then inverse else raw i
/-- Complete physical store. Both unused selector-output shadows remain empty. -/
def data (component : D.Stack K→List Bool) (tag tr : List Bool) : Stack K→List Bool :=
  Sum.elim component (S.data tag tr [] [] [] [])
/-- Original six acquired words, scope and caller accumulators; dirty template
and dirty old selectors are charged and physically erased by the actual code. -/
def initial (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (oldStage oldInverse bank hist out : List Bool) :
    C.State (Stack K) (Label L s.roles.length) :=
  ⟨some (.inl .start),none,none,data
    (SemiprimeD1StackDescriptorRecord.initial s oldTemplate (fields raw oldStage oldInverse) bank hist out).data
    (raw 1) (raw 2),[]⟩
/-- Actual store after both raw fields were physically decoded and selector pushes executed. -/
def afterSelectors (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (bank hist out : List Bool) : Stack K→List Bool :=
  data (SemiprimeD1StackDescriptorRecord.initial s oldTemplate (fields raw [second] [inverse]) bank hist out).data
    (raw 1) (raw 2)
/-- Complete actual original row result; every original acquired field survives. -/
def done (raw : Fin 6→List Bool) (second inverse : Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (hist out : List Bool) : C.State (Stack K) (Label L s.roles.length) :=
  ⟨none,none,none,data
    (SemiprimeD1StackDescriptorRecord.done s sourceMap (fields raw [second] [inverse]) words answer hist out).data
    (raw 1) (raw 2),[]⟩
/-- Genuine fixed finite machine, parameterized only by one static checker/map. -/
def machine [Fintype K] [Fintype L] : Turing.FinTM2 :=SemiprimeD1StackCalls.machine
  (rawSource 0) output (.inl .start) (program s sourceMap)
omit [DecidableEq K] in
/-- Complete physical cardinality includes both selector aliases and all old shadows. -/
theorem stack_card [Fintype K] : Fintype.card (Stack K)=2*Fintype.card K+42 :=by
  rw [Fintype.card_sum,SemiprimeD1StackDescriptorRecord.stack_card,SemiprimeD1StackTransformSelectors.stack_card]
omit [DecidableEq K] in
/-- The seven-role selector component has injective wiring despite the two shared outputs. -/
theorem selectorStack_injective : Function.Injective (@selectorStack K) :=by
  intro a b h;cases a <;> cases b <;> simp_all [selectorStack,descriptorStack,D.source]
end RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecord
