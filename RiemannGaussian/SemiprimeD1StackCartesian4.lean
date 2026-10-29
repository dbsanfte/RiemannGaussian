/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureFragments
import RiemannGaussian.SemiprimeD1StackFrame

/-! # Fixed four-axis physical Cartesian record engine
All four limits, indices and the cached finite constructor tag are Boolean
payloads. Four statically nested real procedures consume copied counters;
the leaf frames all four actual indices and the actual cached tag. No body
callback, runtime native index/list or input-dependent program label occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end Link
/-- Four limit stacks, four current indices and four fixed auxiliary roles. -/
abbrev Stack := Fin 4⊕(Fin 4⊕Fin 4)
/-- Actual cached source limit. -/
def limitStack (level:Fin 4) : Stack := .inl level
/-- Actual mutable physical index. -/
def indexStack (level:Fin 4) : Stack := .inr (.inl level)
/-- Copy scratch, Frame scratch, record output and cached constructor tag. -/
def aux (role:Fin 4) : Stack := .inr (.inr role)
/-- Statically nested four-loop control and five physical field calls. -/
inductive Local where
  | main | ret | halt
  | entry (level:Fin 4) | drop (level:Fin 4) | child (level:Fin 4) | after (level:Fin 4)
  | fields (part:Fin 5)
  deriving DecidableEq,Repr
/-- Exhaustive finite local labels before every payload. -/
instance : Fintype Local where
  elems:={.main,.ret,.halt}∪Finset.univ.image Local.entry∪Finset.univ.image Local.drop∪
    Finset.univ.image Local.child∪Finset.univ.image Local.after∪Finset.univ.image Local.fields
  complete:=by intro pc;cases pc <;> simp
/-- Fixed local labels, four included Copy and five included Frame instances. -/
abbrev Label := Local⊕((Fin 4×Fin 9)⊕(Fin 5×Fin 11))
/-- Copy reads a real limit, writes its corresponding empty current index. -/
def copyStack (level:Fin 4) (k:Fin 3) : Stack :=
  if k=0 then limitStack level else if k=1 then indexStack level else aux 0
/-- Literal fixed Copy inclusion labels. -/
def copyLabel (level:Fin 4) (pc:Fin 9) : Label := .inr (.inl (level,pc))
/-- The first four emitted fields are indices3,2,1,0; the final field is the cached tag. -/
def fieldSource (part:Fin 5) : Stack :=
  if h:part.val<4 then indexStack ⟨3-part.val,by omega⟩ else aux 3
/-- Actual physical Frame roles. -/
def frameStack (part:Fin 5) (k:Fin 3) : Stack :=
  if k=0 then fieldSource part else if k=1 then aux 2 else aux 1
/-- Literal static Frame inclusion labels. -/
def frameLabel (part:Fin 5) (pc:Fin 11) : Label := .inr (.inr (part,pc))
/-- Statically selected lower nesting level; never an input-dependent native index. -/
def nextLevel (level:Fin 4) : Fin 4 := if h:level.val<3 then ⟨level.val+1,by omega⟩ else 0
/-- Actual fixed child entry. -/
def childEntry (level:Fin 4) : Label :=
  if level=3 then .inl (.fields 0) else .inl (.entry (nextLevel level))
/-- Static successor after one physical field call. -/
def nextField (part:Fin 5) : Label :=
  if h:part.val<4 then .inl (.fields ⟨part.val+1,by omega⟩) else .inl .ret
/-- ONE fixed literal instruction table, with real nested calls and returns. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl (level,pc)) => Link.instruction (copyStack level) (copyLabel level) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (part,pc)) => Link.instruction (frameStack part) (frameLabel part) (SemiprimeD1StackFrame.code pc)
  | .inl .main => .call (.inl (.entry 0)) (.inl .halt)
  | .inl .ret => .ret
  | .inl .halt => .base .halt
  | .inl (.entry level) => .call (copyLabel level 0) (.inl (.drop level))
  | .inl (.drop level) => .base (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level)))
  | .inl (.child level) => .call (childEntry level) (.inl (.after level))
  | .inl (.after level) => .base (.pop (indexStack level) (.inl .ret) (.inl (.child level)) (.inl (.child level)))
  | .inl (.fields part) => .call (frameLabel part 0) (nextField part)
/-- Fixed internal engine machine; original-input wrapper will acquire all limits and tag. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (limitStack 0) (aux 2) (.inl .main) program
/-- Real component maps have disjoint physical roles. -/
theorem copyStack_injective (level:Fin 4) : Function.Injective (copyStack level) := by fin_cases level <;> decide
/-- Frame source/output/scratch roles are disjoint for every actual field. -/
theorem frameStack_injective (part:Fin 5) : Function.Injective (frameStack part) := by fin_cases part <;> decide
/-- Twelve fixed Boolean stacks. -/
theorem stack_card : Fintype.card Stack=12 := by decide
/-- One hundred fifteen fixed control labels. -/
theorem label_card : Fintype.card Label=115 := by decide
/-- Every stack alphabet is finite; the real return alphabet is fixed too. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (limitStack 0) (aux 2) (.inl .main) program
end RiemannGaussian.SemiprimeD1StackCartesian4
