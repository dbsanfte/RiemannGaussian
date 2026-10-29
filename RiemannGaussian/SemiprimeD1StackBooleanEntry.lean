/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureFragments
/-! # Fixed physical OR, input-check and two-port equality procedures
Only raw ordered assignment bits are supplied. The assignment is physically
copied and preserved. Read bits live in finite labels, not a callback or native
word evaluator; every result bit is pushed by a literal instruction.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackBooleanEntry
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run choose)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
/-- Four fixed Boolean roles. -/
inductive Stack where
  | assignment | reader | scratch | output
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.assignment,.reader,.scratch,.output]
  (by intro k; cases k <;> simp)
/-- Three finite entry points of the ONE fixed program. -/
inductive Mode where
  | orGate | inputCheck | equality
  deriving DecidableEq
instance : Fintype Mode := Fintype.ofList [.orGate,.inputCheck,.equality]
  (by intro k; cases k <;> simp)
/-- All bit-dependent control is finite. -/
inductive Control where
  | start (mode : Mode) | first (mode : Mode)
  | orSecond (a : Bool) | orThird (a b : Bool) | equalSecond (a : Bool)
  | clear (accepted : Bool) | emit (accepted : Bool) | done
  deriving DecidableEq,Fintype
/-- Actual included preserving Copy labels. -/
abbrev Label := Control ⊕ Fin 9
/-- Three genuinely distinct Copy roles. -/
def copyStack (i : Fin 3) : Stack := if i=0 then .assignment else if i=1 then .reader else .scratch
/-- Literal Copy inclusion. -/
def copyLabel (pc : Fin 9) : Label := .inr pc
/-- Control reached by the first physically read bit. -/
def afterFirst : Mode→Bool→Label
  | .orGate,a => .inl (.orSecond a)
  | .inputCheck,a => .inl (.clear a)
  | .equality,a => .inl (.equalSecond a)
/-- Fixed real Copy plus literal Boolean reads, branches, clearing and output. -/
def program : Label→C.Instruction Stack Label
  | .inr pc => SemiprimeD1StackMultiplierLink.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
  | .inl (.start mode) => .call (copyLabel 0) (.inl (.first mode))
  | .inl (.first mode) => .base (.pop .reader (.inl (.clear false)) (afterFirst mode false) (afterFirst mode true))
  | .inl (.orSecond a) => .base (.pop .reader (.inl (.clear false)) (.inl (.orThird a false)) (.inl (.orThird a true)))
  | .inl (.orThird a b) => .base (.pop .reader (.inl (.clear false))
      (.inl (.clear (decide (false=(a || b))))) (.inl (.clear (decide (true=(a || b))))))
  | .inl (.equalSecond a) => .base (.pop .reader (.inl (.clear false))
      (.inl (.clear (decide (a=false)))) (.inl (.clear (decide (a=true)))))
  | .inl (.clear accepted) => .base (.pop .reader (.inl (.emit accepted))
      (.inl (.clear accepted)) (.inl (.clear accepted)))
  | .inl (.emit accepted) => .base (.push .output accepted (.inl .done))
  | .inl .done => .base .halt
/-- Exact four-stack data, used only to describe actual configurations. -/
def data (assignment reader scratch output : List Bool) : Stack→List Bool
  | .assignment => assignment
  | .reader => reader
  | .scratch => scratch
  | .output => output
/-- Raw ordered assignment input ONLY; all workspace starts empty. -/
def initial (mode : Mode) (bits : List Bool) : C.State Stack Label :=
  ⟨some (.inl (.start mode)),none,none,data bits [] [] [],[]⟩
/-- Raw original assignment retained, one actually computed Boolean returned. -/
def done (bits : List Bool) (accepted : Bool) : C.State Stack Label :=
  ⟨none,none,none,data bits [] [] [accepted],[]⟩
/-- Three fixed finite machines; no runtime truth/count/entry callback. -/
abbrev machine (mode : Mode) : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine .assignment .output (.inl (.start mode)) program
/-- No Copy operands alias. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

end RiemannGaussian.SemiprimeD1StackBooleanEntry
