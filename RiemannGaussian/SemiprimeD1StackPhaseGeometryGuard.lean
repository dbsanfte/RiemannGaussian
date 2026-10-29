/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryOriginal
import RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
import RiemannGaussian.SemiprimeD1StackValidationLink
/-! # Literal original phase guard from acquired binary geometry and order
The whole source executes the frozen geometry source, then physically tests its
zero flag and compares its actual order with the retained original a and u.
No point, sign, order, guard verdict or clock is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuard
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace G
export SemiprimeD1StackPhaseGeometry (Stack Label program input aux subStack)
end G
namespace Less
export SemiprimeD1StackUnarySumLess (Stack contents)
export SemiprimeD1StackUnarySumLessBytecode (Label code entry)
end Less
/-- Caller u, all four consuming comparator fields, copy scratch and actual verdict. -/
inductive Aux where | levels | left | right | limit | valid | scratch | output
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.levels,.left,.right,.limit,.valid,.scratch,.output]
  (by intro k;cases k <;> simp)
/-- Entire acquired14-role geometry bank plus seven concrete guard roles. -/
abbrev Stack :=G.Stack⊕Aux
/-- All fourteen original/acquired geometry fields are included injectively. -/
def geometryStack : G.Stack→Stack :=Sum.inl
/-- Literal guard role inclusion. -/
def aux : Aux→Stack :=Sum.inr
/-- Fixed finite physical guard phases and real included-call labels. -/
inductive Label where
  | start | zero | left (second : Bool) | limit (second : Bool) | compare (second : Bool)
  | branch (second : Bool) | emit (value : Bool) | done
  | geometry (pc : G.Label) | copy (kind : Fin 3) (pc : Fin 9) | less (pc : Less.Label)
  deriving Fintype
/-- Copy the ACQUIRED order, original exponent or original u, never a supplied order. -/
def copySource (kind : Fin 3) : Stack :=
  if kind=0 then geometryStack (G.aux .order) else if kind=1 then geometryStack (G.aux .exponent)
  else aux .levels
/-- Both strict comparisons consume physically copied operands. -/
def copyTarget (kind : Fin 3) : Stack :=if kind=0 then aux .left else aux .limit
/-- Separate actual scratch restores every copied metadata operand. -/
def copyStack (kind : Fin 3) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .scratch
/-- Actual four-field comparison bank; its spare summand is physically empty. -/
def lessStack : Less.Stack→Stack
  | .left=>aux .left | .right=>aux .right | .limit=>aux .limit | .valid=>aux .valid
/-- ONE fixed literal source, independent of all a/u/t operands. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.geometry .start) .zero
  | .zero=>.base (.peek (geometryStack (G.aux .zero)) (.emit false) (.left false) (.emit false))
  | .left second=>.call (.copy 0 0) (.limit second)
  | .limit second=>.call (.copy (if second then 2 else 1) 0) (.compare second)
  | .compare second=>.call (.less Less.entry) (.branch second)
  | .branch second=>.base (.pop (aux .valid) (.emit false) (.emit false)
      (if second then .emit true else .left true))
  | .emit value=>.base (.push (aux .output) value .done)
  | .done=>.base .halt
  | .geometry pc=>SemiprimeD1StackValidationLink.instruction geometryStack Label.geometry (G.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .less pc=>SemiprimeD1StackMultiplierLink.instruction lessStack Label.less (Less.code pc)
/-- Only explicitly named physical Boolean words occur in the runtime bank. -/
def store (geometry : G.Stack→List Bool) (guard : Aux→List Bool) : Stack→List Bool :=Sum.elim geometry guard
/-- Literal guard words; comparator right and copy scratch are always clear at boundaries. -/
def words (u left limit valid output : List Bool) : Aux→List Bool
  | .levels=>u | .left=>left | .limit=>limit | .valid=>valid | .output=>output | _=>[]
/-- Runtime exponent/u metadata is physically unary; t remains physical binary. -/
def input (a u : Nat) (t : List Bool) : Stack→List Bool :=
  store (G.input (List.replicate a true) t) (words (List.replicate u true) [] [] [] [])
/-- Whole front door has ONLY original a/u/t, never geometry or an advised verdict. -/
def initial (a u : Nat) (t : List Bool) : C.State Stack Label :=⟨some .start,none,none,input a u t,[]⟩
/-- Genuine finite Boolean-stack guard machine with its physical multi-input state explicit. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (geometryStack (G.aux .exponent)) (aux .output) .start program
/-- Full allocated physical inventory, including the unused comparator summand. -/
theorem stack_card : Fintype.card Stack=21 :=by rw [Fintype.card_sum,SemiprimeD1StackPhaseGeometry.stack_card];decide
/-- All geometry roles remain distinct in the real included whole call. -/
theorem geometry_injective : Function.Injective geometryStack :=Sum.inl_injective
/-- Real metadata copy restoration uses disjoint source/destination/scratch fields. -/
theorem copy_injective (kind : Fin 3) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- Every consuming comparison field is physically distinct. -/
theorem less_injective : Function.Injective lessStack :=by decide
/-- Internal state is fixed finite before all original operands. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Data and actual return alphabets are fixed finite before input. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuard
