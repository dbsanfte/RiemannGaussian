/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSubtractorExecution
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Literal binary phase geometry and physical dyadic-order acquisition
Only the original unary exponent metadata and original binary grid index are
initially populated. Powers remain binary. The actual borrow chooses an exact
absolute subtraction, and a physical low-bit scan acquires the valuation.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometry
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace S
export SemiprimeD1StackAdder (Stack store)
export SemiprimeD1StackSubtractor (Label code state)
end S
/-- Ten physical original, acquired and copy/scan roles. -/
inductive Aux where | exponent | index | counter | center | alpha | sign | zero | order | scan | scratch
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.exponent,.index,.counter,.center,.alpha,.sign,.zero,.order,.scan,.scratch]
  (by intro k;cases k <;> simp)
/-- Four real ripple-subtraction fields and ten explicit metadata fields. -/
abbrev Stack :=S.Stack⊕Aux
/-- The actual subtractor bank; its output is also the retained magnitude word. -/
def subStack : S.Stack→Stack :=Sum.inl
/-- Literal metadata field inclusion. -/
def aux : Aux→Stack :=Sum.inr
/-- Finite source control, with no exponent, point or valuation in a label. -/
inductive Label where
  | start | seed | power | shift | alphaCopy | alphaShift
  | left (negative : Bool) | right (negative : Bool) | subtract (negative : Bool)
  | readFirst | saveSign (negative : Bool) | clearWrapped | readSecond
  | scanCopy | scan | increment | clearScan | clearOrder | saveZero (zero : Bool) | done
  | copy (kind : Fin 7) (pc : Fin 9) | ripple (pc : S.Label)
  deriving Fintype
/-- Seven static preserving-copy source sites, independent of every input. -/
def copySource (kind : Fin 7) : Stack :=
  if kind=0 then aux .exponent else if kind=1 then aux .center else if kind=2 then aux .index
  else if kind=3 then aux .center else if kind=4 then aux .center else if kind=5 then aux .index
  else subStack .output
/-- Every operand is acquired by a real paid physical copy. -/
def copyTarget (kind : Fin 7) : Stack :=
  if kind=0 then aux .counter else if kind=1 then aux .alpha else if kind=2 then subStack .left
  else if kind=3 then subStack .right else if kind=4 then subStack .left else if kind=5 then subStack .right
  else aux .scan
/-- Actual scratch is disjoint from source and destination at all seven sites. -/
def copyStack (kind : Fin 7) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .scratch
/-- One fixed finite literal source for all exponent and index words. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.copy 0 0) .seed
  | .seed=>.base (.push (aux .center) true .power)
  | .power=>.base (.pop (aux .counter) .alphaCopy .shift .shift)
  | .shift=>.base (.push (aux .center) false .power)
  | .alphaCopy=>.call (.copy 1 0) .alphaShift
  | .alphaShift=>.base (.push (aux .alpha) false (.left false))
  | .left negative=>.call (.copy (if negative then 4 else 2) 0) (.right negative)
  | .right negative=>.call (.copy (if negative then 5 else 3) 0) (.subtract negative)
  | .subtract negative=>.call (.ripple (.start false)) (if negative then .readSecond else .readFirst)
  | .readFirst=>.base (.pop (subStack .output) (.saveSign false) (.saveSign false) (.saveSign true))
  | .saveSign negative=>.base (.push (aux .sign) negative (if negative then .clearWrapped else .scanCopy))
  | .clearWrapped=>.base (.pop (subStack .output) (.left true) .clearWrapped .clearWrapped)
  | .readSecond=>.base (.pop (subStack .output) .scanCopy .scanCopy .scanCopy)
  | .scanCopy=>.call (.copy 6 0) .scan
  | .scan=>.base (.pop (aux .scan) .clearOrder .increment .clearScan)
  | .increment=>.base (.push (aux .order) true .scan)
  | .clearScan=>.base (.pop (aux .scan) (.saveZero false) .clearScan .clearScan)
  | .clearOrder=>.base (.pop (aux .order) (.saveZero true) .clearOrder .clearOrder)
  | .saveZero zero=>.base (.push (aux .zero) zero .done)
  | .done=>.base .halt
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .ripple pc=>SemiprimeD1StackMultiplierLink.instruction subStack Label.ripple (S.code pc)
/-- Exact physical bank view, with no native arithmetic object in the runtime. -/
def store (sub : S.Stack→List Bool) (metadata : Aux→List Bool) : Stack→List Bool :=Sum.elim sub metadata
/-- Explicit metadata role words. -/
def words (exponent index counter center alpha sign zero order scan scratch : List Bool) : Aux→List Bool
  | .exponent=>exponent | .index=>index | .counter=>counter | .center=>center | .alpha=>alpha
  | .sign=>sign | .zero=>zero | .order=>order | .scan=>scan | .scratch=>scratch
/-- Only caller exponent and index words exist at the source front door. -/
def input (exponent index : List Bool) : Stack→List Bool :=
  store (S.store [] [] [] []) (words exponent index [] [] [] [] [] [] [] [])
/-- Two original physical operands, with every work/output/flag/return field empty. -/
def initial (exponent index : List Bool) : C.State Stack Label :=⟨some .start,none,none,input exponent index,[]⟩
/-- Genuine finite machine; its paired physical-input initialization is explicit. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .exponent) (subStack .output) .start program
/-- Every one of the fourteen allocated roles is counted. -/
theorem stack_card : Fintype.card Stack=14 :=by rw [Fintype.card_sum];decide
/-- Actual subtraction uses four distinct physical fields. -/
theorem sub_injective : Function.Injective subStack :=Sum.inl_injective
/-- Every included copy restores its original physical operand. -/
theorem copy_injective (kind : Fin 7) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- Internal control is fixed finite before all exponent/index operands. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All fourteen payload alphabets and the real return alphabet are finite. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseGeometry
