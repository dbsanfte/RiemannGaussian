/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardOriginal
import RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
import RiemannGaussian.SemiprimeD1StackUnaryProduct
import RiemannGaussian.SemiprimeD1ModeRate
/-! # Actual guarded phase height/product/difference metadata acquisition
Only original physical a/u/M, binary t and binary precision p are supplied.
The actual guard acquires i. Accepted paths execute the real unary divider,
products and paired marker subtraction. Rejected paths execute none of them.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadata
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace G
export SemiprimeD1StackPhaseGeometryGuard (Stack Label program input aux geometryStack)
end G
namespace D
export SemiprimeD1StackUnaryDivmod (Stack contents unary)
export SemiprimeD1StackUnaryDivmodBytecode (Label code entry)
end D
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry contents)
end P
/-- Original M/p, actual product work, bounded outputs and real copy/subtraction work. -/
inductive Aux where | edges | precision | multiplier | multiplicand | productScratch | q | r | delta | subtractWork | copyScratch
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.edges,.precision,.multiplier,.multiplicand,.productScratch,.q,.r,.delta,.subtractWork,.copyScratch]
  (by intro k;cases k <;> simp)
/-- Complete21-role acquired guard, real divider6 and ten explicit metadata fields. -/
abbrev Stack :=G.Stack⊕(D.Stack⊕Aux)
/-- Literal inclusion preserves every original geometry/guard field. -/
def guardStack : G.Stack→Stack :=Sum.inl
/-- The quotient field retains the ACTUALLY acquired height h. -/
def divStack (k : D.Stack) : Stack :=.inr (.inl k)
/-- Literal original/output/work role inclusion. -/
def aux (k : Aux) : Stack :=.inr (.inr k)
/-- Two actual products share work fields and write distinct bounded metadata outputs. -/
def productStack (second : Bool) : P.Stack→Stack
  | .multiplier=>aux .multiplier | .multiplicand=>aux .multiplicand
  | .scratch=>aux .productScratch | .product=>if second then aux .r else aux .q
/-- All finite source sites, independent of original parameter values. -/
inductive Label where
  | start | branch | numerator (position : Fin 3) | addU | minusOne | copyDivisor | divide
  | clearRemainder | clearDivisor | qCopyU | subtractCopy (second : Bool)
  | subtract (second : Bool) | remove (second : Bool) | qCopyH
  | product (second : Bool) | clearMultiplicity (second : Bool)
  | rCopyM | rCopyA | plusOne | deltaCopyA | done
  | guard (pc : G.Label) | copy (kind : Fin 9) (pc : Fin 9)
  | division (pc : D.Label) | multiply (second : Bool) (pc : P.Label)
  deriving Fintype
/-- Nine fixed physical preserving-copy source roles. -/
def copySource (kind : Fin 9) : Stack :=
  if kind=0 then aux .edges else if kind=1 then guardStack (G.aux .levels)
  else if kind=2 then guardStack (G.aux .levels) else if kind=3 then guardStack (G.aux .levels)
  else if kind=4 then guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .order))
  else if kind=5 then divStack .quotient else if kind=6 then aux .edges
  else guardStack (G.geometryStack (SemiprimeD1StackPhaseGeometry.aux .exponent))
/-- Every numerator/operand/count is acquired by an actual paid copy. -/
def copyTarget (kind : Fin 9) : Stack :=
  if kind=0 then divStack .input else if kind=1 then divStack .input
  else if kind=2 then divStack .divisor else if kind=3 then aux .multiplicand
  else if kind=4 then aux .subtractWork else if kind=5 then aux .multiplier
  else if kind=6 then aux .multiplier else if kind=7 then aux .multiplicand else aux .delta
/-- Separate restoration scratch at every actual copy call. -/
def copyStack (kind : Fin 9) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .copyScratch
/-- Physical subtraction targets: u-copy for q, or a-copy for the binary shift count. -/
def subtractTarget (second : Bool) : Stack :=if second then aux .delta else aux .multiplicand
/-- One fixed finite literal source; no h/q/r/delta/point/order/clock parameter exists. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.guard .start) .branch
  | .branch=>.base (.peek (guardStack (G.aux .output)) .done .done (.numerator 0))
  | .numerator p=>.call (.copy 0 0) (if h:p.val<2 then .numerator ⟨p.val+1,by omega⟩ else .addU)
  | .addU=>.call (.copy 1 0) .minusOne
  | .minusOne=>.base (.pop (divStack .input) .done .copyDivisor .copyDivisor)
  | .copyDivisor=>.call (.copy 2 0) .divide
  | .divide=>.call (.division D.entry) .clearRemainder
  | .clearRemainder=>.base (.pop (divStack .remainder) .clearDivisor .clearRemainder .clearRemainder)
  | .clearDivisor=>.base (.pop (divStack .divisor) .qCopyU .clearDivisor .clearDivisor)
  | .qCopyU=>.call (.copy 3 0) (.subtractCopy false)
  | .subtractCopy second=>.call (.copy 4 0) (.subtract second)
  | .subtract second=>.base (.pop (aux .subtractWork) (if second then .done else .qCopyH) (.remove second) (.remove second))
  | .remove second=>.base (.pop (subtractTarget second) .done (.subtract second) (.subtract second))
  | .qCopyH=>.call (.copy 5 0) (.product false)
  | .product second=>.call (.multiply second P.entry) (.clearMultiplicity second)
  | .clearMultiplicity second=>.base (.pop (aux .multiplicand) (if second then .deltaCopyA else .rCopyM)
      (.clearMultiplicity second) (.clearMultiplicity second))
  | .rCopyM=>.call (.copy 6 0) .rCopyA
  | .rCopyA=>.call (.copy 7 0) .plusOne
  | .plusOne=>.base (.push (aux .multiplicand) true (.product true))
  | .deltaCopyA=>.call (.copy 8 0) (.subtractCopy true)
  | .done=>.base .halt
  | .guard pc=>SemiprimeD1StackValidationLink.instruction guardStack Label.guard (G.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind)
      (SemiprimeD1StackCopy.code pc)
  | .division pc=>SemiprimeD1StackMultiplierLink.instruction divStack Label.division (D.code pc)
  | .multiply second pc=>SemiprimeD1StackMultiplierLink.instruction (productStack second) (Label.multiply second) (P.code pc)
/-- Exact physical bank views; runtime payloads contain only Boolean words. -/
def store (guard : G.Stack→List Bool) (division : D.Stack→List Bool) (metadata : Aux→List Bool) : Stack→List Bool :=
  Sum.elim guard (Sum.elim division metadata)
/-- Explicit ten-role original/metadata bank. -/
def words (M p multiplier multiplicand scratch q r delta subtractWork copyScratch : List Bool) : Aux→List Bool
  | .edges=>M | .precision=>p | .multiplier=>multiplier | .multiplicand=>multiplicand | .productScratch=>scratch
  | .q=>q | .r=>r | .delta=>delta | .subtractWork=>subtractWork | .copyScratch=>copyScratch
/-- Original physical a/u/M and original BINARY t/p are the only inputs. -/
def input (a u M : Nat) (t p : List Bool) : Stack→List Bool :=
  store (G.input a u t) (fun _=>[]) (words (D.unary M) p [] [] [] [] [] [] [] [])
/-- Whole front door has no acquired guard, i, height/product/difference or advised clock. -/
def initial (a u M : Nat) (t p : List Bool) : C.State Stack Label :=⟨some .start,none,none,input a u M t p,[]⟩
/-- Genuine fixed finite metadata source. Its physical multi-input state is explicit. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .edges) (aux .q) .start program
/-- Every old/new/unused actual physical role is counted. -/
theorem stack_card : Fintype.card Stack=37 :=by
  rw [Fintype.card_sum,SemiprimeD1StackPhaseGeometryGuard.stack_card,Fintype.card_sum]
  decide
/-- Real whole guard has no internal role aliases. -/
theorem guard_injective : Function.Injective guardStack :=Sum.inl_injective
/-- Real divider input/work/height fields remain physically distinct. -/
theorem div_injective : Function.Injective divStack :=fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
/-- Both real product inclusions use separate multiplier/multiplicand/scratch/output words. -/
theorem product_injective (second : Bool) : Function.Injective (productStack second) :=by cases second <;> decide
/-- Every paid preserving-copy site has physically disjoint operands. -/
theorem copy_injective (kind : Fin 9) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- All actual control remains finite before all original metadata and binary words. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All physical payload and real-return alphabets are fixed finite. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadata
