/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionOriginal
import RiemannGaussian.SemiprimeD1StackJetContextBounds
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1FreshJetBits
/-! # Actual original-phase child context/header acquisition
The only inputs are original phase a/u/M, BINARY t/p, and the caller's actual
UNARY-axis header. The source REAL-calls P48, peeks its actual guard/q, acquires
the old context/rank, physically frames q onto a copied old header and REAL-calls
the new context supplier. Numeric precision/rank materialization is fully paid.
This is the header/cache stage; fresh coefficient-vector allocation is separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContext
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack Label program input metadataStack aux)
end P
namespace J
export SemiprimeD1StackJetContext (Stack Label program axesCache precisionBits rankCache widthCache initial bank)
end J
/-- Actual success flag and real preserving-copy/frame restoration scratch. -/
inductive Aux where | valid | scratch deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.valid,.scratch] (by intro k;cases k <;> simp)
/-- All48 P/cache roles, disjoint old/new15-role contexts and two actual helper roles. -/
abbrev Stack :=P.Stack⊕(J.Stack⊕(J.Stack⊕Aux))
/-- Retain every actual phase geometry/metadata/BINARY precision role. -/
def phaseStack : P.Stack→Stack :=Sum.inl
/-- Old context has its OWN physically acquired rank and precision-width cache. -/
def oldStack (k : J.Stack) : Stack :=.inr (.inl k)
/-- New context has its OWN physically acquired q*oldrank and newprecision width. -/
def childStack (k : J.Stack) : Stack :=.inr (.inr (.inl k))
/-- Literal valid/scratch role inclusion. -/
def aux (k : Aux) : Stack :=.inr (.inr (.inr k))
/-- Actual cached guard field from the whole original phase source. -/
def guard : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.guardStack
  (SemiprimeD1StackPhaseGeometryGuard.aux .output)))
/-- Actual acquired unary coefficient-block dimension; no dimension operand is supplied. -/
def blocks : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .q))
/-- Exact original BINARY precision input retained by P48. -/
def originalPrecision : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .precision))
/-- Exact actual new BINARY precision output from P48. -/
def newPrecision : Stack :=phaseStack (P.aux .output)
/-- Fixed finite control, independent of all axes, ranks and numeric precisions. -/
inductive Label where
  | start | guard | positive | copyOldPrecision | oldContext | copyHeader | frame | cons
  | copyPrecision | childContext | accept | reject | done
  | phase (pc : P.Label) | context (child : Bool) (pc : J.Label)
  | copy (kind : Fin 3) (pc : Fin 9) | framing (pc : Fin 11)
  deriving Fintype
/-- All original-source bytes are copied by literal preserving-copy instructions. -/
def copySource (kind : Fin 3) : Stack :=
  if kind=0 then originalPrecision else if kind=1 then oldStack J.axesCache else newPrecision
/-- Only actual clear context input tapes are written by the three copy sites. -/
def copyTarget (kind : Fin 3) : Stack :=
  if kind=0 then oldStack J.precisionBits else if kind=1 then childStack J.axesCache else childStack J.precisionBits
/-- Actual shared restoration scratch remains disjoint from every operand. -/
def copyStack (kind : Fin 3) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .scratch
/-- Real Frame preserves the ACTUAL unary q and prepends it to the actual copied old header. -/
def frameStack (k : Fin 3) : Stack :=if k=0 then blocks else if k=1 then childStack J.axesCache else aux .scratch
/-- Literal original-source→guard/q→oldcontext→header→newcontext pipeline. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.phase .start) .guard
  | .guard=>.base (.peek guard .reject .reject .positive)
  | .positive=>.base (.peek blocks .reject .copyOldPrecision .copyOldPrecision)
  | .copyOldPrecision=>.call (.copy 0 0) .oldContext
  | .oldContext=>.call (.context false .start) .copyHeader
  | .copyHeader=>.call (.copy 1 0) .frame
  | .frame=>.call (.framing 0) .cons
  | .cons=>.base (.push (childStack J.axesCache) true .copyPrecision)
  | .copyPrecision=>.call (.copy 2 0) .childContext
  | .childContext=>.call (.context true .start) .accept
  | .accept=>.base (.push (aux .valid) true .done)
  | .reject=>.base (.push (aux .valid) false .done)
  | .done=>.base .halt
  | .phase pc=>SemiprimeD1StackValidationLink.instruction phaseStack Label.phase (P.program pc)
  | .context child pc=>SemiprimeD1StackValidationLink.instruction (if child then childStack else oldStack)
      (Label.context child) (J.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .framing pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.framing (SemiprimeD1StackFrame.code pc)
/-- Literal old/new acquired cache and helper words. These are physical bank views only. -/
def store (phase : P.Stack→List Bool) (old child : J.Stack→List Bool) (valid scratch : List Bool) : Stack→List Bool :=
  Sum.elim phase (Sum.elim old (Sum.elim child (fun k=>match k with | .valid=>valid | .scratch=>scratch)))
/-- Only the caller's actual old UNARY-axis header is initially installed in its retained tape. -/
def oldInput (axes : List Bool) : J.Stack→List Bool :=(J.initial axes []).data
/-- Every child context input/cache/work field is physically empty before acquisition. -/
def emptyContext : J.Stack→List Bool :=(J.initial [] []).data
/-- NO q/P/rank/context/verdict/clock payload is supplied at the whole front door. -/
def input (a u edges : Nat) (t p axes : List Bool) : Stack→List Bool :=
  store (P.input a u edges t p) (oldInput axes) emptyContext [] []
/-- Whole source starts before any phase or old/new context acquisition. -/
def initial (a u edges : Nat) (t p axes : List Bool) : C.State Stack Label :=⟨some .start,none,none,input a u edges t p axes,[]⟩
/-- Ready entry reuses EXACTLY the ACTUALLY acquired P48 cache, never a given q/P/rank. -/
def ready (a u edges : Nat) (t p axes : List Bool) : C.State Stack Label :=
  ⟨some .guard,none,none,store (SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t p)
    (oldInput axes) emptyContext [] [],[]⟩
/-- One fixed finite context/header machine. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (oldStack J.axesCache) (childStack J.rankCache) .start program
/-- Full allocated inventory includes both VALUE-materializing context banks. -/
theorem stack_card : Fintype.card Stack=80 :=by
  rw [Fintype.card_sum,SemiprimeD1StackPhaseWorkingPrecision.stack_card,Fintype.card_sum]
  have hJ:Fintype.card J.Stack=15:=by decide
  rw [hJ,Fintype.card_sum,hJ]
  decide
/-- Every old phase field remains physically distinct. -/
theorem phase_injective : Function.Injective phaseStack :=Sum.inl_injective
/-- Both actual context source inclusions are injective and disjoint. -/
theorem context_injective (child : Bool) : Function.Injective (if child then childStack else oldStack) :=by
  cases child
  · exact fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
  · exact fun _ _ h=>Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
/-- Every actual original/header/precision copy has distinct source/destination/scratch. -/
theorem copy_injective (kind : Fin 3) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- Actual unary-q framing restores its source and has separate output/scratch. -/
theorem frame_injective : Function.Injective frameStack :=by decide
/-- Control has no axes/rank/precision/count objects; it is fixed finite before all inputs. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All data and actual return alphabets are fixed finite. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackPhaseChildContext
