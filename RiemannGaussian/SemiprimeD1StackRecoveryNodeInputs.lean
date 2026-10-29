/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalResources
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginalResources
/-! # One literal140-role local-node input source
The whole actual affine source calls Grid104 ONCE. Its acquired denominator/q
and retained grid argument/W then feed the entire real inverse and powers
sources through direct physical aliases. No coefficient, q, inverse, power,
scalar, normalizer, clock or evaluator answer is an initial operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputs
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace A
export SemiprimeD1StackRecoveryAffine (Stack Label program input initial grid rational aux oldAux)
end A
namespace I
export SemiprimeD1StackNormalizedInverse (Stack Label Reg Aux program input initial rational reg aux ctl)
end I
namespace P
export SemiprimeD1StackRecoveryPowers (Stack Label Aux program input initial rational aux)
end P
namespace Q
export SemiprimeD1StackRecoveryGrid (reg)
end Q
/-- Eight inverse-cache fields and twelve inverse-private controller/output words. -/
abbrev InversePrivate := (I.Reg×Bool)⊕Fin 12
/-- Entire112 acquired source words plus exactly28 new actual words; no duplicate alias bank. -/
abbrev Stack := A.Stack⊕(InversePrivate⊕Fin 8)
/-- Literal inclusion of the entire affine/Grid bank, retaining every old shadow. -/
def affine : A.Stack→Stack := Sum.inl
/-- Exact inverse private cache address. -/
def inverseReg (k : I.Reg×Bool) : Stack := .inr (.inl (.inl k))
/-- Literal fixed inverse-private controller word. -/
def inverseWork (k : Fin 12) : Stack := .inr (.inl (.inr k))
/-- Literal fixed powers-private controller word. -/
def powersWork (k : Fin 8) : Stack := .inr (.inr k)
/-- ENTIRE inverse58 inclusion shares actual R36, acquired denominator and acquired q directly. -/
def inverse : I.Stack→Stack
  | .inl k=>affine (A.rational k)
  | .inr (.inl k)=>inverseReg k
  | .inr (.inr k)=>match k with
    | .denominator=>affine (A.aux .array)
    | .originalQ=>affine (A.aux .retainedQ)
    | .remaining=>inverseWork 0 | .built=>inverseWork 1
    | .aIndex=>inverseWork 2 | .bIndex=>inverseWork 3 | .terms=>inverseWork 4
    | .reader=>inverseWork 5 | .readTodo=>inverseWork 6 | .fieldFrameScratch=>inverseWork 7
    | .valid=>inverseWork 8 | .copyScratch=>inverseWork 9 | .prefixReverse=>inverseWork 10
    | .output=>inverseWork 11
/-- ENTIRE powers47 inclusion reads the actual retained Grid argument and acquired q, sharing only real R36. -/
def powers : P.Stack→Stack
  | .inl k=>affine (A.rational k)
  | .inr k=>match k with
    | .argumentSigned=>affine (A.grid (Q.reg .argument false))
    | .argumentDen=>affine (A.grid (Q.reg .argument true))
    | .q=>affine (A.aux .retainedQ)
    | .remaining=>powersWork 0 | .currentSigned=>powersWork 1 | .currentDen=>powersWork 2
    | .row=>powersWork 3 | .frameScratch=>powersWork 4 | .copyScratch=>powersWork 5
    | .history=>powersWork 6 | .output=>powersWork 7
/-- Actual complete inverse array produced by its real call. -/
def inverseOutput : Stack := inverse (I.aux .output)
/-- Actual complete power array produced by its real call. -/
def powersOutput : Stack := powers (P.aux .output)
/-- The actual retained Ezero signed numerator, acquired by Grid104. -/
def scalarSigned : Stack := affine (A.grid (Q.reg .scalar false))
/-- The actual retained Ezero binary denominator, acquired by Grid104. -/
def scalarDen : Stack := affine (A.grid (Q.reg .scalar true))
/-- The actual acquired unary multiplicity, never an initial advice word. -/
def qWord : Stack := affine (A.aux .retainedQ)
/-- The physical shared width template retains its exact original bits. -/
def widthWord : Stack := affine (A.rational (SemiprimeD1StackRationalOperation.aux .template))
/-- Only finite literal call/return stages; readyGrid reuses an ACTUAL already acquired Grid bank. -/
inductive Control where | start | readyGrid | inverse | powers | done deriving DecidableEq,Repr
/-- All five literal stages precede every phase and width. -/
instance controlFintype : Fintype Control := Fintype.ofList [.start,.readyGrid,.inverse,.powers,.done] (by intro k;cases k <;> simp)
/-- Static included labels carry no input-dependent index, q, value or evaluator. -/
abbrev Label := Control⊕(A.Label⊕(I.Label⊕P.Label))
/-- Literal caller stage. -/
def ctl : Control→Label := Sum.inl
/-- Actual affine source label inclusion. -/
def affineLabel (pc : A.Label) : Label := .inr (.inl pc)
/-- Actual inverse source label inclusion. -/
def inverseLabel (pc : I.Label) : Label := .inr (.inr (.inl pc))
/-- Actual powers source label inclusion. -/
def powersLabel (pc : P.Label) : Label := .inr (.inr (.inr pc))
/-- ONE fixed literal program: actual Grid/affine once, then real inverse, then real powers, then halt. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (affineLabel (.local .start)) (ctl .inverse)
  | .inl .readyGrid=>.call (affineLabel (.local .ready)) (ctl .inverse)
  | .inl .inverse=>.call (inverseLabel (I.ctl .start)) (ctl .powers)
  | .inl .powers=>.call (powersLabel (.local .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction affine affineLabel (A.program pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackValidationLink.instruction inverse inverseLabel (I.program pc)
  | .inr (.inr (.inr pc))=>SemiprimeD1StackValidationLink.instruction powers powersLabel (P.program pc)
/-- Exact complete physical bank with every old112 and new28 role present. -/
def bank (old : A.Stack→List Bool) (inv : InversePrivate→List Bool) (pow : Fin 8→List Bool) : Stack→List Bool :=
  Sum.elim old (Sum.elim inv pow)
/-- Only the original five phase words are initially present; arrays/q/scalars/powers are actually acquired. -/
def input (a M u t width : List Bool) : Stack→List Bool := bank (A.input a M u t width) (fun _=>[]) (fun _=>[])
/-- Honest whole entry begins BEFORE Grid104 and all actual denominator/inverse/power acquisition. -/
def initial (a M u t width : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input a M u t width,[]⟩
/-- The one fixed finite prepared five-word source; no N-only scalar counter is claimed here. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (affine (A.oldAux .originalA)) inverseOutput (ctl .start) program
/-- Every allocated word and physical alias shadow is counted. -/
theorem stack_card : Fintype.card Stack=140 := by
  change Fintype.card (A.Stack⊕(InversePrivate⊕Fin 8))=140
  rw [Fintype.card_sum,SemiprimeD1StackRecoveryAffine.stack_card,Fintype.card_sum,Fintype.card_sum,Fintype.card_prod]
  have h : Fintype.card I.Reg=4 := by decide
  rw [h,Fintype.card_bool,Fintype.card_fin,Fintype.card_fin]
/-- All actual Boolean and saved-return tape alphabets are finite before every input. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- No numerical coefficient, index, q or clock inhabits runtime internal control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputs
