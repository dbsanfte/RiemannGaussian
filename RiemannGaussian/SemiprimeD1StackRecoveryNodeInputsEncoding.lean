/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsView
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCodec
/-! # Actual affine/Grid cache lineage and exact140-word inverse/power stop specification
All native expressions in this module are theorem-side word specifications.
The program remains parameterless and reads only its five original words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsEncoding
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsCodec
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (retained array result original)
end E
namespace V
export SemiprimeD1StackRecoveryNodeInputsView (empty afterInverse result)
end V
/-- Exact actual retained local argument; its sign/denominator are physical Grid outputs. -/
def argument (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : SemiprimeRationalBits.RationalWord :=
  (SemiprimeD1RecoveryGridBits.acquire width a M u selected).argument
/-- Exact actual Ezero retained by the same original Grid source. -/
def scalar (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : SemiprimeRationalBits.RationalWord :=
  (SemiprimeD1RecoveryGridBits.acquire width a M u selected).scalar
/-- Proof specification of the inverse array obtained from the ACTUAL acquired affine array/q/W. -/
def inverseWords (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : List SemiprimeRationalBits.RationalWord :=
  SemiprimeD1StackNormalizedInverseEncoding.outputWords (E.array a M u selected width) (E.retained a M u selected) width
/-- Exact physical chronological inverse array. -/
def inverseTape (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : List Bool :=
  SemiprimeD1StackNormalizedInverse.tape (inverseWords a M u selected width)
/-- Exact actual sequential powers from the acquired original argument, not supplied coefficients. -/
def powerWords (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : List SemiprimeRationalBits.RationalWord :=
  SemiprimeD1StackRecoveryPowersSpec.array width (argument a M u selected width) (E.retained a M u selected)
/-- Exact physical chronological powers array, with no value-only codec conversion. -/
def powerTape (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : List Bool :=
  SemiprimeD1StackRecoveryPowersSpec.vector (powerWords a M u selected width)
/-- Real complete affine source endpoint, with ALL28 new words still EMPTY. -/
def afterAffine (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : Stack→List Bool :=
  V.empty (E.result a M u selected t width)
/-- Actual complete inverse endpoint; all112 acquired words are retained. -/
def afterInverse (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : Stack→List Bool :=
  V.afterInverse (E.result a M u selected t width) (inverseTape a M u selected width)
/-- Every140 final role: ALL112 retained actual affine/Grid words plus exact acquired inverse and powers. -/
def result (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : Stack→List Bool :=
  V.result (E.result a M u selected t width) (inverseTape a M u selected width) (powerTape a M u selected width)
/-- Actual true halt with no transient flags or internal saved returns. -/
def done (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : C.State Stack Label :=
  ⟨none,none,none,result a M u selected t width,[]⟩
/-- SAME-program ready entry accepts the ACTUAL entire Grid cache, with no acquired q/affine/inverse/power advice. -/
def gridReady (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : C.State Stack Label :=
  ⟨some (ctl .readyGrid),none,none,V.empty (SemiprimeD1StackRecoveryAffineView.bank (E.original a M u selected t width)),[]⟩
/-- All35 old private R36 words really are empty at the actual affine boundary, with the exact W preserved. -/
theorem rational_image (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (k : SemiprimeD1StackRationalOperation.Stack) :
    E.result a M u selected t width (A.rational k)=
      (if k=SemiprimeD1StackRationalOperation.aux .template then width else []) := by
  change Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width k=_
  simp only [Function.update_apply]
/-- Direct aliasing supplies the ACTUAL whole affine array with the exact inverse input codec. -/
theorem denominator_image (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    E.result a M u selected t width (A.aux .array)=SemiprimeD1StackNormalizedInverse.tape (E.array a M u selected width) :=
  affine_tape _
/-- The actual real affine multiplicity output is a retained unary word. -/
theorem q_image (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    E.result a M u selected t width (A.aux .retainedQ)=List.replicate (E.retained a M u selected) true := rfl
/-- Argument sign/magnitude bytes are acquired by Grid, not reacquired or replaced by a power answer. -/
theorem argument_signed (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    E.result a M u selected t width (A.grid (Q.reg .argument false))=
      SemiprimeD1StackRecoveryPowersSpec.signed (argument a M u selected width) := rfl
/-- Argument denominator bytes are the exact ACTUAL retained Grid bytes. -/
theorem argument_den (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    E.result a M u selected t width (A.grid (Q.reg .argument true))=(argument a M u selected width).denominator := rfl
/-- The physical power tape is EXACTLY the shared two-field array ABI, including W0 and every high zero. -/
theorem power_tape (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) :
    powerTape a M u selected width=SemiprimeD1StackNormalizedInverse.tape (powerWords a M u selected width) := powers_tape _
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsEncoding
