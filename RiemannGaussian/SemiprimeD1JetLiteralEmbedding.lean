/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetLiteralLift
import RiemannGaussian.SemiprimeD1JetEmbedding

/-! # CURRENT table set-lift and actual all-coordinate fresh-axis copy
Retargeting precision keeps literal coefficient bytes unchanged. Its semantics
is a new reduction of the same integer lift, never an upward-precision ring map.
The actual existing embed then copies ALL old coefficients and appends zeros.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetLiteralEmbedding
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetLiteralLift
  SemiprimeD1JetScalarMap SemiprimeD1JetInterpretation SemiprimeD1DyadicInteger

/-- Metadata set-lift of CURRENT literal coefficient bytes; no arithmetic is replayed. -/
def retarget (entry : Tagged) (p : ℕ) : Tagged :=
  ⟨entry.creation,⟨entry.current.axes,p⟩,entry.coefficients⟩

/-- Set-lift preserves every actual original coefficient word. -/
theorem retarget_coefficients (entry : Tagged) (p : ℕ) :
    (retarget entry p).coefficients=entry.coefficients := rfl

/-- Immutable creation metadata is not treated as a tensor-evaluation recipe. -/
theorem retarget_creation (entry : Tagged) (p : ℕ) :
    (retarget entry p).creation=entry.creation := rfl

/-- Retargeted CURRENT words are the new precision's reduction of the SAME integer lift. -/
theorem retarget_interpret (entry : Tagged) (p : ℕ) :
    interpret (retarget entry p).current (retarget entry p).coefficients=
      scalarMap (dims entry.current.axes) (reduction p)
        (literal entry.current.axes entry.coefficients) :=
  (literal_reduce entry.current.axes p entry.coefficients).symm

/-- The ACTUAL existing physical copy/zero-extension routine preserves ALL old
coordinates after set-lifting the CURRENT canonical integer table to the new precision. -/
theorem retarget_embed_interpret (entry : Tagged) (p q : ℕ) (hq : 0<q)
    (hshape : entry.coefficients.length=entry.current.rank) :
    HEq (interpret (embed (retarget entry p) [q] p).value.current
      (embed (retarget entry p) [q] p).value.coefficients)
      (SemiprimeD1JetAlgebra.outerEmbedding q (dims entry.current.axes)
        (scalarMap (dims entry.current.axes) (reduction p)
          (literal entry.current.axes entry.coefficients))) := by
  cases entry with
  | mk creation current words =>
    cases current with
    | mk axes oldp =>
      have h := SemiprimeD1JetEmbedding.embed_interpret
        (retarget ⟨creation,⟨axes,oldp⟩,words⟩ p) q hq hshape
      simp only [retarget_interpret] at h
      simp only [retarget] at h ⊢
      convert h using 1 <;> rfl

end RiemannGaussian.SemiprimeD1JetLiteralEmbedding
