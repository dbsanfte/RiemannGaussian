/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowMeaning
import RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
/-! # Semantic bytes and actual occurrence counts along every executed grid fold
The invariant counts physical rows already visited. It supplies no runtime
count, coefficient, height, fit answer or operation evaluator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPayloadBounds
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload one)
end Model
namespace Row
export SemiprimeD1StackRecoveryGridRowMeaning (step work multiplicity numeratorPower denominatorPower slope reciprocal)
end Row
/-- Actual complete boundary payload widths and occurrence count after v physical row visits. -/
structure Bounded (width:List Bool) (p:Model.Payload) (v H:Nat) :Prop where
  /-- Numerator product magnitude is fitted or the literal one seed. -/
  num_mag:p.numerator.numerator.magnitude.length≤ width.length+1
  /-- Numerator product denominator retains the same bounded physical width. -/
  num_den:p.numerator.denominator.length≤ width.length+1
  /-- Denominator product magnitude is fitted or the literal one seed. -/
  den_mag:p.denominator.numerator.magnitude.length≤ width.length+1
  /-- Denominator product denominator retains the same bounded physical width. -/
  den_den:p.denominator.denominator.length≤ width.length+1
  /-- Every row emits at most actual h*u slope occurrences. -/
  count:p.slopes.length≤ v*H
  /-- Every actually emitted slope has BOTH exactly fitted W fields. -/
  slopes:∀x∈p.slopes,x.numerator.magnitude.length=width.length ∧x.denominator.length=width.length
/-- Literal oneWord is paid even at W0, before any actual row is executed. -/
theorem one_bounded (width:List Bool) (H:Nat) :Bounded width Model.one 0 H:=by
  constructor
  · change 1≤ width.length+1;omega
  · change 1≤ width.length+1;omega
  · change 1≤ width.length+1;omega
  · change 1≤ width.length+1;omega
  · exact Nat.zero_le _
  · intro x hx;cases hx
/-- A skipped physical row preserves every payload byte and can only enlarge the visit-count cap. -/
theorem weaken (width:List Bool) (p:Model.Payload) (v H:Nat) (h:Bounded width p v H) :Bounded width p (v+1) H:=by
  exact ⟨h.num_mag,h.num_den,h.den_mag,h.den_den,h.count.trans (Nat.mul_le_mul_right H (by omega)),h.slopes⟩
/-- Whole actual work update has fitted products and emits at most its physically acquired h*u markers. -/
theorem work_bounded (a M u v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) :
    Bounded width (Row.work a M u t q width p) (v+1) (SemiprimeD1TaperedLoss.height M u*u):=by
  have hn:=SemiprimeD1StackRecoveryGridByteBounds.operation_lengths .mul (Row.numeratorPower a M u q width) p.numerator width
  have hd:=SemiprimeD1StackRecoveryGridByteBounds.operation_lengths .mul (Row.denominatorPower a M u t q width) p.denominator width
  have hs:=SemiprimeD1StackRecoveryGridByteBounds.operation_lengths .mul
    (SemiprimeD1StackRecoveryGridModel.alpha a width) (Row.reciprocal a t q width) width
  have hm:Row.multiplicity a M u q≤ SemiprimeD1TaperedLoss.height M u*u:=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  constructor
  · exact hn.1.le.trans (by omega)
  · exact hn.2.le.trans (by omega)
  · exact hd.1.le.trans (by omega)
  · exact hd.2.le.trans (by omega)
  · change (List.replicate (Row.multiplicity a M u q) (Row.slope a t q width)++p.slopes).length≤_
    rw [List.length_append,List.length_replicate,Nat.add_mul,Nat.one_mul]
    have hcount:=hp.count
    omega
  · intro x hx
    change x∈List.replicate (Row.multiplicity a M u q) (Row.slope a t q width)++p.slopes at hx
    rcases List.mem_append.mp hx with hx|hx
    · obtain ⟨_,he⟩:=List.mem_replicate.mp hx
      subst x
      exact hs
    · exact hp.slopes x hx
/-- Every actual center/node skip or work branch preserves the same physical-width/count invariant. -/
theorem step_bounded (a M u v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) :
    Bounded width (Row.step a M u t q width p) (v+1) (SemiprimeD1TaperedLoss.height M u*u):=by
  unfold Row.step
  split
  · exact weaken width p v _ hp
  · split
    · exact weaken width p v _ hp
    · exact work_bounded a M u v t q width p hp
end RiemannGaussian.SemiprimeD1StackRecoveryGridPayloadBounds
