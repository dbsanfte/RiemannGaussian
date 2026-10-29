/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteCalls
/-! # Physical parsing of internally acquired radix records -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteFields
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackJetRoute.control
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F

theorem field_injective (b : Bool) : Function.Injective (fieldStack b) := by
  intro x y h
  cases b <;> cases x with
  | inl x => cases x <;> cases y with
    | inl y => cases y <;> simp_all [fieldStack]
    | inr y => cases y; simp_all [fieldStack]
  | inr x => cases x; cases y with
    | inl y => cases y <;> simp_all [fieldStack]
    | inr y => cases y; rfl

/-- The internally acquired axis field is parsed by the actual finite field procedure. -/
theorem read_axis (word tail left right result : List Bool) :
    Trace.Runs code (8*word.length+7) (ctl .readQ)
      (bank [] (frame word tail) left right result [] [] [] [] [] [] [] []) (ctl .qDone) (bank [] tail left right result [] word [] [] [] [] [] [true]) := by
  have hr := SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  apply Trace.included_call code (fieldStack false) fieldQLabel (field_injective false) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (ctl .readQ) (ctl .qDone) rfl
    (8*word.length+6) _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k with
      | inl k=>cases k <;> rfl
      | inr k=>cases k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k with
      | inl k=>cases k <;> rfl
      | inr k=>cases k; rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim

/-- The internally acquired denominator field is parsed by the actual finite field procedure. -/
theorem read_denominator (word tail left right result q : List Bool) :
    Trace.Runs code (8*word.length+7) (ctl .readD)
      (bank [] (frame word tail) left right result [] q [] [] [] [] [] []) (ctl .dDone) (bank [] tail left right result [] q word [] [] [] [] [true]) := by
  have hr := SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  apply Trace.included_call code (fieldStack true) fieldDLabel (field_injective true) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (ctl .readD) (ctl .dDone) rfl
    (8*word.length+6) _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k with
      | inl k=>cases k <;> rfl
      | inr k=>cases k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k with
      | inl k=>cases k <;> rfl
      | inr k=>cases k; rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim

end RiemannGaussian.SemiprimeD1StackJetRouteFields
