/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCalls
/-! # Paid physical shift and marked low-bit update -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputShift
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputPrimitives SemiprimeD1StackProcedureTrace
/-- Each actual offset cell pays a pop and a binary false prepend; EOF pays a pop. -/
theorem shift_run (p : P.Stack → List Bool) (w : Work) (count xs : List Bool) :
    Runs program (2*count.length+1) (ctl .shift)
      (data p {w with offset := count, shifted := xs}) (ctl .low)
      (data p {w with offset := [], shifted := List.replicate count.length false++xs}) := by
  induction count generalizing xs with
  | nil =>
    have h := pop_run .shift (ctl .low) (ctl .shiftZero) (ctl .shiftZero)
      (product .product) (data p {w with offset := [], shifted := xs}) [] rfl rfl
    simpa only [SemiprimeD1StackBytecode.choose,List.head?_nil,List.tail_nil,update_offset,List.length_nil,Nat.mul_zero,Nat.zero_add,List.replicate_zero,List.nil_append] using h
  | cons b count ih =>
    have h := pop_run .shift (ctl .low) (ctl .shiftZero) (ctl .shiftZero)
      (product .product) (data p {w with offset := b::count, shifted := xs}) (b::count) rfl rfl
    have h0 : Runs program 1 (ctl .shift) (data p {w with offset := b::count, shifted := xs})
        (ctl .shiftZero) (data p {w with offset := count, shifted := xs}) := by
      cases b <;> simpa only [SemiprimeD1StackBytecode.choose,List.head?_cons,List.tail_cons,update_offset] using h
    have h1 := push_run .shiftZero (ctl .shift) (aux .shifted) false
      (data p {w with offset := count, shifted := xs}) rfl
    simp only [data_shifted,update_shifted] at h1
    have h2 := ih (false::xs)
    have hh := join (join h0 h1) h2
    simpa only [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append,
      show (1+1)+(2*count.length+1)=2*(count.length+1)+1 by omega] using hh
/-- Actual false-pop/true-push implements the mark only after a positive physical shift. -/
theorem low_run (p : P.Stack → List Bool) (w : Work) (n : Nat) (hn : 0<n) (xs : List Bool) :
    Runs program 2 (ctl .low)
      (data p {w with offset := [], shifted := List.replicate n false++xs})
      (ctl .widthA) (data p {w with offset := [], shifted := marked n xs}) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h0 := pop_run .low (ctl .bad) (ctl .setOne) (ctl .bad) (aux .shifted)
    (data p {w with offset := [], shifted := List.replicate (n+1) false++xs})
    (false::(List.replicate n false++xs)) rfl (by rw [List.replicate_succ,List.cons_append];rfl)
  simp only [SemiprimeD1StackBytecode.choose,List.head?_cons,List.tail_cons,update_shifted] at h0
  have h1 := push_run .setOne (ctl .widthA) (aux .shifted) true
    (data p {w with offset := [], shifted := List.replicate n false++xs}) rfl
  simp only [data_shifted,update_shifted] at h1
  simpa only [marked,Nat.succ_eq_add_one,Nat.add_sub_cancel] using join h0 h1
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputShift

