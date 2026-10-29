/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteFailure
/-! # Actual successful mixed-radix record traversal -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteStep
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls SemiprimeD1StackJetRouteFields
open SemiprimeD1StackJetRouteDigits SemiprimeD1StackJetRouteControl
open SemiprimeD1StackJetRouteFailure (compose)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackJetRoute.control

theorem flag_true (pc next : Label)
    (hcode : code pc=.base (.pop .valid (ctl (.fail 0)) (ctl (.fail 0)) next))
    (axes records left right result radix q d quotLeft remLeft quotRight remRight : List Bool) :
    Trace.Runs code 1 pc (bank axes records left right result radix q d quotLeft remLeft quotRight remRight [true])
      next (bank axes records left right result radix q d quotLeft remLeft quotRight remRight []) := by
  apply Trace.one_base code pc next (.pop .valid (ctl (.fail 0)) (ctl (.fail 0)) next) _ _ hcode
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp [SemiprimeD1StackBytecode.execute]

theorem peek_record (word tail left right result : List Bool) :
    Trace.Runs code 1 (ctl .recordPeek)
      (bank [] (frame word tail) left right result [] [] [] [] [] [] [] [])
      (ctl .readQ) (bank [] (frame word tail) left right result [] [] [] [] [] [] [] []) := by
  apply Trace.one_base code (ctl .recordPeek) (ctl .readQ)
    (.peek .records (ctl .baseLeft) (ctl .readQ) (ctl .readQ)) _ _ rfl
  · cases word <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,frame]
  · rfl

/-- A compatible original radix record is parsed, divided, physically compared,
cleared, and replaced by the actually executed remainder counters. -/
theorem compatible_step (q d i j : ℕ) (ha : i/d+j/d<q) (tail result : List Bool) :
    ∃m≤2000*(q+d+i+j+1),Trace.Runs code m (ctl .recordPeek)
      (bank [] (frame (unary q) (frame (unary d) tail)) (unary i) (unary j) result [] [] [] [] [] [] [] [])
      (ctl .recordPeek) (bank [] tail (unary (i%d)) (unary (j%d)) result [] [] [] [] [] [] [] []) := by
  have h1 := peek_record (unary q) (frame (unary d) tail) (unary i) (unary j) result
  have h2 := read_axis (unary q) (frame (unary d) tail) (unary i) (unary j) result
  have h3 := flag_true (ctl .qDone) (ctl .readD) rfl [] (frame (unary d) tail)
    (unary i) (unary j) result [] (unary q) [] [] [] [] []
  have h4 := read_denominator (unary d) tail (unary i) (unary j) result (unary q)
  have h5 := flag_true (ctl .dDone) (ctl .divideLeft) rfl [] tail
    (unary i) (unary j) result [] (unary q) (unary d) [] [] [] []
  obtain ⟨a,haClock,h6⟩ := divide_left i j d tail result (unary q)
  obtain ⟨b,hbClock,h7⟩ := divide_right j d tail result (unary q) (unary (i/d)) (unary (i%d))
  obtain ⟨c,hcClock,h8⟩ := compare_digits (i/d) (j/d) q tail result (unary d) (unary (i%d)) (unary (j%d))
  simp only [ha,decide_true] at h8
  have h9 := flag_true (ctl .compareDone) (ctl .clearD) rfl [] tail [] [] result [] []
    (unary d) [] (unary (i%d)) [] (unary (j%d))
  have h10 := clear_denominator tail result (unary d) (unary (i%d)) (unary (j%d))
  have h11 := move_left (i%d) tail result (unary (j%d))
  have h12 := move_right (j%d) tail result (unary (i%d))
  have h := compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6
    (compose h7 (compose h8 (compose h9 (compose h10 (compose h11 h12))))))))))
  refine ⟨_,?_,h⟩
  simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hi := Nat.div_le_self i d
  have hj := Nat.div_le_self j d
  have hri := Nat.mod_le i d
  have hrj := Nat.mod_le j d
  omega

/-- Every live byte of the fixed routing bank is included in this literal width. -/
theorem bank_width (axes records left right result radix q d qi ri qj rj valid : List Bool) :
    ∀k,(bank axes records left right result radix q d qi ri qj rj valid k).length≤
      axes.length+records.length+left.length+right.length+result.length+radix.length+
        q.length+d.length+qi.length+ri.length+qj.length+rj.length+valid.length := by
  intro k; cases k <;> simp only [bank,List.length_nil] <;> omega

/-- Incompatible digits actually enter and execute full physical cleanup. -/
theorem incompatible_step (q d i j : ℕ) (ha : ¬i/d+j/d<q) (tail result : List Bool) :
    ∃m≤2000*(q+d+i+j+tail.length+result.length+1),Trace.Runs code m (ctl .recordPeek)
      (bank [] (frame (unary q) (frame (unary d) tail)) (unary i) (unary j) result [] [] [] [] [] [] [] [])
      (ctl .halt) (bank [] [] [] [] [] [] [] [] [] [] [] [] [false]) := by
  have h1 := peek_record (unary q) (frame (unary d) tail) (unary i) (unary j) result
  have h2 := read_axis (unary q) (frame (unary d) tail) (unary i) (unary j) result
  have h3 := flag_true (ctl .qDone) (ctl .readD) rfl [] (frame (unary d) tail)
    (unary i) (unary j) result [] (unary q) [] [] [] [] []
  have h4 := read_denominator (unary d) tail (unary i) (unary j) result (unary q)
  have h5 := flag_true (ctl .dDone) (ctl .divideLeft) rfl [] tail
    (unary i) (unary j) result [] (unary q) (unary d) [] [] [] []
  obtain ⟨a,haClock,h6⟩ := divide_left i j d tail result (unary q)
  obtain ⟨b,hbClock,h7⟩ := divide_right j d tail result (unary q) (unary (i/d)) (unary (i%d))
  obtain ⟨c,hcClock,h8⟩ := compare_digits (i/d) (j/d) q tail result (unary d) (unary (i%d)) (unary (j%d))
  simp only [ha,decide_false] at h8
  have h9 : Trace.Runs code 1 (ctl .compareDone)
      (bank [] tail [] [] result [] [] (unary d) [] (unary (i%d)) [] (unary (j%d)) [false])
      (ctl (.fail 0)) (bank [] tail [] [] result [] [] (unary d) [] (unary (i%d)) [] (unary (j%d)) []) := by
    apply Trace.one_base code (ctl .compareDone) (ctl (.fail 0))
      (.pop .valid (ctl (.fail 0)) (ctl (.fail 0)) (ctl .clearD)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute]
  have hw := bank_width [] tail [] [] result [] [] (unary d) [] (unary (i%d)) [] (unary (j%d)) []
  simp only [List.length_nil,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate,Nat.zero_add,Nat.add_zero] at hw
  obtain ⟨z,hz,h10⟩ := SemiprimeD1StackJetRouteFailure.reject_clean _ _ hw
  have h := compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6
    (compose h7 (compose h8 (compose h9 h10))))))))
  refine ⟨_,?_,h⟩
  simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hi := Nat.div_le_self i d
  have hj := Nat.div_le_self j d
  have hri := Nat.mod_le i d
  have hrj := Nat.mod_le j d
  omega

end RiemannGaussian.SemiprimeD1StackJetRouteStep
