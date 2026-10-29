/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexClipping

/-! # Unclipped physical signed products for original kernel acquisition
Each short original factor multiplies the already accumulated tail on its
right. The exact output width grows linearly in factor count; no magnitude-fit
promise or native integer product is used to produce the result.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1KernelProductBits
open SemiprimeBitArithmetic SemiprimeBitIndexClipping

/-- Actual full signed product word and its physical report. -/
structure Run where
  /-- Unclipped exact integer word. -/
  word : SignedWord
  /-- Every multiply, sign XOR, output cell and recursive tag. -/
  clock : ℕ

/-- Multiply literal signed words without any supplied product or width answer. -/
def run : List SignedWord → Run
  | [] => ⟨⟨false,[true]⟩,1⟩
  | x::xs =>
    let tail := run xs
    let out := mulSignedBits x tail.word
    ⟨out.word,tail.clock+out.clock+3⟩

/-- The full physical product is exactly the original integer product. -/
theorem run_value (xs : List SignedWord) :
    (run xs).word.value=(xs.map SignedWord.value).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (mulSignedBits x (run xs).word).word.value=_
    rw [mulSignedBits_value,ih]
    rfl

/-- The multiplication order preserves a linear actual physical output width. -/
theorem run_width (xs : List SignedWord) (W : ℕ)
    (hw : ∀ x∈xs,x.magnitude.length ≤ W) :
    (run xs).word.magnitude.length ≤ 2*xs.length*W+1 := by
  induction xs with
  | nil => simp only [run,List.length_cons,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x xs ih =>
    have hh := hw x List.mem_cons_self
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem x hy))
    have hm := mulBits_length x.magnitude (run xs).word.magnitude
    change (mulBits x.magnitude (run xs).word.magnitude).bits.length ≤ _
    simp only [List.length_cons]
    nlinarith

/-- One explicit fixed polynomial of actual factor count and physical width. -/
def budget (n W : ℕ) : ℕ := (n+1)*(24*(2*n*W+W+2)^2+10)

/-- All multiplication reports are paid at actual widths; no decoded magnitude,
precomputed integer factor product or clipping certificate is assumed. -/
theorem run_clock (xs : List SignedWord) (W : ℕ)
    (hw : ∀ x∈xs,x.magnitude.length ≤ W) : (run xs).clock ≤ budget xs.length W := by
  induction xs with
  | nil => simp only [run,List.length_nil,budget];nlinarith
  | cons x xs ih =>
    have hh := hw x List.mem_cons_self
    have htail := fun y hy => hw y (List.mem_cons_of_mem x hy)
    have ht := ih htail
    have hwidth := run_width xs W htail
    have hx : x.magnitude.length ≤ 2*xs.length*W+W+1 := by nlinarith
    have htw : (run xs).word.magnitude.length ≤ 2*xs.length*W+W+1 := by omega
    have hm := (mulSignedBits_cost_width hx htw).1
    have hstep : 24*(2*xs.length*W+W+2)^2+10 ≤
        24*(2*(xs.length+1)*W+W+2)^2+10 := by gcongr;nlinarith
    change (run xs).clock+(mulSignedBits x (run xs).word).clock+3 ≤ _
    simp only [List.length_cons]
    calc
      _ ≤ budget xs.length W+(24*(2*xs.length*W+W+2)^2+4)+3 := by
        have hm' : (mulSignedBits x (run xs).word).clock ≤ 24*(2*xs.length*W+W+2)^2+4 := by
          simpa only [Nat.add_assoc] using hm
        omega
      _ ≤ (xs.length+2)*(24*(2*xs.length*W+W+2)^2+10) := by unfold budget;nlinarith
      _ ≤ budget (xs.length+1) W := by
        unfold budget
        simpa only [Nat.add_assoc] using Nat.mul_le_mul_left (xs.length+2) hstep

end RiemannGaussian.SemiprimeD1KernelProductBits
