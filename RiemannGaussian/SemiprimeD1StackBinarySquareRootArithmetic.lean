/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.Sqrt
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataEncoding
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # Binary greedy square root: arithmetic and actual raw-word specification
The recurrence tests exactly one descending power of two per input cell, plus
the leading power. It never materializes the value of the binary input in unary.
These are proof-side specifications; the finite machine is defined separately.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootArithmetic
open SemiprimeBitArithmetic
open SemiprimeD1StackPackedRootMetadataEncoding (baseWord base_value base_length)
/-- One arithmetic candidate bit; no answer is a runtime operand. -/
def nextRoot (d n r : ℕ) : ℕ := if (r+2^n)^2 ≤ d then r+2^n else r
/-- The n+1 descending candidate-bit tests, including the units bit. -/
def greedy (d : ℕ) : ℕ→ℕ→ℕ
  | 0,r => nextRoot d 0 r
  | n+1,r => greedy d n (nextRoot d (n+1) r)
/-- A single test halves the remaining interval for the integer square root. -/
theorem nextRoot_bounds (d n r : ℕ) (hl : r^2 ≤ d)
    (hu : d < (r+2^(n+1))^2) :
    (nextRoot d n r)^2 ≤ d ∧ d < (nextRoot d n r+2^n)^2 := by
  unfold nextRoot
  split_ifs with h
  · refine ⟨h,?_⟩
    have he : r+2^n+2^n=r+2^(n+1) := by rw [pow_succ]; omega
    rw [he]
    exact hu
  · exact ⟨hl,by omega⟩
/-- Every candidate-bit test preserves a certified interval, without trial division. -/
theorem greedy_bounds (d n r : ℕ) (hl : r^2 ≤ d)
    (hu : d < (r+2^(n+1))^2) :
    (greedy d n r)^2 ≤ d ∧ d < (greedy d n r+1)^2 := by
  induction n generalizing r with
  | zero => simpa only [greedy,pow_zero] using nextRoot_bounds d 0 r hl hu
  | succ n ih =>
    have h:=nextRoot_bounds d (n+1) r hl hu
    exact ih (nextRoot d (n+1) r) h.1 h.2
/-- The interval invariant identifies the result with the ordinary integer sqrt. -/
theorem greedy_eq_sqrt (d n : ℕ) (hd : d < 2^n) : greedy d n 0=Nat.sqrt d := by
  apply Nat.eq_sqrt'.2
  apply greedy_bounds d n 0 (by simp)
  have hp : 0 < 2^(n+1) := by positivity
  have he : 2^n ≤ 2^(n+1) := by rw [pow_succ]; omega
  have hq : 2^(n+1) ≤ (2^(n+1))^2 := by nlinarith
  simpa only [zero_add] using hd.trans_le (he.trans hq)
/-- The actual real-adder trial word, including raw padding. -/
def trial (r p : List Bool) : List Bool := (addBits r p false).bits
/-- The actual multiplier word used by the physical comparison. -/
def square (r p : List Bool) : List Bool := (mulBits (trial r p) (trial r p)).bits
/-- Exact actual comparison outcome: TRUE means reject the candidate. -/
def rejects (d r p : List Bool) : Bool := SemiprimeD1StackWordLessExecution.answer d (square r p)
/-- The physical branch retains either the old raw root or the real-adder word. -/
def nextWord (d r p : List Bool) : List Bool := if rejects d r p then r else trial r p
/-- Proof-side raw-word trace of exactly n+1 candidate-bit iterations. -/
def wordLoop (d : List Bool) : ℕ→List Bool→List Bool
  | 0,r => nextWord d r (baseWord 0)
  | n+1,r => wordLoop d n (nextWord d r (baseWord (n+1)))
/-- The final physical reverse and high-zero trim produce a compact word. -/
def output (d : List Bool) : List Bool :=
  SemiprimeD1StackReduceExecution.trimReverse (wordLoop d d.length []).reverse
/-- The adder trial has the exact expected integer value. -/
theorem trial_value (r p : List Bool) : bitValue (trial r p)=bitValue r+bitValue p := by
  simpa [trial,bitNat] using addBits_correct r p false
/-- The actual square is computed from both real trial copies. -/
theorem square_value (r p : List Bool) : bitValue (square r p)=(bitValue r+bitValue p)^2 := by
  rw [square,mulBits_correct,trial_value,pow_two]
/-- Exact branch semantics follows from the physical subtractor borrow. -/
theorem rejects_true (d r p : List Bool) :
    rejects d r p=true ↔ bitValue d < (bitValue r+bitValue p)^2 := by
  rw [rejects,SemiprimeD1StackWordLessExecution.answer_true,square_value]
/-- Both physical branches implement the arithmetic candidate-bit test. -/
theorem nextWord_value (d r : List Bool) (n : ℕ) :
    bitValue (nextWord d r (baseWord n))=nextRoot (bitValue d) n (bitValue r) := by
  unfold nextWord nextRoot
  by_cases h : rejects d r (baseWord n)=true
  · have hb:= (rejects_true d r (baseWord n)).1 h
    rw [base_value] at hb
    simp only [h,ite_true,show ¬(bitValue r+2^n)^2 ≤ bitValue d by omega,ite_false]
  · have hb : (bitValue r+2^n)^2 ≤ bitValue d := by
      have ht:=rejects_true d r (baseWord n)
      rw [base_value] at ht
      exact Nat.le_of_not_lt (fun hx => h (ht.2 hx))
    simp only [h,Bool.false_eq_true,ite_false,hb,ite_true,trial_value,base_value]
/-- Raw-word execution and the descending arithmetic recurrence agree universally. -/
theorem wordLoop_value (d r : List Bool) (n : ℕ) :
    bitValue (wordLoop d n r)=greedy (bitValue d) n (bitValue r) := by
  induction n generalizing r with
  | zero => exact nextWord_value d r 0
  | succ n ih => rw [wordLoop,ih,nextWord_value,greedy]
/-- The final raw-word specification is the square root for EVERY binary input. -/
theorem output_value (d : List Bool) : bitValue (output d)=Nat.sqrt (bitValue d) := by
  rw [output,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse,wordLoop_value]
  exact greedy_eq_sqrt (bitValue d) d.length (bitValue_lt_width d)
/-- Real final trimming gives the compact byte ABI, including zero and padded inputs. -/
theorem output_compact (d : List Bool) : SemiprimeSourceCompactBits.Compact (output d) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- Actual raw-adder padding grows by at most one cell beyond the longer operand. -/
theorem trial_length (r p : List Bool) : (trial r p).length ≤ max r.length p.length+1 := by
  have h:=(addBits_counts r p false).2.2.2.2
  exact h
/-- The existing raw multiplication width theorem applies to the actual square. -/
theorem square_length (r p : List Bool) : (square r p).length ≤ 3*(trial r p).length := by
  have h:=mulBits_length (trial r p) (trial r p)
  change (square r p).length ≤ 2*(trial r p).length+(trial r p).length at h
  omega
/-- Branch selection cannot exceed the same adder width envelope. -/
theorem nextWord_length (d r p : List Bool) :
    (nextWord d r p).length ≤ max r.length p.length+1 := by
  unfold nextWord
  split_ifs
  · exact (le_max_left r.length p.length).trans (Nat.le_add_right _ 1)
  · exact trial_length r p
/-- n+1 actual tests add only n+1 raw padding cells beyond the largest input word. -/
theorem wordLoop_length (d r : List Bool) (n : ℕ) :
    (wordLoop d n r).length ≤ max r.length (n+1)+(n+1) := by
  induction n generalizing r with
  | zero => simpa only [wordLoop,base_length] using nextWord_length d r (baseWord 0)
  | succ n ih =>
    have h0:=nextWord_length d r (baseWord (n+1))
    rw [base_length] at h0
    have h1:=ih (nextWord d r (baseWord (n+1)))
    have hm : max (nextWord d r (baseWord (n+1))).length (n+1) ≤ max r.length (n+2)+1 :=
      max_le (by omega) (by omega)
    change (wordLoop d n (nextWord d r (baseWord (n+1)))).length ≤ _
    omega
/-- With an empty original root, every completed raw root has linear bit length. -/
theorem original_word_length (d : List Bool) :
    (wordLoop d d.length []).length ≤ 2*(d.length+1) := by
  have h:=wordLoop_length d [] d.length
  simpa only [List.length_nil,max_eq_right (Nat.zero_le _),two_mul] using h
end RiemannGaussian.SemiprimeD1StackBinarySquareRootArithmetic
