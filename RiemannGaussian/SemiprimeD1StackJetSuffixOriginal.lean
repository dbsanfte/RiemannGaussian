/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixScan
/-! # Original positive axes acquire their own physical suffix records and rank -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffixOriginal
open SemiprimeD1StackJetSuffix SemiprimeD1StackJetSuffixCalls
open SemiprimeD1StackJetSuffixPass SemiprimeD1StackJetSuffixScan
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackJetSuffix.control

theorem frame_append (word xs ys : List Bool) : frame word (xs++ys)=frame word xs++ys := by
  induction word with
  | nil => rfl
  | cons b bs ih => simp only [frame,ih,List.cons_append]

theorem fields_append (xs ys : List ℕ) : fields (xs++ys)=fields xs++fields ys := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append,fields,ih,frame_append]

/-- The acquired first-pass tape is exactly the reverse list of original fields. -/
theorem reverseFields_eq (xs : List ℕ) (acc : List Bool) :
    reverseFields xs acc=fields xs.reverse++acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons q qs ih =>
    simp only [reverseFields,ih,List.reverse_cons,fields_append,fields]
    rw [List.append_assoc,←frame_append]
    rfl

theorem result_append (xs ys : List ℕ) (d : ℕ) (acc : List Bool) :
    result (xs++ys) d acc=result ys (result xs d acc).1 (result xs d acc).2 := by
  induction xs generalizing d acc with
  | nil => rfl
  | cons q qs ih => exact ih (q*d) (frame (unary q) (frame (unary d) acc))

/-- Exact tape of suffix records, with a generic original tail radix. -/
def recordTape : List ℕ → ℕ → List Bool → List Bool
  | [],_,acc => acc
  | q::qs,d,acc => frame (unary q) (frame (unary (qs.prod*d)) (recordTape qs d acc))

theorem result_reverse (xs : List ℕ) (d : ℕ) (acc : List Bool) :
    result xs.reverse d acc=(xs.prod*d,recordTape xs d acc) := by
  induction xs with
  | nil => simp [result,recordTape]
  | cons q qs ih =>
    simp only [List.reverse_cons,result_append,ih,result,recordTape,List.prod_cons]
    simp only [Nat.mul_assoc]

/-- Starting the suffix scan physically acquires the rank-one counter. -/
theorem start (rev : List Bool) : Trace.Runs code 1 (ctl .startSuffix)
    (data [] rev [] [] [] [] [] [])
    (ctl .suffixPeek) (data [] rev [] (unary 1) [] [] [] []) := by
  apply Trace.one_base code (ctl .startSuffix) (ctl .suffixPeek)
    (.push .radix true (ctl .suffixPeek)) _ _ rfl
  · rfl
  · simp [SemiprimeD1StackBytecode.execute,unary]

/-- Final success is a physical output validity cell. -/
theorem success (rank records : List Bool) : Trace.Runs code 1 (ctl .success)
    (data [] [] [] rank [] records [] [])
    (ctl .halt) (data [] [] [] rank [] records [] [true]) := by
  apply Trace.one_base code (ctl .success) (ctl .halt)
    (.push .valid true (ctl .halt)) _ _ rfl
  · rfl
  · simp [SemiprimeD1StackBytecode.execute]

/-- Closed original-data suffix acquisition: no radix/product/catalogue is supplied.
Every parsed field, product, copy and erased counter belongs to this actual trace. -/
theorem acquire (axes : List ℕ) (hp : ∀q∈axes,0<q) :
    ∃m≤100*(axes.length+1)*(axes.prod+1),Trace.Runs code m (ctl .vector)
      (data (vectorBits (axes.map unary)) [] [] [] [] [] [] [])
      (ctl .halt) (data [] [] [] (unary axes.prod) [] (recordTape axes 1 []) [] [true]) := by
  have h1 := first_pass axes hp [] [] [] []
  rw [reverseFields_eq,List.append_nil] at h1
  have h2 := start (fields axes.reverse)
  obtain ⟨n,hn,h3⟩ := scan axes.reverse 1 []
  rw [result_reverse] at h3
  simp only [Nat.mul_one] at h3
  have h4 := success (unary axes.prod) (recordTape axes 1 [])
  have h := compose h1 (compose h2 (compose h3 h4))
  refine ⟨_,?_,h⟩
  have hr : 0<axes.prod := SemiprimeD1StackRouteArithmetic.rank_pos axes hp
  have hb := scanBudget_le axes.reverse 1 axes.prod
    (by simpa only [List.mem_reverse] using hp) (by omega) (by simp)
  have hsum : axes.sum≤axes.length*axes.prod := by
    apply List.sum_le_length_nsmul
    intro q hq
    obtain ⟨before,after,he⟩ := List.mem_iff_append.mp hq
    have hbefore : 0<before.prod := List.prod_pos (by intro v hv; apply hp v; rw [he]; simp [hv])
    have hafter : 0<after.prod := List.prod_pos (by intro v hv; apply hp v; rw [he]; simp [hv])
    rw [he,List.prod_append,List.prod_cons]
    exact (Nat.le_mul_of_pos_right q hafter).trans (Nat.le_mul_of_pos_left _ hbefore)
  simp only [List.length_reverse] at hb
  nlinarith

/-- Literal initial physical data and empty return stack. -/
def initial (axes : List ℕ) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨some (ctl .vector),none,none,data (vectorBits (axes.map unary)) [] [] [] [] [] [] [],[]⟩

/-- Exact clean data returned by the executed original suffix acquisition. -/
def final (axes : List ℕ) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨none,none,none,data [] [] [] (unary axes.prod) [] (recordTape axes 1 []) [] [true],[]⟩

/-- Closed finite-stack execution, including the literal final halt. -/
theorem acquire_run (axes : List ℕ) (hp : ∀q∈axes,0<q) :
    ∃m≤100*(axes.length+1)*(axes.prod+1)+1,
      SemiprimeD1StackCalls.run code m (initial axes)=some (final axes) := by
  obtain ⟨m,hm,ht⟩ := acquire axes hp
  obtain ⟨out,hr,ho⟩ := ht [] (initial axes) ⟨rfl,rfl,rfl⟩
  have hh := Trace.halt_run code (ctl .halt) rfl
    (data [] [] [] (unary axes.prod) [] (recordTape axes 1 []) [] [true]) [] out ho
  refine ⟨m+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh

end RiemannGaussian.SemiprimeD1StackJetSuffixOriginal
