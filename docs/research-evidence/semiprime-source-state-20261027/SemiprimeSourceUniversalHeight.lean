/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceUniversal
import RiemannGaussian.SemiprimeBinomialExecutionBounds

/-! # Integer scratch bounds for the executed universal numerator supplier
All suffix statements refer to the actual right-recursive sum and difference
functions. Actual parity coefficients come from the already executed solver.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RiemannGaussian.SemiprimeSourceUniversalHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.MatrixSupport SqrtLog
open SemiprimeMaterializedSourceUniversal
variable {r Q R : ℕ}

/-- An actual equality register is literally zero or one. -/
theorem delta_zero_or_one (y u : UniversalType r Q 1) :
    (delta y u).value=0 ∨ (delta y u).value=1 := by
  unfold SemiprimeMaterializedSourceUniversal.delta
  dsimp only
  split_ifs <;> simp

/-- Equality leaves need at most one magnitude bit. -/
theorem delta_abs (y u : UniversalType r Q 1) : |(delta y u).value| ≤ (1:ℤ) := by
  rcases delta_zero_or_one y u with h|h <;> rw [h] <;> norm_num

/-- Every actual two-branch finite difference is bounded before cancellation. -/
theorem difference_abs (xs : List (Fin Q)) (y u : UniversalType r Q 1) :
    |(difference xs y u).value| ≤ (2^xs.length:ℕ) := by
  induction xs generalizing u with
  | nil => simpa only [difference,List.length_nil,pow_zero,Nat.cast_one] using delta_abs y u
  | cons a xs ih =>
    have hl := ih u
    have hr := ih (swapPositions 0 {a} u)
    simp only [difference,List.length_cons,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    exact (abs_sub _ _).trans (by linarith)

/-- Every recursive difference frame, with any accumulated swaps, has the same global cap. -/
theorem difference_frame_abs (xs : List (Fin Q)) (k : ℕ) (y u : UniversalType r Q 1) :
    |(difference (xs.drop k) y u).value| ≤ (2^xs.length:ℕ) := by
  exact (difference_abs _ y u).trans (by exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (by simp only [List.length_drop]; omega)))

/-- All actually acquired scalar power prefixes obey the native exponent cap. -/
theorem powerTwo_prefix_abs (k R : ℕ) (hk : k ≤ R) :
    |(powerTwo k).value| ≤ (2^R:ℕ) := by
  rw [powerTwo_value,abs_pow]
  norm_num only [show |(2:ℤ)|=2 by decide]
  exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hk

/-- Generic right-recursive sum height, without cancellation assumptions. -/
theorem sumRuns_abs {α : Type*} (f : α → Run ℤ) (xs : List α) (B : ℕ)
    (hf : ∀ a∈xs,|(f a).value| ≤ (B:ℤ)) :
    |(sumRuns f xs).value| ≤ (xs.length*B:ℕ) := by
  induction xs with
  | nil => simp [sumRuns]
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht := ih (fun x hx => hf x (by simp [hx]))
    simp only [Nat.cast_mul] at ht
    simp only [sumRuns,List.length_cons,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    exact (abs_add_le _ _).trans (by nlinarith)

/-- Every actual right-recursive suffix has its own literal remaining-term count. -/
theorem sumRuns_suffix_abs {α : Type*} (f : α → Run ℤ) (xs : List α) (B k : ℕ)
    (hf : ∀ a∈xs,|(f a).value| ≤ (B:ℤ)) :
    |(sumRuns f (xs.drop k)).value| ≤ ((xs.drop k).length*B:ℕ) :=
  sumRuns_abs f _ B (fun a ha => hf a (List.mem_of_mem_drop ha))

/-- A left prefix is also bounded if retained by an implementation adapter. -/
theorem sumRuns_prefix_abs {α : Type*} (f : α → Run ℤ) (xs : List α) (B k : ℕ)
    (hf : ∀ a∈xs,|(f a).value| ≤ (B:ℤ)) :
    |(sumRuns f (xs.take k)).value| ≤ ((xs.take k).length*B:ℕ) :=
  sumRuns_abs f _ B (fun a ha => hf a (List.mem_of_mem_take ha))

/-- The partial multiplication preceding a difference uses only its original coefficient. -/
theorem contribution_partial_abs (c : Fin R → ℤ) (j : Fin R) :
    |c j*(powerTwo (R-1-j.val)).value| ≤ (c j).natAbs*2^R := by
  rw [abs_mul]
  have hp := powerTwo_prefix_abs (R-1-j.val) R (by omega)
  have hc : |c j|=((c j).natAbs:ℤ) := Int.natCast_natAbs (c j) |>.symm
  rw [hc]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

/-- Every executed subset contribution, including rejected cardinalities. -/
theorem contribution_abs (c : Fin R → ℤ) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (s : Finset (Fin Q)) :
    |(contribution c j t y u s).value| ≤ ((c j).natAbs*2^R*2^Q:ℕ) := by
  have hp := contribution_partial_abs c j
  have hd := difference_abs (positions s) y (swapPositions 0 (activePositions t) u)
  have hs : (positions s).length ≤ Q := by rw [positions_length]; exact s.card_le_univ.trans_eq (by simp)
  have hd' : |(difference (positions s) y (swapPositions 0 (activePositions t) u)).value| ≤ (2^Q:ℕ) :=
    hd.trans (by exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hs)
  unfold contribution
  split_ifs
  · dsimp only
    rw [abs_mul]
    exact mul_le_mul hp hd' (abs_nonneg _) (by positivity)
  · simp

/-- One native subset-term envelope. -/
def termBound (C R Q : ℕ) : ℕ := C*2^R*2^Q

/-- Every subset callback uses the same original coefficient envelope. -/
theorem contribution_uniform (c : Fin R → ℤ) (C : ℕ)
    (hc : ∀ j,|(c j)| ≤ (C:ℤ)) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (s : Finset (Fin Q)) :
    |(contribution c j t y u s).value| ≤ (termBound C R Q:ℕ) := by
  have hj : (c j).natAbs ≤ C := by
    have h := hc j
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  exact (contribution_abs c j t y u s).trans (by exact_mod_cast (Nat.mul_le_mul_right (2^Q) (Nat.mul_le_mul_right (2^R) hj)))

/-- Every actual subset-sum recursion frame has a term-count bound. -/
theorem inner_suffix_abs (c : Fin R → ℤ) (C : ℕ)
    (hc : ∀ j,|(c j)| ≤ (C:ℤ)) (j : Fin R) (t : Fin Q)
    (y u : UniversalType r Q 1) (k : ℕ) :
    |(sumRuns (contribution c j t y u) ((subsets (active t)).value.drop k)).value| ≤
      (2^Q*termBound C R Q:ℕ) := by
  have h := sumRuns_suffix_abs (contribution c j t y u) (subsets (active t)).value
    (termBound C R Q) k (fun S _ => contribution_uniform c C hc j t y u S)
  have hl : ((subsets (active t)).value.drop k).length ≤ 2^Q := by
    rw [List.length_drop,subsets_length]
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide : 0<2) (active_length_le t))
  exact h.trans (by exact_mod_cast Nat.mul_le_mul_right (termBound C R Q) hl)

/-- Every parity-index sum recursion frame is bounded before cancellation. -/
theorem outer_suffix_abs (c : Fin R → ℤ) (C : ℕ)
    (hc : ∀ j,|(c j)| ≤ (C:ℤ)) (t : Fin Q)
    (y u : UniversalType r Q 1) (k : ℕ) :
    |(sumRuns (fun j : Fin R => sumRuns (contribution c j t y u) (subsets (active t)).value)
      ((List.finRange R).drop k)).value| ≤ (R*(2^Q*termBound C R Q):ℕ) := by
  have h := sumRuns_suffix_abs
    (fun j : Fin R => sumRuns (contribution c j t y u) (subsets (active t)).value)
    (List.finRange R) (2^Q*termBound C R Q) k (fun j _ => by
      simpa only [List.drop_zero] using inner_suffix_abs c C hc j t y u 0)
  have hl : ((List.finRange R).drop k).length ≤ R := by
    simp only [List.length_drop,List.length_finRange]
    omega
  exact h.trans (by exact_mod_cast Nat.mul_le_mul_right (2^Q*termBound C R Q) hl)

/-- The actual entry report has the same bound as its outermost suffix. -/
theorem entry_abs (c : Fin R → ℤ) (C : ℕ)
    (hc : ∀ j,|(c j)| ≤ (C:ℤ)) (t : Fin Q) (u y : UniversalType r Q 1) :
    |(entry c t u y).value| ≤ (R*(2^Q*termBound C R Q):ℕ) := by
  simpa only [entry,List.drop_zero] using outer_suffix_abs c C hc t y u 0

/-- The actual parity coefficient exponent, not a supplied coefficient answer. -/
def coefficientExponent (A R : ℕ) : ℕ := R*(A+Nat.clog 2 (R+1)+1)

/-- Coarse polynomial bit exponent for all original acquired universal entries. -/
def entryExponent (A Q R : ℕ) : ℕ := coefficientExponent A R+2*R+2*Q

/-- Explicit scalar majorant fits a polynomial exponent in original dimensions. -/
theorem entry_majorant (A Q R : ℕ) :
    R*(2^Q*termBound (2^(coefficientExponent A R)) R Q) ≤ 2^(entryExponent A Q R) := by
  calc
    _ ≤ 2^R*(2^Q*termBound (2^(coefficientExponent A R)) R Q) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n:=R)))
    _ = _ := by unfold termBound entryExponent; simp only [← pow_add]; congr 1; omega

/-- The executed cached parity supplier gives every entry an original-input height. -/
theorem entry_acquired_abs (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) :
    |(entry (SemiprimeBinomialExecutionTracked.acquiredParity A R) t u y).value| ≤
      (2^(entryExponent A Q R):ℕ) := by
  exact (entry_abs _ (2^(coefficientExponent A R))
    (SemiprimeBinomialExecutionBounds.acquiredParity_bound_power A R) t u y).trans
    (by exact_mod_cast entry_majorant A Q R)

/-- The source zero-extended numerator inherits that actual acquired height. -/
theorem extended_acquired_abs (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q 1) :
    |SemiprimeUniversalNumeratorExecution.extended
      (SemiprimeBinomialExecutionTracked.acquiredParity A R) 0 t g u y| ≤
      (2^(entryExponent A Q R):ℕ) := by
  have he := entry_value A (SemiprimeBinomialExecutionTracked.acquiredParity A R)
    (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R) t u y
  have hs := SemiprimeUniversalNumeratorExecution.entry_eq A
    (SemiprimeBinomialExecutionTracked.acquiredParity A R)
    (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R) 0 t u y
  have hb := entry_acquired_abs A R t u y
  unfold SemiprimeUniversalNumeratorExecution.extended
  split_ifs
  · rw [hs,← he]
    exact hb
  · simp
  · simp

/-- The original interpolation frontend's computed parity is the same vector. -/
theorem extended_parity_abs (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q 1) :
    |SemiprimeUniversalNumeratorExecution.extended
      (SemiprimeBinomialExecution.parity A R) 0 t g u y| ≤
      (2^(entryExponent A Q R):ℕ) := by
  have hc : SemiprimeBinomialExecutionTracked.acquiredParity A R = SemiprimeBinomialExecution.parity A R :=
    (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R).trans (SemiprimeBinomialExecution.parity_eq A R).symm
  rw [← hc]
  exact extended_acquired_abs A R t g u y

/-- A fully polynomial bit exponent, including zero dimensions. -/
theorem entryExponent_polynomial (A Q R : ℕ) :
    entryExponent A Q R ≤ R*(A+R+2)+2*R+2*Q := by
  have hc : Nat.clog 2 (R+1) ≤ R+1 := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  unfold entryExponent coefficientExponent
  nlinarith

/-- Every cached table cell is an actual bounded acquired entry. -/
theorem table_cell_abs (A R : ℕ) (words : List (UniversalType r Q 1))
    (matrix : List (List ℤ)) (row : List ℤ) (z : ℤ)
    (hm : matrix∈(table A R words).value) (hr : row∈matrix) (hz : z∈row) :
    |z| ≤ (2^(entryExponent A Q R):ℕ) := by
  simp only [table,collect_value] at hm
  obtain ⟨t,_,ht⟩ := List.mem_map.mp hm
  subst matrix
  obtain ⟨u,_,hu⟩ := List.mem_map.mp hr
  subst row
  obtain ⟨y,_,hy⟩ := List.mem_map.mp hz
  subst z
  exact entry_acquired_abs A R t u y

/-- The materialized table has exactly the advertised number of node matrices. -/
theorem table_length (A R : ℕ) (words : List (UniversalType r Q 1)) :
    (table A R words).value.length=Q := by
  simp only [table,collect_value,List.length_map,List.length_finRange]

/-- Every actual matrix has the original row count, including empty banks. -/
theorem table_matrix_length (A R : ℕ) (words : List (UniversalType r Q 1))
    (matrix : List (List ℤ)) (hm : matrix∈(table A R words).value) :
    matrix.length=words.length := by
  simp only [table,collect_value] at hm
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hm
  simp only [List.length_map]

/-- Every actual cached row has the original column count. -/
theorem table_row_length (A R : ℕ) (words : List (UniversalType r Q 1))
    (matrix : List (List ℤ)) (row : List ℤ)
    (hm : matrix∈(table A R words).value) (hr : row∈matrix) :
    row.length=words.length := by
  simp only [table,collect_value] at hm
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
  simp only [List.length_map]

/-- The actual cached Pascal kernel obeys the original binomial cap at every index. -/
theorem acquired_kernel_bound (A R i : ℕ) (hi : i ≤ R) :
    SemiprimeBinomialExecution.natCoeff (SemiprimeBinomialExecutionTracked.acquireChoose R A).coefficients i ≤ 2^A := by
  rw [SemiprimeBinomialExecutionTracked.acquireChoose_value]
  exact SemiprimeBinomialExecutionBounds.chooseRow_bound R A i hi

/-- Every actual cached reversed target has its original power-of-two cap. -/
theorem acquired_target_bound (A R k : ℕ) (hk : k<R) :
    |SemiprimeBinomialExecution.coeff
      (SemiprimeBinomialExecutionTracked.acquireLower (SemiprimeBinomialExecutionTracked.sign A).1 R).coefficients
      (R-(k+1))| ≤ (2^R:ℕ) := by
  rw [SemiprimeBinomialExecutionTracked.acquireLower_value _ _ _ (by omega),
    SemiprimeBinomialExecutionTracked.sign_value]
  exact SemiprimeBinomialExecutionBounds.target_bound A R k

/-- Every solve prefix is bounded for the LITERAL acquired kernel and target cache. -/
theorem acquired_solve_prefix_bound (A R len : ℕ) (hlen : len ≤ R) (i : ℕ) (hi : i<len) :
    |SemiprimeBinomialExecution.coeff
      (SemiprimeBinomialExecution.solve (SemiprimeBinomialExecutionTracked.acquireChoose R A).coefficients
        (fun k => SemiprimeBinomialExecution.coeff
          (SemiprimeBinomialExecutionTracked.acquireLower (SemiprimeBinomialExecutionTracked.sign A).1 R).coefficients
          (R-(k+1))) len).coefficients i| ≤
      (2^R*(SemiprimeBinomialExecutionBounds.solveBase R (2^A))^len:ℕ) :=
  SemiprimeBinomialExecutionBounds.solve_bound _ _ R (2^A) (2^R)
    (fun k hk => acquired_kernel_bound A R k hk) (fun k hk => acquired_target_bound A R k hk)
    len hlen i hi

/-- Every partial dot within that actual prefix has a cancellation-independent cap. -/
theorem acquired_dot_prefix_bound (A R len m : ℕ) (hlen : len ≤ R) (hm : m ≤ len) :
    |(SemiprimeBinomialExecution.dot (SemiprimeBinomialExecutionTracked.acquireChoose R A).coefficients
      (SemiprimeBinomialExecution.solve (SemiprimeBinomialExecutionTracked.acquireChoose R A).coefficients
        (fun k => SemiprimeBinomialExecution.coeff
          (SemiprimeBinomialExecutionTracked.acquireLower (SemiprimeBinomialExecutionTracked.sign A).1 R).coefficients
          (R-(k+1))) len).coefficients len m).value| ≤
      (m*2^A*(2^R*(SemiprimeBinomialExecutionBounds.solveBase R (2^A))^len):ℕ) := by
  apply SemiprimeBinomialExecutionBounds.dot_bound
  · intro i _
    exact acquired_kernel_bound A R (len-i) (by omega)
  · intro i hi
    exact acquired_solve_prefix_bound A R len hlen i (by omega)

/-- Uniform nested cache dimensions give an exact scalar-cell count. -/
theorem flatMap_length_uniform {α β : Type*} (xs : List α) (f : α → List β) (D : ℕ)
    (h : ∀ x∈xs,(f x).length=D) : (xs.flatMap f).length=xs.length*D := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,ha,ht]
    ring

/-- The executed numerator table stores exactly Q times the square of the actual bank length. -/
theorem table_scalar_cells (A R : ℕ) (words : List (UniversalType r Q 1)) :
    ((table A R words).value.flatMap (fun matrix => matrix.flatMap id)).length=
      Q*(words.length*words.length) := by
  rw [flatMap_length_uniform _ _ (words.length*words.length)]
  · rw [table_length]
  · intro matrix hm
    rw [flatMap_length_uniform _ id words.length]
    · rw [table_matrix_length A R words matrix hm]
    · intro row hr
      exact table_row_length A R words matrix row hm hr

end RiemannGaussian.SemiprimeSourceUniversalHeight
