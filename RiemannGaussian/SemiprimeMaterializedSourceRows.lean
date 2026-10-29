/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceUniversal
import RiemannGaussian.SemiprimeSourceArrayAcquisition

/-! # Acquired source expressions with their actual generation and array clocks
Finite expressions are constructed by paid list traversals before compilation.
No polynomial or requested coefficient is an execution input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourceRows
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SubexpRowInterpolation SqrtLog
open SemiprimeMaterializedSourceUniversal
open SemiprimeSourceCodeArrays SemiprimeSourceInterpolationExecution
variable {r Q R : ℕ}

/-- Build a sum or product AST by an actual finite list fold. -/
def foldCodes (multiply : Bool) : List (PolynomialCode ℚ) → Run (PolynomialCode ℚ)
  | [] => ⟨.constant (if multiply then 1 else 0),1⟩
  | a::as =>
      let tail := foldCodes multiply as
      ⟨if multiply then .mul a tail.value else .add a tail.value,tail.work+2⟩

theorem foldCodes_value (multiply : Bool) (xs : List (PolynomialCode ℚ)) :
    (foldCodes multiply xs).value=
      if multiply then PolynomialCode.product xs else PolynomialCode.sum xs := by
  induction xs with
  | nil => cases multiply <;> rfl
  | cons a as ih => cases multiply <;> simp [foldCodes,ih,PolynomialCode.product,PolynomialCode.sum]

theorem foldCodes_work (multiply : Bool) (xs : List (PolynomialCode ℚ)) :
    (foldCodes multiply xs).work=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [foldCodes,List.length_cons,ih]; omega

/-- One literal Lagrange factor, with denominator inversion and finite membership charged. -/
def basisTerm (s : Finset (Fin Q)) (i j : Fin Q) : Run (PolynomialCode ℚ) :=
  if j∈s.erase i then
    ⟨.mul (.constant ((units Q).differenceInverse i j))
      (.add .indeterminate (.constant (-node Q j))),Q+10⟩
  else ⟨.constant 1,Q+3⟩

/-- Full finite source basis constructor, including all factor ASTs and list cells. -/
def basis (s : Finset (Fin Q)) (i : Fin Q) : Run (PolynomialCode ℚ) :=
  let terms := collect (basisTerm s i) (List.finRange Q)
  let product := foldCodes true terms.value
  ⟨.mul (.mul (.constant ((units Q).nodeInverse i)) .indeterminate) product.value,
    terms.work+product.work+7⟩

theorem basis_value (s : Finset (Fin Q)) (i : Fin Q) :
    (basis s i).value=basisCode (units Q) s i := by
  simp only [basis,collect_value,foldCodes_value,ite_true,basisCode,List.ofFn_eq_map]
  congr 2
  apply List.map_congr_left
  intro j _
  unfold basisTerm
  split_ifs <;> rfl

/-- Basis construction work, including complete finite membership scans. -/
theorem basis_work (s : Finset (Fin Q)) (i : Fin Q) :
    (basis s i).work≤Q*(Q+14)+9 := by
  have ht := collect_work (basisTerm s i) (List.finRange Q) (Q+10) (by
    intro j _
    unfold basisTerm
    split_ifs <;> dsimp only <;> omega)
  rw [List.length_finRange] at ht
  simp only [basis,foldCodes_work,collect_value,List.length_map,List.length_finRange]
  nlinarith

/-- Actual prescribed scalar from an acquired numerator, including zero-extension tests. -/
def prescription (c : Fin R → ℤ) (u y : UniversalType r Q 1) (t : Fin Q) : Run ℚ :=
  if (u.head t=y.head t ∧ u.slot 0 t≠y.head t) ∧ y.slot 0 t≠y.head t then
    let numerator := SemiprimeMaterializedSourceUniversal.entry c t u y
    let power := powerTwo (R-1)
    ⟨-((numerator.value : ℚ)/(power.value : ℚ)),numerator.work+power.work+9⟩
  else ⟨0,5⟩

/-- This coefficient supplier is exactly the original finite source prescription. -/
theorem prescription_value (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (u y : UniversalType r Q 1) (t : Fin Q) :
    (prescription c u y t).value=
      SemiprimeSourceInterpolationExecution.prescription c u 0 y t := by
  have he : (SemiprimeMaterializedSourceUniversal.entry c t u y).value=
      SemiprimeUniversalNumeratorExecution.entry c 0 t u y :=
    (SemiprimeMaterializedSourceUniversal.entry_value A c hc t u y).trans
      (SemiprimeUniversalNumeratorExecution.entry_eq A c hc 0 t u y).symm
  unfold prescription SemiprimeSourceInterpolationExecution.prescription
    SemiprimeUniversalNumeratorExecution.extended
  by_cases hu : u.head t=y.head t ∧ u.slot 0 t≠y.head t
  · by_cases hy : y.slot 0 t≠y.head t
    · simp [hu.1,hu.2,hy,he,powerTwo_value,
        SemiprimeSourceInterpolationExecution.denominator,div_eq_mul_inv,mul_comm]
    · simp [hu,hy]
  · simp [hu]

/-- One correction summand: both its scalar numerator and basis AST are acquired. -/
def correctionTerm (c : Fin R → ℤ) (u y : UniversalType r Q 1)
    (s : Finset (Fin Q)) (i : Fin Q) : Run (PolynomialCode ℚ) :=
  if i∈s then
    let scalar := prescription c u y i
    let poly := basis s i
    ⟨.mul (.constant scalar.value) poly.value,scalar.work+poly.work+Q+4⟩
  else ⟨.constant 0,Q+2⟩

/-- Acquired correction AST with every candidate coordinate explicitly traversed. -/
def correction (c : Fin R → ℤ) (u y : UniversalType r Q 1) (s : Finset (Fin Q)) :
    Run (PolynomialCode ℚ) :=
  let terms := collect (correctionTerm c u y s) (List.finRange Q)
  let sum := foldCodes false terms.value
  ⟨sum.value,terms.work+sum.work⟩

theorem correction_value (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (u y : UniversalType r Q 1) (s : Finset (Fin Q)) :
    (correction c u y s).value=correctionCode (units Q) s
      (SemiprimeSourceInterpolationExecution.prescription c u 0 y) := by
  simp only [correction,collect_value,foldCodes_value,Bool.false_eq_true,ite_false,correctionCode,List.ofFn_eq_map]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold correctionTerm
  split_ifs
  · simp only [basis_value,prescription_value A c hc]
  · rfl

/-- Actual row expression from acquired scalar prescriptions and exact register equality. -/
def rowCode (c : Fin R → ℤ) (u y : UniversalType r Q 1) : Run (PolynomialCode ℚ) :=
  let eq := delta y u
  let mismatches := mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y
  if mismatches.card≤R then
    let extra := correction c u y mismatches
    ⟨.add (.constant (eq.value : ℚ)) extra.value,eq.work+extra.work+(Q+1)*(Q+1)+4⟩
  else ⟨.add (.constant (eq.value : ℚ)) (.constant 0),eq.work+(Q+1)*(Q+1)+4⟩

theorem rowCode_value (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (u y : UniversalType r Q 1) :
    (rowCode c u y).value=SemiprimeSourceInterpolationExecution.code c u 0 y := by
  unfold rowCode SemiprimeSourceInterpolationExecution.code mismatchRowCode
  simp only [mem_correctionColumns]
  split_ifs
  · rw [correction_value A c hc,delta_value]
    simp only [LayoutNumerator.integerDelta,Pi.single_apply]
    by_cases h : u=y
    · subst y
      simp
    · have hy : y≠u := Ne.symm h
      simp [h,hy]
  · rw [delta_value]
    simp only [LayoutNumerator.integerDelta,Pi.single_apply]
    by_cases h : u=y
    · subst y
      simp
    · have hy : y≠u := Ne.symm h
      simp [h,hy]

/-- Scalar work envelope for an acquired prescription. -/
def prescriptionBudget (Q R : ℕ) : ℕ := entryBudget Q R+2*R+12

theorem prescription_work (c : Fin R → ℤ) (u y : UniversalType r Q 1) (t : Fin Q) :
    (prescription c u y t).work≤prescriptionBudget Q R := by
  have he := entry_work c t u y
  unfold prescription
  split_ifs <;> dsimp only
  · rw [powerTwo_work]
    unfold prescriptionBudget
    have hr : R-1≤R := Nat.sub_le _ _
    omega
  · unfold prescriptionBudget
    omega

/-- Every code-generation branch, including rejected coordinates and columns, is paid. -/
def codeBudget (Q R : ℕ) : ℕ :=
  Q*(prescriptionBudget Q R+Q*(Q+14)+2*Q+21)+7*Q+(Q+1)*(Q+1)+9

theorem rowCode_work (c : Fin R → ℤ) (u y : UniversalType r Q 1) :
    (rowCode c u y).work≤codeBudget Q R := by
  have ht (s : Finset (Fin Q)) (i : Fin Q) :
      (correctionTerm c u y s i).work≤prescriptionBudget Q R+Q*(Q+14)+Q+13 := by
    have hp := prescription_work c u y i
    have hb := basis_work s i
    unfold correctionTerm
    split_ifs <;> dsimp only <;> omega
  have hc (s : Finset (Fin Q)) :
      (correction c u y s).work≤Q*(prescriptionBudget Q R+Q*(Q+14)+Q+15)+1+(2*Q+1) := by
    have h := collect_work (correctionTerm c u y s) (List.finRange Q)
      (prescriptionBudget Q R+Q*(Q+14)+Q+13) (fun i _ => ht s i)
    rw [List.length_finRange] at h
    have he : Q*(prescriptionBudget Q R+Q*(Q+14)+Q+13+2)=
        Q*(prescriptionBudget Q R+Q*(Q+14)+Q+15) := by ring
    rw [he] at h
    simp only [correction,foldCodes_work,collect_value,List.length_map,List.length_finRange]
    omega
  unfold rowCode
  dsimp only
  split_ifs <;> dsimp only
  · have h := hc (mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y)
    rw [delta_work]
    unfold codeBudget
    nlinarith
  · rw [delta_work]
    unfold codeBudget
    omega

/-- Node count of the actual source sum/product fold. -/
theorem nodes_fold (multiply : Bool) (xs : List (PolynomialCode ℚ)) :
    nodes (if multiply then PolynomialCode.product xs else PolynomialCode.sum xs)=
      (xs.map (fun p => nodes p+1)).sum+1 := by
  induction xs with
  | nil => cases multiply <;> rfl
  | cons a as ih =>
    cases multiply <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,PolynomialCode.product,PolynomialCode.sum,
        List.foldr_cons,nodes,List.map_cons,List.sum_cons] at * <;> omega

/-- Uniform AST size of the acquired basis: finite coordinates, not tensor dimension. -/
theorem basis_nodes (s : Finset (Fin Q)) (i : Fin Q) :
    nodes (basisCode (units Q) s i)≤6*Q+5 := by
  unfold basisCode
  simp only [nodes]
  have hn := nodes_fold true (List.ofFn (fun j : Fin Q =>
    if j∈s.erase i then PolynomialCode.mul (.constant ((units Q).differenceInverse i j))
      (.add .indeterminate (.constant (-node Q j))) else .constant 1))
  simp only [ite_true,List.map_ofFn,List.sum_ofFn,Function.comp_apply] at hn
  rw [hn]
  have hs : (∑ j : Fin Q, (nodes (if j∈s.erase i then
    PolynomialCode.mul (.constant ((units Q).differenceInverse i j))
      (.add .indeterminate (.constant (-node Q j))) else .constant 1)+1))≤Q*6 := by
    calc
      _ ≤ ∑ _j : Fin Q, 6 := Finset.sum_le_sum (by
        intro j _
        split_ifs <;> norm_num [nodes])
      _ = Q*6 := by simp
  omega

/-- The finite mismatch constructor has a quadratic-in-Q AST size. -/
theorem code_nodes (c : Fin R → ℤ) (u y : UniversalType r Q 1) :
    nodes (SemiprimeSourceInterpolationExecution.code c u 0 y)≤Q*(6*Q+8)+3 := by
  unfold SemiprimeSourceInterpolationExecution.code mismatchRowCode
  simp only [nodes]
  split_ifs
  · unfold correctionCode
    have hn := nodes_fold false (List.ofFn (fun i : Fin Q =>
      if i∈mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y then
        PolynomialCode.mul (.constant (SemiprimeSourceInterpolationExecution.prescription c u 0 y i))
          (basisCode (units Q) (mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y) i)
      else .constant 0))
    simp only [Bool.false_eq_true,ite_false,List.map_ofFn,List.sum_ofFn,Function.comp_apply] at hn
    rw [hn]
    have hs : (∑ i : Fin Q, (nodes (if i∈mismatchPositions
      (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y then
        PolynomialCode.mul (.constant (SemiprimeSourceInterpolationExecution.prescription c u 0 y i))
          (basisCode (units Q) (mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y) i)
      else .constant 0)+1))≤Q*(6*Q+8) := by
      calc
        _ ≤ ∑ _i : Fin Q, (6*Q+8) := Finset.sum_le_sum (by
          intro i _
          have hb := basis_nodes (mismatchPositions (fun v : UniversalType r Q 1 => v.head) (u.slot 0) y) i
          split_ifs <;> simp only [nodes] <;> omega)
        _ = Q*(6*Q+8) := by simp
    omega
  · simp only [nodes]
    omega

/-- Compile the acquired expression once, paying generation, arithmetic, reads and array cells. -/
def row (c : Fin R → ℤ) (u y : UniversalType r Q 1) : Run (Array ℚ) :=
  let generated := rowCode c u y
  let compiled := SemiprimeSourceCodeArrays.compile (R+1) generated.value
  ⟨compiled.coefficients,generated.work+compiled.arithmetic+compiled.reads+
    nodes generated.value*(R+2)⟩

/-- The new paid source row returns the exact previous acquired array. -/
theorem row_value (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (u y : UniversalType r Q 1) :
    (row c u y).value=(SemiprimeSourceInterpolationExecution.row c u 0 y).coefficients := by
  simp only [row,rowCode_value A c hc,SemiprimeSourceInterpolationExecution.row]

/-- Full scalar/control row-generation-and-compilation budget. -/
def rowBudget (Q R : ℕ) : ℕ := codeBudget Q R+
  (Q*(6*Q+8)+3)*(2*((R+1)*(R+2))+3*(R+1)+(R+2))

theorem row_work (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R)
    (u y : UniversalType r Q 1) : (row c u y).work≤rowBudget Q R := by
  have hg := rowCode_work c u y
  have hn := code_nodes c u y
  have ha := compile_arithmetic (R+1) (rowCode c u y).value
  have hr := compile_reads (R+1) (rowCode c u y).value
  have he := rowCode_value A c hc u y
  rw [he] at ha hr
  have hm := Nat.mul_le_mul_right (2*((R+1)*(R+2))+3*(R+1)+(R+2)) hn
  unfold row rowBudget
  dsimp only
  rw [he]
  nlinarith

/-- Non-numerator part of the actual full row budget, a literal polynomial. -/
def rowAuxiliary (Q R : ℕ) : ℕ :=
  Q*(2*R+12+Q*(Q+14)+2*Q+21)+7*Q+(Q+1)*(Q+1)+9+
  (Q*(6*Q+8)+3)*(2*((R+1)*(R+2))+3*(R+1)+(R+2))

/-- A literal polynomial coefficient for the native universal-alphabet bound. -/
def rowPolynomial (Q R : ℕ) : ℕ := Q*entryPolynomial Q R+rowAuxiliary Q R

theorem rowBudget_polynomial (Q R D : ℕ) (hD : 2^(2*Q)≤D) :
    rowBudget Q R≤D*rowPolynomial Q R := by
  have he := entryBudget_polynomial Q R D hD
  have hone : 1≤D := (Nat.one_le_pow _ _ (by decide : 1≤2)).trans hD
  have hm := Nat.mul_le_mul_left Q he
  have ha := Nat.mul_le_mul_right (rowAuxiliary Q R) hone
  calc
    rowBudget Q R = Q*entryBudget Q R+rowAuxiliary Q R := by
      unfold rowBudget codeBudget prescriptionBudget rowAuxiliary
      ring
    _ ≤ Q*(D*entryPolynomial Q R)+D*rowAuxiliary Q R := by omega
    _ = D*rowPolynomial Q R := by unfold rowPolynomial; ring

/-- Materialize the entire universal coefficient family, acquiring parity exactly once. -/
def acquire (A R : ℕ) (words : List (UniversalType r Q 1)) : Run (List (List (Array ℚ))) :=
  let parity := SemiprimeBinomialExecutionTracked.acquireParity A R
  let c := fun j : Fin R => SemiprimeBinomialExecution.coeff parity.coefficients j.rev.val
  let rows := collect (fun u => collect (row c u) words) words
  ⟨rows.value,rows.work+parity.arithmetic+parity.reads+1⟩

/-- All acquired arrays are the same original universal arrays; none is requested as input. -/
theorem acquire_value (A R : ℕ) (words : List (UniversalType r Q 1)) :
    (acquire A R words).value=words.map (fun u => words.map (fun y =>
      (SemiprimeUniversalSourceExecution.universalRow A R u y).coefficients)) := by
  unfold acquire
  simp only [collect_value]
  apply List.map_congr_left
  intro u _
  apply List.map_congr_left
  intro y _
  change (row (SemiprimeBinomialExecutionTracked.acquiredParity A R) u y).value=_
  rw [row_value A _ (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R)]
  unfold SemiprimeUniversalSourceExecution.universalRow
  congr 2
  exact (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R).trans
    (SemiprimeBinomialExecution.parity_eq A R).symm

/-- Full universal array-family generation budget, with two materialized finite dimensions. -/
def acquireBudget (A R Q D : ℕ) : ℕ :=
  D*(D*(rowBudget Q R+2)+3)+1+(A*(R+1)+A+R+R^2)+(2*A*(R+1)+R^2)+1

theorem acquire_work (A R : ℕ) (words : List (UniversalType r Q 1)) :
    (acquire A R words).work≤acquireBudget A R Q words.length := by
  let parity := SemiprimeBinomialExecutionTracked.acquireParity A R
  let c := fun j : Fin R => SemiprimeBinomialExecution.coeff parity.coefficients j.rev.val
  have hc : c=BinomialInterpolation.parityCoefficients (K:=ℤ) A R :=
    SemiprimeBinomialExecutionTracked.acquiredParity_eq A R
  have inner (u : UniversalType r Q 1) :
      (collect (row c u) words).work≤words.length*(rowBudget Q R+2)+1 :=
    collect_work _ _ _ (fun y _ => row_work A c hc u y)
  have outer := collect_work (fun u => collect (row c u) words) words
    (words.length*(rowBudget Q R+2)+1) (fun u _ => inner u)
  have hp := SemiprimeBinomialExecutionTracked.acquireParity_work A R
  unfold acquire
  dsimp only
  rw [hp.1,hp.2]
  unfold acquireBudget
  have he : words.length*(words.length*(rowBudget Q R+2)+1+2)=
      words.length*(words.length*(rowBudget Q R+2)+3) := by ring
  rw [he] at outer
  dsimp only [c,parity] at outer
  omega

end RiemannGaussian.SemiprimeMaterializedSourceRows
