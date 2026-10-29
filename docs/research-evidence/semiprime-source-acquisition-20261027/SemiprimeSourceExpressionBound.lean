/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayAcquisition

/-! # Polynomial work of the actual source coefficient-array interpreter
These bounds charge interpreting the acquired source expression. Acquiring its
integer constants, packing and finite sets is a separate preprocessing phase.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceExpressionBound
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SubexpRowInterpolation SemiprimeSourceCodeArrays

/-- Summation syntax contains one final zero leaf and one addition per entry. -/
theorem nodes_sum (ps : List (PolynomialCode ℚ)) :
    nodes (PolynomialCode.sum ps)=1+(ps.map nodes).sum+ps.length := by
  induction ps with
  | nil => simp [PolynomialCode.sum,nodes]
  | cons p ps ih =>
    simp only [PolynomialCode.sum,List.foldr_cons,nodes] at ih ⊢
    rw [ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Product syntax contains one final unit leaf and one multiplication per entry. -/
theorem nodes_product (ps : List (PolynomialCode ℚ)) :
    nodes (PolynomialCode.product ps)=1+(ps.map nodes).sum+ps.length := by
  induction ps with
  | nil => simp [PolynomialCode.product,nodes]
  | cons p ps ih =>
    simp only [PolynomialCode.product,List.foldr_cons,nodes] at ih ⊢
    rw [ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- The actual fixed-length syntax list has its expected linear node budget. -/
theorem nodes_list_bound (Q B : ℕ) (f : Fin Q → PolynomialCode ℚ)
    (h : ∀ i, nodes (f i)≤B) :
    ((List.ofFn f).map nodes).sum≤Q*B := by
  rw [List.map_ofFn,List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin Q, B := Finset.sum_le_sum (fun i _ => h i)
    _ = Q*B := by simp

/-- One Lagrange basis uses at most six nodes per interpolation position. -/
theorem basis_nodes {Q : ℕ} {node : Fin Q → ℚ} (u : NodeUnits node)
    (s : Finset (Fin Q)) (i : Fin Q) : nodes (basisCode u s i)≤6*Q+5 := by
  let f := fun j : Fin Q => if j ∈ s.erase i then
    PolynomialCode.mul (PolynomialCode.constant (u.differenceInverse i j))
      (.add .indeterminate (.constant (-node j))) else .constant 1
  have hf : ∀ j, nodes (f j)≤5 := by
    intro j
    dsimp only [f]
    split_ifs <;> norm_num [nodes]
  have h := nodes_list_bound Q 5 f hf
  change nodes (.mul (.mul (.constant (u.nodeInverse i)) .indeterminate)
    (PolynomialCode.product (List.ofFn f)))≤_
  simp only [nodes,nodes_product,List.length_ofFn]
  omega

/-- The actual correction expression has a quadratic node budget in Q. -/
theorem correction_nodes {Q : ℕ} {node : Fin Q → ℚ} (u : NodeUnits node)
    (s : Finset (Fin Q)) (d : Fin Q → ℚ) :
    nodes (correctionCode u s d)≤6*Q^2+8*Q+1 := by
  let f := fun i : Fin Q => if i ∈ s then
    PolynomialCode.mul (.constant (d i)) (basisCode u s i) else .constant 0
  have hf : ∀ i, nodes (f i)≤6*Q+7 := by
    intro i
    dsimp only [f]
    split_ifs
    · have h := basis_nodes u s i
      simp only [nodes]
      omega
    · simp only [nodes]
      omega
  have h := nodes_list_bound Q (6*Q+7) f hf
  change nodes (PolynomialCode.sum (List.ofFn f))≤_
  rw [nodes_sum,List.length_ofFn]
  nlinarith

/-- Complete source interpolation, including the selector and mismatch branch. -/
theorem mismatch_nodes {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    {Q : ℕ} {node : Fin Q → ℚ} (v : V) (head : V → Fin Q → C)
    (σ : Fin Q → C) (R : ℕ) (u : NodeUnits node) (d : V → Fin Q → ℚ) (y : V) :
    nodes (mismatchRowCode v head σ R u d y)≤6*Q^2+8*Q+3 := by
  unfold mismatchRowCode
  simp only [nodes]
  split_ifs
  · have h := correction_nodes u (mismatchPositions head σ y) (d y)
    omega
  · simp only [nodes]
    omega

/-- Actual universal-array arithmetic/read budget, excluding expression acquisition. -/
theorem universal_array_work {r Q : ℕ} (R : ℕ)
    (a y : MulticolorTypes.UniversalType r Q 1) :
    (SemiprimeSourceArrayAcquisition.universal R a y).work≤
      (6*Q^2+8*Q+3)*(2*(R+1)*(R+2)+3*(R+1)) := by
  let c := SemiprimeBinomialExecution.parity (Subexp.TailInterval.intervalStart r Q R) R
  let p := SemiprimeSourceInterpolationExecution.code c a 0 y
  have hn : nodes p≤6*Q^2+8*Q+3 := mismatch_nodes a (fun v => v.head) (a.slot 0) R
    (SemiprimeSourceInterpolationExecution.units Q)
    (SemiprimeSourceInterpolationExecution.prescription c a 0) y
  have ha := compile_arithmetic (R+1) p
  have hr := compile_reads (R+1) p
  change (compile (R+1) p).arithmetic+(compile (R+1) p).reads+0≤_
  have hmul := Nat.mul_le_mul_right (2*(R+1)*(R+2)+3*(R+1)) hn
  nlinarith

/-- The original-variable array interpreter has a polynomial budget, with the
actual universal-expression budget substituted rather than supplied as advice.
Integer constant, word, packing and address acquisition are separate costs. -/
theorem source_array_work {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (ε : ℚ) (R : ℕ)
    (i : I) (v : Fin n) :
    (SemiprimeSourceArrayAcquisition.row owner factor en ε R i v).work≤
      (R+2)+en.incidences.values.length*
        ((6*Q^2+8*Q+3)*(2*(R+1)*(R+2)+3*(R+1))+2*(R+2)+(4*(R+1)+1)) :=
  SemiprimeBlockArrayExecution.sourceRow_work
    (SemiprimeFiniteEnumerations.searchPacking owner factor en ε) owner (R+1)
    ((6*Q^2+8*Q+3)*(2*(R+1)*(R+2)+3*(R+1)))
    (SemiprimeSourceArrayAcquisition.universal R) (universal_array_work R) i v

end RiemannGaussian.SemiprimeSourceExpressionBound
