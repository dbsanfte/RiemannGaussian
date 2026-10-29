/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCodeArrayHeight
import RiemannGaussian.SemiprimeSourceUniversalHeight

/-! # Original-dimension heights of actual source interpolation syntax
Integer nodes, integer-difference inverses and executed universal prescriptions
supply the leaf bounds. All subtree arrays share one original full-tree cap;
no final row cancellation or supplied intermediate value is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeSourceInterpolationHeight
open scoped BigOperators
open Polynomial
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SubexpRowInterpolation
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeLocalExecutionHeight
open SemiprimeSourceCodeArrays SemiprimeSourceCodeArrayHeight SemiprimeSourceInterpolationExecution
open SemiprimeHermiteArrayHeight

/-- One positive original denominator clears ALL actual source constants. -/
def leafDenominator (Q R : ℕ) : ℕ := 2^(R-1)*Q.factorial
/-- Literal source constant numerator bound from the acquired parity execution. -/
def leafNumerator (A Q R : ℕ) : ℕ :=
  leafDenominator Q R*(Q+2^SemiprimeSourceUniversalHeight.entryExponent A Q R+1)
/-- Proved actual source expression node cap. -/
def nodeCap (Q : ℕ) : ℕ := 6*Q^2+8*Q+3
/-- One denominator shared by every original source interpolation subtree. -/
def denominator (Q R : ℕ) : ℕ := leafDenominator Q R^nodeCap Q
/-- One common original numerator envelope, including literal leftover units. -/
def numerator (A Q R : ℕ) : ℕ :=
  base (R+1) (leafDenominator Q R) (leafNumerator A Q R)^nodeCap Q

/-- The leaf denominator is positive even at Q=0 or R=0. -/
theorem leafDenominator_positive (Q R : ℕ) : 0<leafDenominator Q R :=
  Nat.mul_pos (by positivity) (Nat.factorial_pos Q)
/-- Literal units fit the original numerator bound. -/
theorem leafDenominator_le_numerator (A Q R : ℕ) : leafDenominator Q R ≤ leafNumerator A Q R := by
  unfold leafNumerator
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (leafDenominator Q R)
    (Nat.succ_le_succ (Nat.zero_le _))
/-- The common full-tree denominator is positive. -/
theorem denominator_positive (Q R : ℕ) : 0<denominator Q R := pow_pos (leafDenominator_positive Q R) _
/-- A common original representation for leftover source-row literals. -/
theorem denominator_le_numerator (A Q R : ℕ) : denominator Q R ≤ numerator A Q R :=
  Nat.pow_le_pow_left (base_guards (R+1) (leafDenominator Q R) (leafNumerator A Q R)).1 _

/-- A factorial-cleared constant is promoted to the shared power-two denominator. -/
theorem lift_factorial {q : ℚ} (Q R C : ℕ) (hq : Representation q Q.factorial C) :
    Representation q (leafDenominator Q R) (2^(R-1)*C) := by
  have h := representation_mul hq (representation_one (2^(R-1)) (by positivity))
  simpa only [mul_one,leafDenominator,Nat.mul_comm] using h

/-- Every actual node inverse is bounded directly from its ORIGINAL integer node. -/
theorem nodeInverse_representation (A Q R : ℕ) (t : Fin Q) :
    Representation ((units Q).nodeInverse t) (leafDenominator Q R) (leafNumerator A Q R) := by
  have h := representation_of_clears_abs (Nat.factorial_pos Q)
    (SemiprimeSourceRowHeight.sample_node_clears Q t)
    (SemiprimeSourceRowHeight.sample_node_inverse_abs Q t)
  have h' : Representation ((units Q).nodeInverse t) Q.factorial Q.factorial := by
    have he : (units Q).nodeInverse t=(((t.val+1:ℕ):ℚ))⁻¹ := by
      simp [units,NodeUnits.nodeInverse,NodeUnits.ofField,node]
    rw [he]
    rw [SemiprimeSourceRowHeight.sample_node_inverse] at h
    simpa only [Nat.mul_one] using h
  exact representation_mono (lift_factorial Q R Q.factorial h') (leafDenominator_le_numerator A Q R)

/-- Difference-inverse constants are used only for unequal integer nodes. -/
theorem differenceInverse_representation (A Q R : ℕ) (i j : Fin Q) (hij : i≠j) :
    Representation ((units Q).differenceInverse i j) (leafDenominator Q R) (leafNumerator A Q R) := by
  have h := representation_of_clears_abs (Nat.factorial_pos Q)
    (SemiprimeSourceRowHeight.sample_difference_clears Q i j hij)
    (SemiprimeSourceRowHeight.sample_difference_inverse_abs Q i j hij)
  have h' : Representation ((units Q).differenceInverse i j) Q.factorial Q.factorial := by
    have he : (units Q).differenceInverse i j=(((i.val:ℤ)-j.val:ℤ):ℚ)⁻¹ := by
      simp only [units,NodeUnits.differenceInverse,NodeUnits.ofField,ne_eq,hij,not_false_eq_true,
        dite_true,node,Int.cast_sub,Int.cast_natCast,Units.val_inv_eq_inv_val,Units.val_mk0]
      congr 1
      ring
    rw [he]
    rw [SemiprimeSourceRowHeight.sample_difference_inverse Q i j hij] at h
    simpa only [Nat.mul_one] using h
  exact representation_mono (lift_factorial Q R Q.factorial h') (leafDenominator_le_numerator A Q R)

/-- Negated node constants have original magnitude at most Q. -/
theorem negativeNode_representation (A Q R : ℕ) (t : Fin Q) :
    Representation (-node Q t) (leafDenominator Q R) (leafNumerator A Q R) := by
  have h := representation_integer_mul (representation_one (leafDenominator Q R)
    (leafDenominator_positive Q R)) (-((t.val+1:ℕ):ℤ)) (show (-((t.val+1:ℕ):ℤ)).natAbs ≤ Q by
      simp only [Int.natAbs_neg,Int.natAbs_natCast];omega)
  have h' : Representation (-node Q t) (leafDenominator Q R) (leafDenominator Q R*Q) := by
    simpa only [one_mul,node,Int.cast_neg,Int.cast_natCast,Int.cast_add,Int.cast_one,Nat.cast_add,Nat.cast_one] using h
  apply representation_mono h'
  unfold leafNumerator
  exact Nat.mul_le_mul_left _ (by
    simpa only [Nat.add_assoc] using Nat.le_add_right Q
      (2^SemiprimeSourceUniversalHeight.entryExponent A Q R+1))

/-- The acquired integer numerator gives the actual prescription representation. -/
theorem prescription_representation {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) (t : Fin Q) :
    Representation (prescription (SemiprimeBinomialExecution.parity A R) a 0 y t)
      (leafDenominator Q R) (leafNumerator A Q R) := by
  let z := SemiprimeUniversalNumeratorExecution.extended (SemiprimeBinomialExecution.parity A R)
    (0:Fin 1) t (y.head t) a y
  have hz := SemiprimeSourceUniversalHeight.extended_parity_abs A R t (y.head t) a y
  have hz' : z.natAbs ≤ 2^SemiprimeSourceUniversalHeight.entryExponent A Q R := by
    have h : (z.natAbs:ℤ) ≤ (2^SemiprimeSourceUniversalHeight.entryExponent A Q R:ℕ) := by
      simpa only [Int.natCast_natAbs] using hz
    exact_mod_cast h
  have hr : Representation ((-(z:ℚ))/((2^(R-1):ℕ):ℚ)) (2^(R-1))
      (2^SemiprimeSourceUniversalHeight.entryExponent A Q R) :=
    ⟨-z,by simp,by simpa only [Int.natAbs_neg] using hz'⟩
  have hm := representation_mul hr (representation_one Q.factorial (Nat.factorial_pos Q))
  have he : prescription (SemiprimeBinomialExecution.parity A R) a 0 y t=
      (-(z:ℚ))/((2^(R-1):ℕ):ℚ) := by
    simp only [prescription,SemiprimeSourceInterpolationExecution.denominator,Units.val_inv_eq_inv_val,
      Units.val_mk0,neg_mul,inv_mul_eq_div,Nat.cast_pow,Nat.cast_ofNat,z,neg_div]
  rw [← he,mul_one] at hm
  apply representation_mono hm
  unfold leafNumerator leafDenominator
  have hp : 1 ≤ 2^(R-1) := Nat.one_le_two_pow
  calc
    2^SemiprimeSourceUniversalHeight.entryExponent A Q R*Q.factorial ≤
        (Q+2^SemiprimeSourceUniversalHeight.entryExponent A Q R+1)*Q.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2^(R-1)*((Q+2^SemiprimeSourceUniversalHeight.entryExponent A Q R+1)*Q.factorial) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ hp
    _ = _ := by ring

/-- Original bounds extend through the literal finite sum syntax. -/
theorem leaves_sum (d B : ℕ) (ps : List (PolynomialCode ℚ))
    (hp : ∀ p∈ps,Leaves d B p) : Leaves d B (PolynomialCode.sum ps) := by
  induction ps with
  | nil => exact representation_mono (representation_zero d) (Nat.zero_le _)
  | cons p ps ih => exact ⟨hp p List.mem_cons_self,ih (fun q hq => hp q (List.mem_cons_of_mem p hq))⟩

/-- Original bounds extend through literal finite product syntax. -/
theorem leaves_product (d B : ℕ) (hd : 0<d) (hdB : d ≤ B) (ps : List (PolynomialCode ℚ))
    (hp : ∀ p∈ps,Leaves d B p) : Leaves d B (PolynomialCode.product ps) := by
  induction ps with
  | nil => exact representation_mono (representation_one d hd) hdB
  | cons p ps ih => exact ⟨hp p List.mem_cons_self,ih (fun q hq => hp q (List.mem_cons_of_mem p hq))⟩

/-- The literal actual Lagrange basis contains only the derived original constants. -/
theorem basis_leaves (A Q R : ℕ) (s : Finset (Fin Q)) (i : Fin Q) :
    Leaves (leafDenominator Q R) (leafNumerator A Q R) (basisCode (units Q) s i) := by
  refine ⟨⟨nodeInverse_representation A Q R i,trivial⟩,?_⟩
  apply leaves_product _ _ (leafDenominator_positive Q R) (leafDenominator_le_numerator A Q R)
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  split_ifs with hj
  · exact ⟨differenceInverse_representation A Q R i j (Finset.ne_of_mem_erase hj).symm,
      ⟨trivial,negativeNode_representation A Q R j⟩⟩
  · exact representation_mono (representation_one _ (leafDenominator_positive Q R))
      (leafDenominator_le_numerator A Q R)

/-- All ACTUAL interpolation leaves are derived from parity and original integer samples. -/
theorem code_leaves {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    Leaves (leafDenominator Q R) (leafNumerator A Q R)
      (code (SemiprimeBinomialExecution.parity A R) a 0 y) := by
  unfold code mismatchRowCode
  constructor
  · by_cases h : y=a
    · simpa only [h,Pi.single_eq_same,Leaves] using representation_mono
        (representation_one _ (leafDenominator_positive Q R)) (leafDenominator_le_numerator A Q R)
    · simpa only [Pi.single_eq_of_ne h,Leaves] using representation_mono (representation_zero _) (Nat.zero_le (leafNumerator A Q R))
  · split_ifs
    · apply leaves_sum
      intro p hp
      obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
      split_ifs
      · exact ⟨prescription_representation A R a y t,basis_leaves A Q R _ t⟩
      · exact representation_mono (representation_zero _) (Nat.zero_le _)
    · exact representation_mono (representation_zero _) (Nat.zero_le _)

/-- Actual source syntax has the original quadratic node cap. -/
theorem code_nodes {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    nodes (code (SemiprimeBinomialExecution.parity A R) a 0 y) ≤ nodeCap Q :=
  SemiprimeSourceExpressionBound.mismatch_nodes a (fun v => v.head) (a.slot 0) R (units Q)
    (prescription (SemiprimeBinomialExecution.parity A R) a 0) y

/-- The actual acquired universal coefficient array has one common original-data bound. -/
theorem universalRow_bound {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    ArrayBound (SemiprimeUniversalSourceExecution.universalRow A R a y).coefficients (R+1)
      (denominator Q R) (numerator A Q R) :=
  subtree_representation (R+1) (leafDenominator Q R) (leafNumerator A Q R) (nodeCap Q)
    (leafDenominator_positive Q R) _ _ (code_leaves A R a y) (code_nodes A R a y) (.refl _)

/-- The literal centered source array caller is included without coefficient advice. -/
theorem source_universal_bound {r Q : ℕ} (R : ℕ) (a y : UniversalType r Q 1) :
    ArrayBound (SemiprimeSourceArrayAcquisition.universal R a y).jet.coefficients (R+1)
      (denominator Q R) (numerator (Subexp.TailInterval.intervalStart r Q R) Q R) :=
  universalRow_bound _ R a y

/-- Every actual syntax subtree, not merely the completed universal row, has the original cap. -/
theorem code_subtree_bound {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p : PolynomialCode ℚ) (hp : Subcode p (code (SemiprimeBinomialExecution.parity A R) a 0 y)) :
    ArrayBound (compile (R+1) p).coefficients (R+1) (denominator Q R) (numerator A Q R) :=
  subtree_representation (R+1) (leafDenominator Q R) (leafNumerator A Q R) (nodeCap Q)
    (leafDenominator_positive Q R) _ p (code_leaves A R a y) (code_nodes A R a y) hp

/-- Every original-source convolution slice, including arbitrary prefixes/suffixes, is covered. -/
theorem code_convolution_slice_bound {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p q : PolynomialCode ℚ) (hpq : Subcode (.mul p q)
      (code (SemiprimeBinomialExecution.parity A R) a 0 y))
    (n start len : ℕ) (hn : n<R+1) (hlen : start+len ≤ n+1) :
    Representation (∑ i∈Finset.range len,
      coefficient (compile (R+1) p).coefficients (start+i)*
        coefficient (compile (R+1) q).coefficients (n-(start+i)))
      (denominator Q R) (numerator A Q R) :=
  subtree_convolution_slice (R+1) (leafDenominator Q R) (leafNumerator A Q R) (nodeCap Q)
    (leafDenominator_positive Q R) _ p q (code_leaves A R a y) (code_nodes A R a y)
    hpq n start len hn hlen

/-- Every cached ascending prefix ARRAY in source multiplication has the original cap. -/
theorem code_multiply_prefix_bound {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p q : PolynomialCode ℚ) (hpq : Subcode (.mul p q)
      (code (SemiprimeBinomialExecution.parity A R) a 0 y)) (k : ℕ) (hk : k ≤ R+1) :
    ArrayBound (multiply (compile (R+1) p).coefficients (compile (R+1) q).coefficients k).coefficients
      k (denominator Q R) (numerator A Q R) :=
  subtree_multiply_prefix (R+1) (leafDenominator Q R) (leafNumerator A Q R) (nodeCap Q)
    (leafDenominator_positive Q R) _ p q (code_leaves A R a y) (code_nodes A R a y) hpq k hk

/-- Every actually executed source dot-prefix frame has the SAME original denominator. -/
theorem code_dotPrefix_bound {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p q : PolynomialCode ℚ) (hpq : Subcode (.mul p q)
      (code (SemiprimeBinomialExecution.parity A R) a 0 y))
    (n len : ℕ) (hn : n<R+1) (hlen : len ≤ n) :
    Representation (dotPrefix (compile (R+1) p).coefficients
      (compile (R+1) q).coefficients (n-1) len).value (denominator Q R) (numerator A Q R) := by
  have hs := subcode_leaves (leafDenominator Q R) (leafNumerator A Q R) hpq (code_leaves A R a y)
  have h := compile_dotPrefix_representation (R+1) (leafDenominator Q R) (leafNumerator A Q R)
    (leafDenominator_positive Q R) p q hs.1 hs.2 n len hn hlen
  exact representation_power_extend (leafDenominator Q R)
    (base (R+1) (leafDenominator Q R) (leafNumerator A Q R)) _ (nodeCap Q)
    (leafDenominator_positive Q R) (base_guards _ _ _).1
    ((subcode_nodes hpq).trans (code_nodes A R a y)) h

end RiemannGaussian.SemiprimeSourceInterpolationHeight
