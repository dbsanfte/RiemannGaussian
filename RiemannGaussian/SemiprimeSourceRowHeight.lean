/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceLayoutHeight
import Mathlib

/-!
# Exact common denominators of the native source polynomial rows

These statements concern the actual rational polynomial rows, rather than the
integer matrices used to certify their kernels.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeSourceRowHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpRowInterpolation
open RiemannGaussian.SemiprimeSourceLayout
attribute [local instance] Classical.propDecidable

/-- Integer polynomials inside rational polynomials, without coefficient choices. -/
def integerPolynomials : Subring (Polynomial ℚ) :=
  (Polynomial.mapRingHom (Int.castRingHom ℚ)).range

/-- The specified integer clears every coefficient of the literal polynomial. -/
def Clears (d : ℕ) (p : Polynomial ℚ) : Prop :=
  Polynomial.C (d : ℚ) * p ∈ integerPolynomials

theorem integer_C (z : ℤ) : Polynomial.C (z : ℚ) ∈ integerPolynomials := by
  exact ⟨Polynomial.C z, by simp⟩

theorem integer_X : (Polynomial.X : Polynomial ℚ) ∈ integerPolynomials := by
  exact ⟨Polynomial.X, by simp⟩

theorem clears_of_integer (d : ℕ) {p : Polynomial ℚ} (hp : p ∈ integerPolynomials) :
    Clears d p :=
  integerPolynomials.mul_mem (integer_C d) hp

theorem clears_zero (d : ℕ) : Clears d 0 := by
  exact clears_of_integer d integerPolynomials.zero_mem

theorem clears_add {d : ℕ} {p q : Polynomial ℚ} (hp : Clears d p) (hq : Clears d q) :
    Clears d (p + q) := by
  simpa only [Clears, mul_add] using integerPolynomials.add_mem hp hq

theorem clears_neg {d : ℕ} {p : Polynomial ℚ} (hp : Clears d p) : Clears d (-p) := by
  simpa only [Clears, mul_neg] using integerPolynomials.neg_mem hp

theorem clears_mul {d e : ℕ} {p q : Polynomial ℚ} (hp : Clears d p) (hq : Clears e q) :
    Clears (d * e) (p * q) := by
  have h := integerPolynomials.mul_mem hp hq
  change Polynomial.C ((d * e : ℕ) : ℚ) * (p * q) ∈ integerPolynomials
  convert h using 1
  simp only [Nat.cast_mul, Polynomial.C_mul]
  ring

theorem clears_of_dvd {d e : ℕ} {p : Polynomial ℚ} (hp : Clears d p) (hde : d ∣ e) :
    Clears e p := by
  obtain ⟨k, rfl⟩ := hde
  have h := integerPolynomials.mul_mem (integer_C k) hp
  change Polynomial.C ((d * k : ℕ) : ℚ) * p ∈ integerPolynomials
  convert h using 1
  simp only [Nat.cast_mul, Polynomial.C_mul, Int.cast_natCast]
  ring

theorem clears_sum {I : Type*} (s : Finset I) (d : ℕ) (p : I → Polynomial ℚ)
    (hp : ∀ i ∈ s, Clears d (p i)) : Clears d (∑ i ∈ s, p i) := by
  unfold Clears
  rw [Finset.mul_sum]
  exact integerPolynomials.sum_mem hp

theorem clears_prod {I : Type*} (s : Finset I) (d : ℕ) (p : I → Polynomial ℚ)
    (hp : ∀ i ∈ s, Clears d (p i)) : Clears (d ^ s.card) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clears_of_integer 1 integerPolynomials.one_mem
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, Finset.prod_insert hi, pow_succ']
    exact clears_mul (hp i (Finset.mem_insert_self i s))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem clears_inverse {d : ℕ} {k : ℤ} (hk : k ≠ 0) (hkd : k ∣ (d : ℤ)) :
    Clears d (Polynomial.C (k : ℚ)⁻¹) := by
  obtain ⟨z, hz⟩ := hkd
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have he : (d : ℚ) * (k : ℚ)⁻¹ = (z : ℚ) := by
    have hzq : (d : ℚ) = (k : ℚ) * (z : ℚ) := by exact_mod_cast hz
    rw [hzq]
    field_simp
  unfold Clears
  rw [← Polynomial.C_mul, he]
  exact integer_C z

theorem factorial_dvd_inverse {Q : ℕ} {k : ℤ} (hk : k ≠ 0) (hbound : k.natAbs ≤ Q) :
    Clears Q.factorial (Polynomial.C (k : ℚ)⁻¹) := by
  apply clears_inverse hk
  apply Int.natAbs_dvd.mp
  apply Int.natCast_dvd.mpr
  simpa only [Int.natAbs_natCast] using Nat.dvd_factorial (Int.natAbs_pos.mpr hk) hbound

theorem sample_node_inverse (Q : ℕ) (i : Fin Q) :
    (sampleUnits Q).nodeInverse i = ((i.val + 1 : ℕ) : ℚ)⁻¹ := by
  simp [sampleUnits, NodeUnits.nodeInverse, NodeUnits.ofField, sampleNode]

theorem sample_difference_inverse (Q : ℕ) (i j : Fin Q) (hij : i ≠ j) :
    (sampleUnits Q).differenceInverse i j = (((i.val : ℤ) - j.val : ℤ) : ℚ)⁻¹ := by
  simp [sampleUnits, NodeUnits.differenceInverse, NodeUnits.ofField, sampleNode, hij]

theorem sample_node_clears (Q : ℕ) (i : Fin Q) :
    Clears Q.factorial (Polynomial.C ((sampleUnits Q).nodeInverse i)) := by
  rw [sample_node_inverse]
  have hbound : ((i.val + 1 : ℕ) : ℤ).natAbs ≤ Q := by
    rw [Int.natAbs_natCast]
    omega
  have h := factorial_dvd_inverse (Q := Q) (k := ((i.val + 1 : ℕ) : ℤ)) (by omega) hbound
  simpa only [Int.cast_natCast] using h

theorem sample_difference_clears (Q : ℕ) (i j : Fin Q) (hij : i ≠ j) :
    Clears Q.factorial (Polynomial.C ((sampleUnits Q).differenceInverse i j)) := by
  rw [sample_difference_inverse Q i j hij]
  apply factorial_dvd_inverse
  · intro he
    apply hij
    apply Fin.ext
    omega
  · have he : |((i.val : ℤ) - j.val)| ≤ (Q : ℤ) := abs_le.mpr (by
      have hi := i.isLt
      have hj := j.isLt
      constructor <;> omega)
    rw [← Int.natCast_natAbs] at he
    exact_mod_cast he

theorem sample_basisDivisor_clears (Q : ℕ) (i j : Fin Q) (hij : i ≠ j) :
    Clears Q.factorial (basisDivisor (sampleUnits Q) i j) := by
  have hp : (Polynomial.X - Polynomial.C (sampleNode Q j)) ∈ integerPolynomials := by
    have hc : Polynomial.C (sampleNode Q j) ∈ integerPolynomials := by
      simpa [sampleNode] using integer_C (j.val + 1)
    exact integerPolynomials.sub_mem integer_X hc
  have h := clears_mul (sample_difference_clears Q i j hij) (clears_of_integer 1 hp)
  simpa only [Nat.mul_one, basisDivisor] using h

theorem sample_basis_clears (Q : ℕ) (s : Finset (Fin Q)) (i : Fin Q) (hi : i ∈ s) :
    Clears (Q.factorial ^ (Q + 1)) (basis (sampleUnits Q) s i) := by
  have hfirst : Clears Q.factorial (Polynomial.C ((sampleUnits Q).nodeInverse i) * Polynomial.X) := by
    simpa only [Nat.mul_one] using
      clears_mul (sample_node_clears Q i) (clears_of_integer 1 integer_X)
  have hp := clears_prod (s.erase i) Q.factorial
    (fun j => basisDivisor (sampleUnits Q) i j) (by
      intro j hj
      exact sample_basisDivisor_clears Q i j (Finset.ne_of_mem_erase hj).symm)
  have hb := clears_mul hfirst hp
  have hc : 1 + (s.erase i).card = s.card := by
    simpa only [Nat.add_comm] using Finset.card_erase_add_one hi
  have hd : s.card ≤ Q := (Finset.card_le_univ s).trans_eq (by simp)
  have he : Q.factorial * Q.factorial ^ (s.erase i).card = Q.factorial ^ s.card := by
    rw [← pow_succ', show (s.erase i).card + 1 = s.card by omega]
  rw [he] at hb
  exact clears_of_dvd hb (pow_dvd_pow _ (by omega))

/-- One common denominator for the whole interpolation polynomial, not one per coefficient. -/
theorem sample_correction_clears {Q D : ℕ} (s : Finset (Fin Q)) (d : Fin Q → ℚ)
    (hd : ∀ i ∈ s, Clears D (Polynomial.C (d i))) :
    Clears (D * Q.factorial ^ (Q + 1)) (correctionPolynomial (sampleUnits Q) s d) := by
  apply clears_sum
  intro i hi
  exact clears_mul (hd i hi) (sample_basis_clears Q s i hi)

/-- Finite mismatch interpolation preserves the same common denominator. -/
theorem sample_mismatch_clears {Q D : ℕ} {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (d : V → Fin Q → ℚ) (hd : ∀ y i, Clears D (Polynomial.C (d y i))) (y : V) :
    Clears (D * Q.factorial ^ (Q + 1))
      (mismatchRowPath v head σ R (sampleUnits Q) d y) := by
  unfold mismatchRowPath rowPath
  apply clears_add
  · by_cases hy : y = v
    · subst y
      simpa only [Pi.single_eq_same, Polynomial.C_1] using
        clears_of_integer (D * Q.factorial ^ (Q + 1)) integerPolynomials.one_mem
    · simp only [Pi.single_eq_of_ne hy, Polynomial.C_0]
      exact clears_zero _
  · unfold mismatchCorrection columnCorrection
    split_ifs
    · exact sample_correction_clears _ _ (fun i _ => hd y i)
    · exact clears_zero _

/-- The actual spectral denominator, as a natural number. -/
def spectralDenominator (R : ℕ) : ℕ := 2 ^ (R - 1)

/-- A single public denominator clears every actual source polynomial row. -/
def rowDenominator (Q R : ℕ) : ℕ := spectralDenominator R * Q.factorial ^ (Q + 1)

theorem denominatorUnit_inverse (R : ℕ) :
    (↑((denominatorUnit R)⁻¹) : ℚ) = (spectralDenominator R : ℚ)⁻¹ := by
  simp [denominatorUnit, LayoutNumerator.denominator, spectralDenominator]

theorem spectral_coefficient_clears (R : ℕ) (z : ℤ) :
    Clears (spectralDenominator R)
      (Polynomial.C ((↑((denominatorUnit R)⁻¹) : ℚ) * (z : ℚ))) := by
  rw [denominatorUnit_inverse]
  have hi := clears_inverse (d := spectralDenominator R)
    (k := (spectralDenominator R : ℤ)) (by unfold spectralDenominator; positivity) (dvd_refl _)
  have hm := clears_mul hi (clears_of_integer 1 (integer_C z))
  simpa only [Nat.mul_one, Int.cast_natCast, Polynomial.C_mul] using hm

theorem sourceRow_clears {r Q Δ : ℕ} (N : LayoutScaledMatrices.Numerators r Q Δ)
    (a : MulticolorTypes.UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (y : MulticolorTypes.UniversalType r Q Δ) :
    Clears (rowDenominator Q R)
      (LayoutScaledMatrices.sourceRow N (denominatorUnit R) a i R (sampleUnits Q) y) := by
  unfold LayoutScaledMatrices.sourceRow SubexpAnnihilation.rowForMatrices
  apply sample_mismatch_clears
  intro z t
  unfold SubexpAnnihilation.matrixPrescription SubexpAnnihilation.zeroExtendMatrix
  simp only [RingHom.id_apply]
  split_ifs
  · rw [LayoutScaledMatrices.unitScaled, Polynomial.C_neg]
    exact clears_neg (spectral_coefficient_clears R _)
  · simpa only [neg_zero, Polynomial.C_0] using clears_zero (spectralDenominator R)
  · simpa only [neg_zero, Polynomial.C_0] using clears_zero (spectralDenominator R)

theorem pullback_row_clears {I V : Type*} [Fintype I] [DecidableEq V]
    (owner : I → V) (a : I → Polynomial ℚ) (D : ℕ) (ha : ∀ i, Clears D (a i)) (v : V) :
    Clears D (LayoutPullback.row owner a v) := by
  apply clears_sum
  intro i _
  split_ifs
  · exact ha i
  · exact clears_zero D

theorem assembled_row_clears {U I : Type*} [Fintype U] [DecidableEq I] {label : I → U} {b : ℕ}
    (P : BlockPacking.CompleteBlocks label b) (rows : U → U → Polynomial ℚ)
    (D : ℕ) (hrows : ∀ u v, Clears D (rows u v)) (i v : I) :
    Clears D (LayoutBlocks.assembledRow P rows i v) := by
  by_cases hi : i ∈ Set.range P.embed
  · obtain ⟨⟨j,u⟩, rfl⟩ := hi
    rw [LayoutBlocks.assembledRow_apply]
    exact pullback_row_clears _ _ D (hrows u) v
  · rw [LayoutBlocks.assembledRow_outside P rows i hi]
    dsimp only
    split_ifs
    · simpa only [Polynomial.C_1] using clears_of_integer D integerPolynomials.one_mem
    · simpa only [Polynomial.C_0] using clears_zero D

/-- Every coefficient of every actual built row has this SAME public denominator. -/
theorem builtLayout_row_clears {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (i : I) (v : V) :
    Clears (rowDenominator Q R) ((builtLayout owner factor en ε R).row i v) := by
  let pack := searchedPacking owner factor en ε
  let C := universalLayout r Q R
  have hc : ∀ a y, Clears (rowDenominator Q R) (C.row a y) := by
    intro a y
    exact sourceRow_clears (LayoutNumerator.family r Q 1
      (Subexp.TailInterval.intervalStart r Q R) R) a 0 R y
  change Clears (rowDenominator Q R)
    (LayoutPullback.row owner (LayoutBlocks.assembledRow pack.completeBlocks C.row i) v)
  exact pullback_row_clears _ _ _ (assembled_row_clears pack.completeBlocks C.row _ hc i) v

/-- The denominator-cleared row is literally an integer polynomial. -/
theorem builtLayout_integer_polynomial {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (i : I) (v : V) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) = Polynomial.C (rowDenominator Q R : ℚ) *
        (builtLayout owner factor en ε R).row i v :=
  builtLayout_row_clears owner factor en ε R i v

/-- Uniform absolute bound on every rational coefficient, including the zero tail. -/
def CoeffBound (p : Polynomial ℚ) (B : ℚ) : Prop := ∀ k, |p.coeff k| ≤ B

theorem coeffBound_C {c B : ℚ} (hc : |c| ≤ B) (hB : 0 ≤ B) : CoeffBound (Polynomial.C c) B := by
  intro k
  cases k with
  | zero => simpa using hc
  | succ k => simpa using hB

theorem coeffBound_zero {B : ℚ} (hB : 0 ≤ B) : CoeffBound 0 B := by
  intro k
  simpa using hB

theorem coeffBound_add {p q : Polynomial ℚ} {A B : ℚ}
    (hp : CoeffBound p A) (hq : CoeffBound q B) : CoeffBound (p + q) (A + B) := by
  intro k
  exact (abs_add_le _ _).trans (add_le_add (hp k) (hq k))

theorem coeffBound_C_mul_unit {p : Polynomial ℚ} {a B : ℚ}
    (hp : CoeffBound p B) (ha : |a| ≤ 1) :
    CoeffBound (Polynomial.C a * p) B := by
  intro k
  rw [Polynomial.coeff_C_mul, abs_mul]
  calc
    _ ≤ 1 * B := mul_le_mul ha (hp k) (abs_nonneg _) (by norm_num)
    _ = B := one_mul _

theorem coeffBound_mul_X {p : Polynomial ℚ} {B : ℚ} (hp : CoeffBound p B) (hB : 0 ≤ B) :
    CoeffBound (p * Polynomial.X) B := by
  intro k
  cases k with
  | zero => simpa using hB
  | succ k => simpa using hp k

theorem coeffBound_mul_linear {p : Polynomial ℚ} {c B Q : ℚ}
    (hp : CoeffBound p B) (hc : |c| ≤ Q) (hB : 0 ≤ B) :
    CoeffBound (p * (Polynomial.X - Polynomial.C c)) (B * (Q + 1)) := by
  intro k
  rw [mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_C]
  cases k with
  | zero =>
    rw [Polynomial.coeff_mul_X_zero, zero_sub, abs_neg, abs_mul]
    have hm := mul_le_mul (hp 0) hc (abs_nonneg c) hB
    nlinarith
  | succ k =>
    rw [Polynomial.coeff_mul_X]
    calc
      _ ≤ |p.coeff k| + |p.coeff (k + 1) * c| := abs_sub _ _
      _ ≤ B + B * Q := by
        rw [abs_mul]
        exact add_le_add (hp k) (mul_le_mul (hp (k + 1)) hc (abs_nonneg c) hB)
      _ = _ := by ring

theorem coeffBound_normalized_product {I : Type*} (s : Finset I) (a c : I → ℚ)
    (Q : ℚ) (hQ : 0 ≤ Q) (ha : ∀ i ∈ s, |a i| ≤ 1) (hc : ∀ i ∈ s, |c i| ≤ Q) :
    CoeffBound (∏ i ∈ s, Polynomial.C (a i) * (Polynomial.X - Polynomial.C (c i)))
      ((Q + 1) ^ s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffBound_C (c := 1) (B := 1) (by norm_num) (by norm_num)
  | @insert i s hi ih =>
    have hp := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hl := coeffBound_mul_linear hp (hc i (Finset.mem_insert_self i s)) (by positivity)
    have hu := coeffBound_C_mul_unit hl (ha i (Finset.mem_insert_self i s))
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    convert hu using 1
    ring

theorem sample_node_inverse_abs (Q : ℕ) (i : Fin Q) :
    |(sampleUnits Q).nodeInverse i| ≤ 1 := by
  rw [sample_node_inverse, abs_inv]
  apply inv_le_one_of_one_le₀
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast (show 1 ≤ i.val + 1 by omega)

theorem sample_difference_inverse_abs (Q : ℕ) (i j : Fin Q) (hij : i ≠ j) :
    |(sampleUnits Q).differenceInverse i j| ≤ 1 := by
  rw [sample_difference_inverse Q i j hij, abs_inv]
  apply inv_le_one_of_one_le₀
  have hneq : (i.val : ℤ) - j.val ≠ 0 := by
    intro he
    apply hij
    apply Fin.ext
    omega
  exact_mod_cast Int.one_le_abs hneq

theorem sample_node_abs (Q : ℕ) (i : Fin Q) : |sampleNode Q i| ≤ (Q : ℚ) := by
  rw [abs_of_nonneg (by unfold sampleNode; positivity)]
  unfold sampleNode
  exact_mod_cast Nat.succ_le_of_lt i.isLt

theorem sample_basis_coeffBound (Q : ℕ) (s : Finset (Fin Q)) (i : Fin Q) :
    CoeffBound (basis (sampleUnits Q) s i) ((Q + 1 : ℚ) ^ Q) := by
  have hp := coeffBound_normalized_product (s.erase i)
    (fun j => (sampleUnits Q).differenceInverse i j) (sampleNode Q) (Q : ℚ)
    (by positivity) (fun j hj => sample_difference_inverse_abs Q i j (Finset.ne_of_mem_erase hj).symm)
    (fun j _ => sample_node_abs Q j)
  have hx := coeffBound_mul_X hp (by positivity)
  have hu := coeffBound_C_mul_unit hx (sample_node_inverse_abs Q i)
  have he : (Polynomial.C ((sampleUnits Q).nodeInverse i) * Polynomial.X) *
      ∏ j ∈ s.erase i, basisDivisor (sampleUnits Q) i j =
    Polynomial.C ((sampleUnits Q).nodeInverse i) *
      ((∏ j ∈ s.erase i, Polynomial.C ((sampleUnits Q).differenceInverse i j) *
        (Polynomial.X - Polynomial.C (sampleNode Q j))) * Polynomial.X) := by
    simp only [basisDivisor]
    ring
  have hc : (s.erase i).card ≤ Q :=
    (Finset.card_le_univ _).trans_eq (by simp)
  have hpow : (Q + 1 : ℚ) ^ (s.erase i).card ≤ (Q + 1 : ℚ) ^ Q :=
    pow_le_pow_right₀ (by have : (0 : ℚ) ≤ Q := Nat.cast_nonneg _; linarith) hc
  intro k
  unfold basis
  rw [he]
  exact (hu k).trans hpow

theorem coeffBound_C_mul {p : Polynomial ℚ} {a B W : ℚ}
    (hp : CoeffBound p B) (ha : |a| ≤ W) (hW : 0 ≤ W) :
    CoeffBound (Polynomial.C a * p) (W * B) := by
  intro k
  rw [Polynomial.coeff_C_mul, abs_mul]
  exact mul_le_mul ha (hp k) (abs_nonneg _) hW

theorem coeffBound_sum {I : Type*} (s : Finset I) (p : I → Polynomial ℚ) (B : ℚ)
    (hp : ∀ i ∈ s, CoeffBound (p i) B) :
    CoeffBound (∑ i ∈ s, p i) ((s.card : ℚ) * B) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ i ∈ s, |(p i).coeff k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i hi => hp i hi k)
    _ = _ := by simp

theorem sample_correction_coeffBound {Q : ℕ} (s : Finset (Fin Q)) (d : Fin Q → ℚ)
    (W : ℚ) (hW : 0 ≤ W) (hd : ∀ i ∈ s, |d i| ≤ W) :
    CoeffBound (correctionPolynomial (sampleUnits Q) s d)
      ((Q : ℚ) * W * (Q + 1 : ℚ) ^ Q) := by
  have hsum := coeffBound_sum s (fun i => Polynomial.C (d i) * basis (sampleUnits Q) s i)
    (W * (Q + 1 : ℚ) ^ Q) (fun i hi =>
      coeffBound_C_mul (sample_basis_coeffBound Q s i) (hd i hi) hW)
  have hcn : s.card ≤ Q := (Finset.card_le_univ s).trans_eq (by simp)
  have hc : (s.card : ℚ) ≤ Q := by exact_mod_cast hcn
  intro k
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ W * (Q + 1 : ℚ) ^ Q by positivity)
  exact (hsum k).trans (by nlinarith [hm])

theorem sample_mismatch_coeffBound {Q : ℕ} {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (d : V → Fin Q → ℚ) (W : ℚ) (hW : 0 ≤ W) (hd : ∀ y i, |d y i| ≤ W) (y : V) :
    CoeffBound (mismatchRowPath v head σ R (sampleUnits Q) d y)
      (1 + (Q : ℚ) * W * (Q + 1 : ℚ) ^ Q) := by
  unfold mismatchRowPath rowPath
  apply coeffBound_add
  · by_cases hy : y = v
    · subst y
      simp only [Pi.single_eq_same]
      exact coeffBound_C (by norm_num) (by norm_num)
    · simp only [Pi.single_eq_of_ne hy]
      exact coeffBound_C (by norm_num) (by norm_num)
  · unfold mismatchCorrection columnCorrection
    split_ifs
    · exact sample_correction_coeffBound _ _ W hW (fun i _ => hd y i)
    · exact coeffBound_zero (by positivity)

theorem spectral_inverse_abs (R : ℕ) : |(↑((denominatorUnit R)⁻¹) : ℚ)| ≤ 1 := by
  rw [denominatorUnit_inverse, abs_inv, abs_of_nonneg (by positivity)]
  apply inv_le_one_of_one_le₀
  exact_mod_cast (Nat.one_le_pow (R - 1) 2 (by decide))

theorem sourceRow_coeffBound {r Q Δ : ℕ} (N : LayoutScaledMatrices.Numerators r Q Δ)
    (a : MulticolorTypes.UniversalType r Q Δ) (i : Fin Δ) (R W : ℕ)
    (hN : ∀ t g j u v, (N t g j u v).natAbs ≤ W)
    (y : MulticolorTypes.UniversalType r Q Δ) :
    CoeffBound (LayoutScaledMatrices.sourceRow N (denominatorUnit R) a i R (sampleUnits Q) y)
      (1 + (Q : ℚ) * W * (Q + 1 : ℚ) ^ Q) := by
  unfold LayoutScaledMatrices.sourceRow SubexpAnnihilation.rowForMatrices
  apply sample_mismatch_coeffBound _ _ _ _ _ (W : ℚ) (by positivity)
  intro z t
  unfold SubexpAnnihilation.matrixPrescription SubexpAnnihilation.zeroExtendMatrix
  simp only [RingHom.id_apply]
  split_ifs with hu hy
  · rw [LayoutScaledMatrices.unitScaled, abs_neg, abs_mul]
    have hm : |((N t (z.head t) i ⟨a, hu⟩ ⟨z, hy⟩ : ℤ) : ℚ)| ≤ W := by
      exact_mod_cast (show |N t (z.head t) i ⟨a, hu⟩ ⟨z, hy⟩| ≤ (W : ℤ) by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hN t (z.head t) i ⟨a, hu⟩ ⟨z, hy⟩)
    exact (mul_le_mul (spectral_inverse_abs R) hm (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · simp
  · simp

theorem pullback_row_coeffBound_injective {I V : Type*} [Fintype I] [DecidableEq V]
    (owner : I → V) (hinj : Function.Injective owner) (a : I → Polynomial ℚ) (W : ℚ)
    (hW : 0 ≤ W) (ha : ∀ i, CoeffBound (a i) W) (v : V) :
    CoeffBound (LayoutPullback.row owner a v) W := by
  by_cases hv : v ∈ Set.range owner
  · obtain ⟨i, rfl⟩ := hv
    rw [LayoutPullback.row_apply_injective owner hinj a i]
    exact ha i
  · rw [LayoutPullback.row_eq_zero owner a v hv]
    exact coeffBound_zero hW

theorem assembled_row_coeffBound {U I : Type*} [Fintype U] [DecidableEq I] {label : I → U} {b : ℕ}
    (P : BlockPacking.CompleteBlocks label b) (rows : U → U → Polynomial ℚ)
    (W : ℚ) (hW : 1 ≤ W) (hrows : ∀ u v, CoeffBound (rows u v) W) (i v : I) :
    CoeffBound (LayoutBlocks.assembledRow P rows i v) W := by
  by_cases hi : i ∈ Set.range P.embed
  · obtain ⟨⟨j,u⟩, rfl⟩ := hi
    rw [LayoutBlocks.assembledRow_apply]
    exact pullback_row_coeffBound_injective _ (P.blockEmbedding j).injective _ W (by linarith)
      (hrows u) v
  · rw [LayoutBlocks.assembledRow_outside P rows i hi]
    dsimp only
    split_ifs
    · exact coeffBound_C (by simpa using hW) (by linarith)
    · exact coeffBound_C (by simpa using le_trans (by norm_num : (0 : ℚ) ≤ 1) hW) (by linarith)

theorem pullback_row_coeffBound_fibre {I V : Type*} [Fintype I] [DecidableEq V]
    (owner : I → V) (a : I → Polynomial ℚ) (B : ℕ) (W : ℚ) (hW : 0 ≤ W)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (ha : ∀ i, CoeffBound (a i) W) (v : V) :
    CoeffBound (LayoutPullback.row owner a v) (B * W) := by
  intro k
  have he : (LayoutPullback.row owner a v).coeff k =
      ∑ i ∈ Finset.univ.filter (fun i => owner i = v), (a i).coeff k := by
    simp only [LayoutPullback.row, Polynomial.finsetSum_coeff, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => owner i = v), |(a i).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => owner i = v), W :=
      Finset.sum_le_sum (fun i _ => ha i k)
    _ = ((Finset.univ.filter (fun i => owner i = v)).card : ℚ) * W := by simp
    _ ≤ (B : ℚ) * W := mul_le_mul_of_nonneg_right (by exact_mod_cast howner v) hW

/-- An explicit small-bit bound for actual rational row coefficients. -/
def rowCoefficientBound (Q R B : ℕ) : ℕ :=
  B * (1 + Q * (8 * Q) ^ (2 * R) * (Q + 1) ^ Q)

/-- Actual polynomial-row heights, derived through the native constructor. -/
theorem builtLayout_row_coeffBound {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (i : I) (v : V) :
    CoeffBound ((builtLayout owner factor en ε R).row i v) (rowCoefficientBound Q R B) := by
  let pack := searchedPacking owner factor en ε
  let C := universalLayout r Q R
  let W : ℚ := 1 + Q * (8 * Q : ℕ) ^ (2 * R) * (Q + 1 : ℚ) ^ Q
  have hw : 1 ≤ W := by
    dsimp [W]
    exact le_add_of_nonneg_right (by positivity)
  have hc : ∀ a y, CoeffBound (C.row a y) W := by
    intro a y
    change CoeffBound (LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1
      (Subexp.TailInterval.intervalStart r Q R) R) (denominatorUnit R) a 0 R (sampleUnits Q) y) W
    simpa only [W, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using sourceRow_coeffBound (LayoutNumerator.family r Q 1
      (Subexp.TailInterval.intervalStart r Q R) R) a 0 R ((8 * Q) ^ (2 * R))
      (fun t g j u v => LayoutNumerator.family_natAbs_le _ _ hAQ hQ t g j u v) y
  have hb := assembled_row_coeffBound pack.completeBlocks C.row W hw hc i
  have hp := pullback_row_coeffBound_fibre owner
    (LayoutBlocks.assembledRow pack.completeBlocks C.row i) B W (by linarith) howner hb v
  change CoeffBound (LayoutPullback.row owner
    (LayoutBlocks.assembledRow pack.completeBlocks C.row i) v) (rowCoefficientBound Q R B)
  simpa only [rowCoefficientBound, W, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hp

/-- Denominator bit height grows polynomially in the public interpolation dimensions. -/
theorem rowDenominator_le_power (Q R : ℕ) :
    rowDenominator Q R ≤ 2 ^ (R + Nat.clog 2 Q * Q * (Q + 1)) := by
  unfold rowDenominator spectralDenominator
  calc
    2 ^ (R - 1) * Q.factorial ^ (Q + 1) ≤ 2 ^ R * (Q ^ Q) ^ (Q + 1) := by
      gcongr
      · omega
      · exact Nat.factorial_le_pow Q
    _ ≤ 2 ^ R * ((2 ^ Nat.clog 2 Q) ^ Q) ^ (Q + 1) := by
      gcongr
      exact Nat.le_pow_clog (by decide) Q
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; simp only [Nat.mul_assoc]

/-- The same native integer polynomial has an explicit numerator bound. -/
theorem builtLayout_integer_polynomial_bounded {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (i : I) (v : V) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) = Polynomial.C (rowDenominator Q R : ℚ) *
        (builtLayout owner factor en ε R).row i v ∧
      ∀ k, |P.coeff k| ≤ ((rowDenominator Q R * rowCoefficientBound Q R B : ℕ) : ℤ) := by
  obtain ⟨P, hP⟩ := builtLayout_integer_polynomial owner factor en ε R i v
  refine ⟨P, hP, ?_⟩
  intro k
  have he := congrArg (fun p : Polynomial ℚ => p.coeff k) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at he
  change ((P.coeff k : ℤ) : ℚ) = _ at he
  have hb := builtLayout_row_coeffBound owner factor en ε R B howner hQ hAQ i v k
  have hm := mul_le_mul_of_nonneg_left hb
    (show (0 : ℚ) ≤ rowDenominator Q R by positivity)
  have habs : |((P.coeff k : ℤ) : ℚ)| ≤
      ((rowDenominator Q R * rowCoefficientBound Q R B : ℕ) : ℚ) := by
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    exact_mod_cast hm
  exact_mod_cast habs

/-- Explicit logarithmic coefficient budget independent of the universal alphabet size. -/
def rowCoefficientExponent (Q R : ℕ) : ℕ :=
  1 + Nat.clog 2 (8 * (Q + 1)) * (1 + 2 * R + Q)

theorem rowCoefficientBound_le_power (Q R B : ℕ) :
    rowCoefficientBound Q R B ≤ B * 2 ^ rowCoefficientExponent Q R := by
  let c := Nat.clog 2 (8 * (Q + 1))
  have hb : 8 * (Q + 1) ≤ 2 ^ c := Nat.le_pow_clog (by decide) _
  have hQ : Q ≤ 2 ^ c := by omega
  have h8Q : 8 * Q ≤ 2 ^ c := by omega
  have hQ1 : Q + 1 ≤ 2 ^ c := by omega
  have hp : Q * (8 * Q) ^ (2 * R) * (Q + 1) ^ Q ≤
      2 ^ c * (2 ^ c) ^ (2 * R) * (2 ^ c) ^ Q := by gcongr
  have he : 2 ^ c * (2 ^ c) ^ (2 * R) * (2 ^ c) ^ Q =
      2 ^ (c * (1 + 2 * R + Q)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [he] at hp
  have hpos : 1 ≤ 2 ^ (c * (1 + 2 * R + Q)) := Nat.one_le_pow _ _ (by decide)
  have hs : 1 + Q * (8 * Q) ^ (2 * R) * (Q + 1) ^ Q ≤
      2 ^ (1 + c * (1 + 2 * R + Q)) := by
    rw [pow_add, pow_one]
    nlinarith
  exact Nat.mul_le_mul_left B hs

/-- A single explicit polynomial-size exponent controls the common integer numerators. -/
def rowNumeratorExponent (Q R : ℕ) : ℕ :=
  R + Nat.clog 2 Q * Q * (Q + 1) + rowCoefficientExponent Q R

theorem rowNumeratorBound_le_power (Q R B : ℕ) :
    rowDenominator Q R * rowCoefficientBound Q R B ≤ B * 2 ^ rowNumeratorExponent Q R := by
  calc
    _ ≤ 2 ^ (R + Nat.clog 2 Q * Q * (Q + 1)) *
        (B * 2 ^ rowCoefficientExponent Q R) :=
      Nat.mul_le_mul (rowDenominator_le_power Q R) (rowCoefficientBound_le_power Q R B)
    _ = _ := by rw [rowNumeratorExponent, pow_add]; ring

/-- Complete native row representation with one shared denominator, bounded degree,
and polynomial-bit integer numerators; all conclusions follow from the constructor. -/
theorem builtLayout_row_representation {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (i : I) (v : V) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) = Polynomial.C (rowDenominator Q R : ℚ) *
        (builtLayout owner factor en ε R).row i v ∧ P.natDegree ≤ R ∧
      ∀ k, |P.coeff k| ≤ ((B * 2 ^ rowNumeratorExponent Q R : ℕ) : ℤ) := by
  obtain ⟨P, hP, hb⟩ := builtLayout_integer_polynomial_bounded owner factor en ε R B
    howner hQ hAQ i v
  refine ⟨P, hP, ?_, ?_⟩
  · have hinj : Function.Injective (Int.castRingHom ℚ) := by
      intro x y h
      change (x : ℚ) = (y : ℚ) at h
      exact_mod_cast h
    calc
      P.natDegree = (P.map (Int.castRingHom ℚ)).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hinj P).symm
      _ = (Polynomial.C (rowDenominator Q R : ℚ) *
          (builtLayout owner factor en ε R).row i v).natDegree := congrArg Polynomial.natDegree hP
      _ ≤ ((builtLayout owner factor en ε R).row i v).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ R := builtLayout_degree owner factor en ε R i v
  · intro k
    exact (hb k).trans (by exact_mod_cast rowNumeratorBound_le_power Q R B)

theorem rowDenominator_pos (Q R : ℕ) : 0 < rowDenominator Q R := by
  unfold rowDenominator spectralDenominator
  exact Nat.mul_pos (by positivity) (Nat.pow_pos (Nat.factorial_pos Q))

end RiemannGaussian.SemiprimeSourceRowHeight
