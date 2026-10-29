/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteDenominatorBits

/-! # Actual original D.9 weight and weightPrefix common denominators
Every retained weight and partial coefficient sum uses ONE original-derived
common denominator. No repeated-sum denominator multiplication is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteWeightHeight
open scoped BigOperators
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeHermiteArrayHeight
  SemiprimeD1JetRecoveryWeights SemiprimeD1JetRecoveryGrid SemiprimeD1TaperedLoss
  SemiprimeD1WireKernelOriginal SemiprimeD1HermiteDenominatorHeight
  SemiprimeD1HermiteDenominatorBits

/-- Literal representations of powers have fixed power denominators. -/
theorem representation_pow {q : ℚ} {d B : ℕ} (hq : Representation q d B) (n : ℕ) :
    Representation (q^n) (d^n) (B^n) := by
  induction n with
  | zero => exact ⟨1,by simp,by simp⟩
  | succ n ih =>
    simpa only [pow_succ] using representation_mul ih hq

/-- Actual scalar E_t0 uses acquired signed integer products with a positive denominator. -/
def scalarDenominator (a h u t : ℕ) : ℕ :=
  (SemiprimeD1JetRecoveryScalarHeight.denominator a h u t).natAbs

/-- Actual E_t0 numerator magnitude before reduction. -/
def scalarNumerator (a h u t : ℕ) : ℕ :=
  (SemiprimeD1JetRecoveryScalarHeight.numerator a h u t).natAbs

/-- The actual scalar denominator is positive, not advised. -/
theorem scalarDenominator_pos (a h u t : ℕ) : 0<scalarDenominator a h u t :=
  Int.natAbs_pos.mpr (SemiprimeD1JetRecoveryScalarHeight.denominator_ne_zero a h u t)

/-- Exact original E_t0 representation, preserving all scalar signs. -/
theorem scalar_representation (a h u t : ℕ) :
    Representation (Ezero a h u t) (scalarDenominator a h u t) (scalarNumerator a h u t) := by
  rw [SemiprimeD1JetRecoveryScalarHeight.ratio_spec]
  exact int_ratio_representation _ _

/-- Original evaluation argument has numerator at most2L and denominator exactly2L. -/
theorem argument_representation (a : ℕ) (t : Fin (size a)) :
    Representation (SemiprimeD1WeightPrecision.argument a t.val) (size a) (size a) := by
  have h := int_ratio_representation (-point a t.val) ((2:ℤ)^(a+1))
  have he : ((2:ℤ)^(a+1)).natAbs=size a := by norm_num [Int.natAbs_pow,SemiprimeD1WireKernelOriginal.size]
  rw [he] at h
  have hm := representation_mono h (by
    simpa only [Int.natAbs_neg] using (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a t.val t.isLt).le)
  simpa only [SemiprimeD1WeightPrecision.argument,Int.cast_neg,Int.cast_pow,Int.cast_ofNat] using hm

/-- Power padding uses a single actual2L denominator, not a new denominator per sum. -/
theorem argument_power_representation (a h u : ℕ) (t : Fin (size a)) (k : ℕ)
    (hk : k≤nodeMultiplicity a h u t.val) :
    Representation ((SemiprimeD1WeightPrecision.argument a t.val)^k)
      ((size a)^nodeMultiplicity a h u t.val) ((size a)^nodeMultiplicity a h u t.val) := by
  exact representation_power_extend (size a) (size a) k _ (by unfold SemiprimeD1WireKernelOriginal.size;positivity)
    le_rfl hk (representation_pow (argument_representation a t) k)

/-- Actual common denominator of ALL retained weights at one original node. -/
def weightDenominator (a h u t : ℕ) : ℕ :=
  scalarDenominator a h u t*(sourceDenominator a h u t*size a)^nodeMultiplicity a h u t

/-- Explicit fixed numerator envelope for ALL actual weight sums/prefixes at one node. -/
def weightNumerator (a h u t : ℕ) : ℕ :=
  scalarNumerator a h u t*nodeMultiplicity a h u t*
    (inverseBase (nodeMultiplicity a h u t) (sourceDenominator a h u t)
      (sourceNumerator a h u t)*size a)^nodeMultiplicity a h u t

/-- Actual native scalar coefficient-sum weightPrefix, with the same original caches as acquire. -/
def weightPrefix (a h u t j len : ℕ) : ℚ :=
  Ezero a h u t*∑k∈Finset.range len,if j≤k then
    coefficient (acquire a h u t).inverse.coefficients (k-j)*
      (SemiprimeD1WeightPrecision.argument a t)^k else 0

/-- EVERY actual node-weight weightPrefix has ONE fixed denominator, derived solely from
original factors/inverse recurrence and literal loop indices. -/
theorem prefix_representation (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) (j len : ℕ) (hlen : len≤nodeMultiplicity a h u t.val) :
    Representation (weightPrefix a h u t.val j len) (weightDenominator a h u t.val) (weightNumerator a h u t.val) := by
  let q := nodeMultiplicity a h u t.val
  let D := sourceDenominator a h u t.val
  let V := inverseBase q D (sourceNumerator a h u t.val)
  have hs : Representation
      (∑k∈Finset.range len,if j≤k then coefficient (acquire a h u t.val).inverse.coefficients (k-j)*
          (SemiprimeD1WeightPrecision.argument a t.val)^k else 0)
      ((D*size a)^q) (len*(V*size a)^q) := by
    have hh := representation_sum (Finset.range len)
      (fun k => if j≤k then coefficient (acquire a h u t.val).inverse.coefficients (k-j)*
        (SemiprimeD1WeightPrecision.argument a t.val)^k else 0) ((D*size a)^q) ((V*size a)^q) (by
        intro k hk
        have hkl := Finset.mem_range.mp hk
        by_cases hj : j≤k
        · simp only [hj,ite_true]
          have hm := representation_mul (original_inverse_representation a h u t hq (k-j) (by omega))
            (argument_power_representation a h u t k (by omega))
          simpa only [mul_pow] using hm
        · simp only [hj,ite_false]
          exact representation_mono (representation_zero _) (Nat.zero_le _))
    simpa only [Finset.card_range] using hh
  have hm := representation_mul (scalar_representation a h u t.val) hs
  apply representation_mono hm
  unfold weightNumerator
  dsimp only [q,D,V] at *
  nlinarith [Nat.mul_le_mul_left (scalarNumerator a h u t.val*
    (inverseBase (nodeMultiplicity a h u t.val) (sourceDenominator a h u t.val)
      (sourceNumerator a h u t.val)*size a)^nodeMultiplicity a h u t.val) hlen]

/-- Each actual stored weight is the full weightPrefix and has the SAME common denominator. -/
theorem weight_representation (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) (j : ℕ) (hj : j<nodeMultiplicity a h u t.val) :
    Representation (coefficient (acquire a h u t.val).weights j)
      (weightDenominator a h u t.val) (weightNumerator a h u t.val) := by
  rw [acquire_weight a h u t.val j hj]
  exact prefix_representation a h u t hq j _ le_rfl

/-- The original weight denominator is positive even when a partial sum is zero. -/
theorem weightDenominator_pos (a h u t : ℕ) : 0<weightDenominator a h u t := by
  unfold weightDenominator
  exact Nat.mul_pos (scalarDenominator_pos _ _ _ _) (pow_pos
    (Nat.mul_pos (sourceDenominator_pos _ _ _ _) (by unfold SemiprimeD1WireKernelOriginal.size;positivity)) _)

/-- Canonical normalization of every actual weight weightPrefix cannot increase the derived bounds. -/
theorem prefix_reduced_bounds (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) (j len : ℕ) (hlen : len≤nodeMultiplicity a h u t.val) :
    (weightPrefix a h u t.val j len).den≤weightDenominator a h u t.val ∧
    (weightPrefix a h u t.val j len).num.natAbs≤weightNumerator a h u t.val :=
  representation_reduced_bound (weightDenominator_pos _ _ _ _)
    (prefix_representation a h u t hq j len hlen)

end RiemannGaussian.SemiprimeD1HermiteWeightHeight
