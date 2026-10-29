import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumeratorBounds
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.SpectralRank

namespace OAI.Algorithms

/-!
# From the rational spectral matrix to the integer constraint family

The integer constraints are literally `d I - N`. Their rational range has
exactly the dimension of `I - M`, and the same numerators supply the ring
row construction from `LayoutScaledMatrices`.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open Matrix Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport
open LayoutScaledMatrices

variable {r Q Δ : ℕ}

noncomputable def family (r Q Δ A R : ℕ) : Numerators r Q Δ :=
  fun t g i => joint i t g A R

theorem family_support (A R : ℕ) (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (a b : Joint t g i) (hne : family r Q Δ A R t g i a b ≠ 0) :
    (SubexponentialSAT.SubexpRowInterpolation.mismatchPositions
      (fun y : UniversalType r Q Δ => y.head) (a.val.slot i) b.val).card ≤ R :=
  joint_support i t g A R a b hne

theorem family_natAbs_le (A R : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (a b : Joint t g i) :
    (family r Q Δ A R t g i a b).natAbs ≤ (8 * Q) ^ (2 * R) :=
  joint_natAbs_le i t g A R hAQ hQ a b

theorem denominator_natAbs_le (Q R : ℕ) (hQ : 1 ≤ Q) :
    (denominator R).natAbs ≤ (8 * Q) ^ (2 * R) := by
  simp only [denominator, Int.natAbs_pow ]
  calc
    (2 : ℕ) ^ (R - 1) ≤ (8 * Q) ^ (R - 1) := by gcongr; omega
    _ ≤ (8 * Q) ^ (2 * R) := by apply Nat.pow_le_pow_right <;> omega

theorem clearedDefect_natAbs_le (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (A R : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (a b : Joint t g i) :
    (clearedDefect (denominator R) (joint i t g A R) a b).natAbs ≤
      2 * (8 * Q) ^ (2 * R) := by
  have hd : (if a = b then denominator R else 0).natAbs ≤ (8 * Q) ^ (2 * R) := by
    split_ifs
    · exact denominator_natAbs_le Q R hQ
    · simp
  calc
    _ ≤ (if a = b then denominator R else 0).natAbs +
        (joint i t g A R a b).natAbs := Int.natAbs_sub_le _ _
    _ ≤ (8 * Q) ^ (2 * R) + (8 * Q) ^ (2 * R) :=
      add_le_add hd (joint_natAbs_le i t g A R hAQ hQ a b)
    _ = _ := by omega

/-- The rational matrix obtained by casting the literal integer constraints. -/
noncomputable def rationalDefect (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℚ :=
  fun a b => (clearedDefect (denominator R) (joint i t g A R) a b : ℚ)

theorem rationalDefect_eq (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    rationalDefect i t g A R = (denominator R : ℚ) •
      (1 - jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))) := by
  ext a b
  simp only [rationalDefect, clearedDefect, Int.cast_sub]
  rw [joint_cast ℚ (by norm_num)]
  by_cases hab : a = b <;>
    simp [ hab, smul_eq_mul, mul_sub]

theorem rationalDefect_linear (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    (rationalDefect i t g A R).mulVecLin = (denominator R : ℚ) •
      (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin) := by
  rw [rationalDefect_eq]
  apply LinearMap.ext
  intro x
  simp [ ]

theorem rationalDefect_range (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    LinearMap.range (rationalDefect i t g A R).mulVecLin =
      LinearMap.range (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin) := by
  rw [rationalDefect_linear]
  apply LinearMap.range_smul
  simp [denominator]

theorem rationalDefect_finrank (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    finrank ℚ (LinearMap.range (rationalDefect i t g A R).mulVecLin) =
      finrank ℚ (LinearMap.range (LinearMap.id - (jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := ℚ) A R))).mulVecLin)) := by
  rw [rationalDefect_range]

/-- The actual cleared integer matrix inherits the centered spectral bound. -/
theorem centered_rationalDefect_rank_relative
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (finrank ℚ (LinearMap.range (rationalDefect i t g
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R).mulVecLin) : ℚ) ≤
      ε * (Fintype.card (Joint t g i) : ℚ) := by
  rw [rationalDefect_finrank]
  exact Spectral.centered_jointMatrix_rank_relative (by norm_num)
    t g i ε hr hQ hR hsize hε hwidth

/-- The explicit integer numerators now discharge the support hypothesis of
the existing ring-valued interpolation rows. -/
theorem family_sourceRow_annihilates
    {O : Type*} [CommRing O] {node : Fin Q → O}
    (A R : ℕ) (denom : Oˣ) (hdenom : (denom : O) = (denominator R : O))
    (a : UniversalType r Q Δ) (i : Fin Δ)
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot i t)
    (z : UniversalType r Q Δ → ℤ)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hconstraint : clearedDefect (denominator R) (joint i t g A R) *ᵥ
      (fun y : Joint t g i => z y) = 0) :
    (∑ y, (sourceRow (family r Q Δ A R) denom a i R units y).eval (node t) *
      (z y : O)) = 0 := by
  exact sourceRow_annihilates (family r Q Δ A R) (denominator R) denom hdenom
    a i R units (fun t g j u v h => family_support A R t g j u v h)
    t g hg z hz hconstraint

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
