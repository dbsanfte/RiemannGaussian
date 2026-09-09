/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactPrimal

/-!
# A sharp enclosure of the exact phase coefficients

An approximate primal row is only rational input. Its residual in the
central contact equations is checked exactly, then transported to the
proved exact root and its true inverse. This sharp enclosure supports
positivity checks without treating numerical stationary coefficients as
an exact solution.
-/

open scoped Classical
open Matrix

namespace RiemannGaussian

/-- Rational center for the cost-normalized exact coefficient row. -/
def phaseContactPrimalCenterQ (i : Fin 9) : ℚ :=
  match i.val with
  | 0 => 1845369414132787269460269694619345222011469044639 / 10000000000000000000000000000000000000000000000000
  | 1 => 3951512936228226246336213504118533757240686099799 / 12500000000000000000000000000000000000000000000000
  | 2 => 4873164120945378274333792628167478413132849971037 / 25000000000000000000000000000000000000000000000000
  | 3 => 8030110489783631443720910922776490212439320861227 / 100000000000000000000000000000000000000000000000000
  | 4 => 1741724185903389665646217249479128287577252187891 / 100000000000000000000000000000000000000000000000000
  | 5 => 6699551824910587859968147661334617127349778711 / 12500000000000000000000000000000000000000000000000
  | 6 => 4774114100221225505823953898196506811706214417 / 50000000000000000000000000000000000000000000000000
  | 7 => 467220101773317925606586663530380369022380089 / 25000000000000000000000000000000000000000000000000
  | 8 => 28124899963417725897825519235445040174432679 / 50000000000000000000000000000000000000000000000000
  | _ => 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The rational primal row satisfies each central contact equation to
within `10⁻⁴⁰`; this is exact rational arithmetic. -/
theorem phaseContactPrimalCenterQ_residual (k : Fin 9) :
    |(∑ i : Fin 9, phaseContactPrimalCenterQ i * phaseContactRootMatrixQ i k) -
      (if k.val = 8 then 1 else 0)| ≤ (1 / 10 ^ 40 : ℚ) := by
  fin_cases k <;> norm_num [phaseContactPrimalCenterQ, phaseContactRootMatrixQ,
    phaseContactJetQ, phaseContactRootCenterQ, phaseContactFrequency, Fin.sum_univ_succ]

/-- The rational primal center has absolute coefficient mass at most one. -/
theorem phaseContactPrimalCenterQ_mass_le :
    ∑ i : Fin 9, |phaseContactPrimalCenterQ i| ≤ (1 : ℚ) := by
  norm_num [phaseContactPrimalCenterQ, Fin.sum_univ_succ]

noncomputable section

/-- The rational center interpreted in the real coefficient space. -/
def phaseContactPrimalCenter (i : Fin 9) : ℝ := (phaseContactPrimalCenterQ i : ℝ)

/-- The rational central matrix is the actual contact Jacobian at the
same rational center. -/
theorem phaseContactRootMatrixQ_cast (i k : Fin 9) :
    (phaseContactRootMatrixQ i k : ℝ) = phaseContactJacobian phaseContactRootCenter i k := by
  fin_cases k <;>
    simp [phaseContactRootMatrixQ, phaseContactJacobian, phaseContactRootCenter,
      phaseContactCost, (phaseContactJetQ_cast _ _).1, (phaseContactJetQ_cast _ _).2.2.1, apply_ite]
  split_ifs <;> simp_all

private theorem exactJacobian_entry_error (i k : Fin 9) :
    |phaseContactJacobian phaseContactExactRoot i k -
      phaseContactJacobian phaseContactRootCenter i k| ≤ (1 / 10 ^ 18 : ℝ) := by
  have hc (k : Fin 9) : |phaseContactRootCenter k| ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (abs_phaseContactRootCenterQ_le k)
    have h' : |phaseContactRootCenter k| ≤ (999999 / 1000000 : ℝ) := by
      simpa only [phaseContactRootCenter, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using h
    exact h'.trans (by norm_num)
  have hq (j : Fin 4) : |phaseContactExactRoot (phaseContactCosineCoordinate j)| ≤ 1 :=
    (abs_phaseContactExactRoot_cosine_lt_one j).le
  have hd (k : Fin 9) : |phaseContactExactRoot k - phaseContactRootCenter k| ≤
      (44 / 10 ^ 40 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans
      phaseContactExactRoot_dist_le_refined
  have h := abs_phaseContactSecantAction_sub_diagonal_le
    (h := Pi.single k 1) (by norm_num : (0 : ℝ) ≤ 44 / 10 ^ 40)
    (by norm_num : (0 : ℝ) ≤ 1) hc hq hq hd hd
    (fun j ↦ by simp only [Pi.single_apply]; split_ifs <;> norm_num) i
  rw [← phaseContactJacobian_mulVec, ← phaseContactJacobian_mulVec,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h.trans (by norm_num)

private theorem exactPrimal_residual (k : Fin 9) :
    |(phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactExactRoot) k -
      (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) k| ≤ (2 / 10 ^ 18 : ℝ) := by
  have hc : |(phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactRootCenter) k -
      (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) k| ≤ (1 / 10 ^ 40 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (phaseContactPrimalCenterQ_residual k)
    push_cast at h
    simpa [Matrix.vecMul, dotProduct, phaseContactPrimalCenter,
      phaseContactRootMatrixQ_cast, Pi.single_apply, Fin.ext_iff, apply_ite] using h
  have hm : ∑ i : Fin 9, |phaseContactPrimalCenter i| ≤ (1 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr phaseContactPrimalCenterQ_mass_le
    simpa only [phaseContactPrimalCenter, Rat.cast_sum, Rat.cast_abs, Rat.cast_one] using h
  have hv : |(phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactExactRoot) k -
      (phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactRootCenter) k| ≤
      (1 / 10 ^ 18 : ℝ) := by
    simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
    calc
      _ ≤ ∑ i : Fin 9, |phaseContactPrimalCenter i| *
          |phaseContactJacobian phaseContactExactRoot i k -
            phaseContactJacobian phaseContactRootCenter i k| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (s := (Finset.univ : Finset (Fin 9)))
          (f := fun i ↦ phaseContactPrimalCenter i *
            (phaseContactJacobian phaseContactExactRoot i k - phaseContactJacobian phaseContactRootCenter i k))
      _ ≤ ∑ i : Fin 9, |phaseContactPrimalCenter i| * (1 / 10 ^ 18 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (exactJacobian_entry_error i k) (abs_nonneg _))
      _ ≤ _ := by rw [← Finset.sum_mul]; nlinarith
  have ht := abs_sub_le
    ((phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactExactRoot) k)
    ((phaseContactPrimalCenter ᵥ* phaseContactJacobian phaseContactRootCenter) k)
    ((Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) k)
  linarith

private theorem exactInverse_entry_le (i k : Fin 9) :
    |(phaseContactJacobian phaseContactExactRoot)⁻¹ i k| ≤ (44 : ℝ) := by
  let J := phaseContactJacobian phaseContactExactRoot
  let e : Fin 9 → ℝ := Pi.single k 1
  have hJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J
    ((Matrix.isUnit_iff_isUnit_det J).mp isUnit_phaseContactExactRoot_jacobian)
  have h := norm_le_mul_norm_phaseContactExactRoot_jacobian (J⁻¹ *ᵥ e)
  change ‖J⁻¹ *ᵥ e‖ ≤ 44 * ‖J *ᵥ (J⁻¹ *ᵥ e)‖ at h
  rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec] at h
  have he : ‖e‖ = 1 := by simp only [e, Pi.norm_single, norm_one]
  rw [he, mul_one] at h
  have hi := (norm_le_pi_norm (J⁻¹ *ᵥ e) i).trans h
  simpa only [J, e, Matrix.mulVec_single_one, Matrix.col_apply, Real.norm_eq_abs] using hi

/-- Every true primal coefficient is within `10⁻¹⁵` of the rational
center. The proof uses the actual contact root and matrix inverse. -/
theorem abs_phaseContactExactCoefficients_sub_center_le (i : Fin 9) :
    |phaseContactExactCoefficients i - phaseContactPrimalCenter i| ≤ (1 / 10 ^ 15 : ℝ) := by
  let J := phaseContactJacobian phaseContactExactRoot
  let e : Fin 9 → ℝ := Pi.single 8 1
  have hJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J
    ((Matrix.isUnit_iff_isUnit_det J).mp isUnit_phaseContactExactRoot_jacobian)
  have he : (phaseContactPrimalCenter ᵥ* J - e) ᵥ* J⁻¹ =
      phaseContactPrimalCenter - phaseContactExactCoefficients := by
    rw [Matrix.sub_vecMul, Matrix.vecMul_vecMul, hJ, Matrix.vecMul_one]
    congr 1
    ext k
    simp only [e, Matrix.single_one_vecMul, Matrix.row_apply,
      phaseContactExactCoefficients, phaseContactPrimalRow, J]
  have hbound : |((phaseContactPrimalCenter ᵥ* J - e) ᵥ* J⁻¹) i| ≤ (1 / 10 ^ 15 : ℝ) := by
    calc
      _ ≤ ∑ k : Fin 9, |(phaseContactPrimalCenter ᵥ* J - e) k| * |J⁻¹ k i| := by
        simpa only [Matrix.vecMul, dotProduct, abs_mul] using Finset.abs_sum_le_sum_abs
          (s := (Finset.univ : Finset (Fin 9)))
          (f := fun k ↦ (phaseContactPrimalCenter ᵥ* J - e) k * J⁻¹ k i)
      _ ≤ ∑ _k : Fin 9, (2 / 10 ^ 18 : ℝ) * 44 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (exactPrimal_residual k) (exactInverse_entry_le k i) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  rw [he] at hbound
  simpa only [Pi.sub_apply, abs_sub_comm] using hbound

end

end RiemannGaussian
