/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactRootData
import RiemannGaussian.ZetaPhaseContactJacobian
import Mathlib.Topology.MetricSpace.Contracting

/-!
# An exact isolated solution of the four-contact equations

Rational data and exact Chebyshev secants prove that a preconditioned map
contracts on a closed real box. Banach's theorem supplies a unique exact
solution in that box. The contact cosines are interior and the contact
masses are strictly positive.

This constructs the proposed optimizer's dual contact geometry. Global
nonnegativity of the associated primal kernel and attainment of the dual
bound remain separate obligations; solving the equations alone does not
assert global optimality or a new statement about zeta zeros.
-/

open scoped Classical NNReal
open Matrix

namespace RiemannGaussian

noncomputable section

/-- The rational root center viewed in the real contact space. -/
def phaseContactRootCenter (i : Fin 9) : ℝ := (phaseContactRootCenterQ i : ℝ)

private def rootPreconditioner : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j ↦ (phaseContactRootPreconditionerQ i j : ℝ)

private def rootCentralMatrix : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j ↦ (phaseContactRootMatrixQ i j : ℝ)

private theorem rootResidual_cast (i : Fin 9) :
    (phaseContactRootResidualQ i : ℝ) = phaseContactSystem phaseContactRootCenter i := by
  unfold phaseContactRootResidualQ phaseContactSystem phaseContactCost phaseContactSourceCoeff
  dsimp only
  push_cast
  simp only [(phaseContactJetQ_cast _ _).1]
  split_ifs <;> norm_num [phaseContactRootCenter]

private theorem rootCentralMatrix_mulVec (h : Fin 9 → ℝ) :
    rootCentralMatrix *ᵥ h = phaseContactSecantAction phaseContactRootCenter phaseContactRootCenter h := by
  ext i
  dsimp [rootCentralMatrix, Matrix.mulVec, dotProduct, phaseContactRootMatrixQ]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Rat.cast_neg, Rat.cast_mul, apply_ite, Rat.cast_one,
    Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]
  simp only [(phaseContactJetQ_cast _ _).1, (phaseContactJetQ_cast _ _).2.2.1]
  unfold phaseContactSecantAction phaseContactRootCenter phaseContactCost
  simp only [Fin.sum_univ_succ, phaseContactMassCoordinate, phaseContactCosineCoordinate]
  dsimp
  ring


private theorem norm_matrix_mulVec_le {M : Matrix (Fin 9) (Fin 9) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hM : ∀ i, ∑ j : Fin 9, |M i j| ≤ C) (x : Fin 9 → ℝ) :
    ‖M *ᵥ x‖ ≤ C * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg x))).mpr
  intro i
  change |∑ j : Fin 9, M i j * x j| ≤ C * ‖x‖
  calc
    _ ≤ ∑ j : Fin 9, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 9, |M i j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j : Fin 9, |M i j|) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)

private theorem newton_difference (B J : Matrix (Fin 9) (Fin 9) ℝ)
    (u v : Fin 9 → ℝ) :
    (u - B *ᵥ phaseContactSystem u) - (v - B *ᵥ phaseContactSystem v) =
      (1 - B * J) *ᵥ (u - v) -
        B *ᵥ (phaseContactSecantAction u v (u - v) - J *ᵥ (u - v)) := by
  have he : phaseContactSystem u - phaseContactSystem v =
      phaseContactSecantAction u v (u - v) := by
    ext i
    exact phaseContactSystem_sub_eq_secant u v i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    ← he]
  simp only [Matrix.mulVec_sub]
  abel

private theorem newton_contraction {B J : Matrix (Fin 9) (Fin 9) ℝ} {c : Fin 9 → ℝ}
    (hB : ∀ i, ∑ j : Fin 9, |B i j| ≤ 22)
    (hBJ : ∀ i, ∑ j : Fin 9, |(1 - B * J) i j| ≤ 1 / 4)
    (hJ : ∀ h, J *ᵥ h = phaseContactSecantAction c c h)
    (hc : ∀ i, |c i| ≤ 1 - 1 / 10 ^ 30)
    {u v : Fin 9 → ℝ} (hu : ‖u - c‖ ≤ 1 / 10 ^ 30) (hv : ‖v - c‖ ≤ 1 / 10 ^ 30) :
    ‖(u - B *ᵥ phaseContactSystem u) - (v - B *ᵥ phaseContactSystem v)‖ ≤
      (1 / 2 : ℝ) * ‖u - v‖ := by
  have huc (i : Fin 9) : |u i - c i| ≤ (1 / 10 ^ 30 : ℝ) := (norm_le_pi_norm (u - c) i).trans hu
  have hvc (i : Fin 9) : |v i - c i| ≤ (1 / 10 ^ 30 : ℝ) := (norm_le_pi_norm (v - c) i).trans hv
  have hc' (i : Fin 9) : |c i| ≤ 1 := (hc i).trans (by norm_num)
  have hu' (j : Fin 4) : |u (phaseContactCosineCoordinate j)| ≤ 1 := by
    have ht := abs_sub_le (u (phaseContactCosineCoordinate j)) (c (phaseContactCosineCoordinate j)) 0
    simp only [sub_zero] at ht
    linarith [huc (phaseContactCosineCoordinate j), hc (phaseContactCosineCoordinate j)]
  have hv' (j : Fin 4) : |v (phaseContactCosineCoordinate j)| ≤ 1 := by
    have ht := abs_sub_le (v (phaseContactCosineCoordinate j)) (c (phaseContactCosineCoordinate j)) 0
    simp only [sub_zero] at ht
    linarith [hvc (phaseContactCosineCoordinate j), hc (phaseContactCosineCoordinate j)]
  have hrem : ‖phaseContactSecantAction u v (u - v) - J *ᵥ (u - v)‖ ≤
      16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖u - v‖ := by
    rw [hJ]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact abs_phaseContactSecantAction_sub_diagonal_le (by norm_num) (norm_nonneg _)
      hc' hu' hv' huc hvc (fun k ↦ norm_le_pi_norm (u - v) k) i
  rw [newton_difference]
  calc
    _ ≤ ‖(1 - B * J) *ᵥ (u - v)‖ +
        ‖B *ᵥ (phaseContactSecantAction u v (u - v) - J *ᵥ (u - v))‖ := norm_sub_le _ _
    _ ≤ (1 / 4 : ℝ) * ‖u - v‖ +
        22 * ‖phaseContactSecantAction u v (u - v) - J *ᵥ (u - v)‖ :=
      add_le_add (norm_matrix_mulVec_le (by norm_num) hBJ _) (norm_matrix_mulVec_le (by norm_num) hB _)
    _ ≤ (1 / 4 : ℝ) * ‖u - v‖ + 22 * (16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖u - v‖) := by
      linarith
    _ ≤ _ := by nlinarith [norm_nonneg (u - v)]

private theorem newton_root_exists_unique
    {B J : Matrix (Fin 9) (Fin 9) ℝ} {c : Fin 9 → ℝ}
    (hB : ∀ i, ∑ j : Fin 9, |B i j| ≤ 22)
    (hBJ : ∀ i, ∑ j : Fin 9, |(1 - B * J) i j| ≤ 1 / 4)
    (hJB : ∀ i, ∑ j : Fin 9, |(1 - J * B) i j| ≤ 1 / 4)
    (hJ : ∀ h, J *ᵥ h = phaseContactSecantAction c c h)
    (hc : ∀ i, |c i| ≤ 1 - 1 / 10 ^ 30)
    (hF : ‖phaseContactSystem c‖ ≤ 1 / 10 ^ 40) :
    ∃! u : Fin 9 → ℝ, ‖u - c‖ ≤ 1 / 10 ^ 30 ∧ phaseContactSystem u = 0 := by
  let f : (Fin 9 → ℝ) → (Fin 9 → ℝ) := fun u ↦ u - B *ᵥ phaseContactSystem u
  let s := Metric.closedBall c (1 / 10 ^ 30 : ℝ)
  have hc_mem : c ∈ s := by simp [s, Metric.mem_closedBall]
  have hcenter : ‖f c - c‖ ≤ (22 : ℝ) * (1 / 10 ^ 40) := by
    have he : f c - c = -(B *ᵥ phaseContactSystem c) := by dsimp [f]; abel
    rw [he, norm_neg]
    exact (norm_matrix_mulVec_le (by norm_num) hB _).trans
      (mul_le_mul_of_nonneg_left hF (by norm_num))
  have hmaps : Set.MapsTo f s s := by
    intro u hu
    change dist u c ≤ (1 / 10 ^ 30 : ℝ) at hu
    change dist (f u) c ≤ (1 / 10 ^ 30 : ℝ)
    rw [dist_eq_norm] at hu ⊢
    have hcon := newton_contraction hB hBJ hJ hc hu
      (show ‖c - c‖ ≤ (1 / 10 ^ 30 : ℝ) by simp)
    change ‖f u - f c‖ ≤ (1 / 2 : ℝ) * ‖u - c‖ at hcon
    calc
      _ ≤ ‖f u - f c‖ + ‖f c - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (1 / 2 : ℝ) * ‖u - c‖ + 22 * (1 / 10 ^ 40) := add_le_add hcon hcenter
      _ ≤ _ := by linarith
  have hf : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict f s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    change dist (f u) (f v) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (u : Fin 9 → ℝ) (v : Fin 9 → ℝ)
    have hu : ‖(u : Fin 9 → ℝ) - c‖ ≤ (1 / 10 ^ 30 : ℝ) := by
      simpa only [s, Metric.mem_closedBall, dist_eq_norm] using u.property
    have hv : ‖(v : Fin 9 → ℝ) - c‖ ≤ (1 / 10 ^ 30 : ℝ) := by
      simpa only [s, Metric.mem_closedBall, dist_eq_norm] using v.property
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      newton_contraction hB hBJ hJ hc hu hv
  obtain ⟨u, hu, hfu, _⟩ := ContractingWith.exists_fixedPoint'
    (s := s) Metric.isClosed_closedBall.isComplete hmaps hf hc_mem (edist_ne_top _ _)
  have hu_ball : ‖u - c‖ ≤ (1 / 10 ^ 30 : ℝ) := by
    simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hu
  have hBu : B *ᵥ phaseContactSystem u = 0 := by
    change u - B *ᵥ phaseContactSystem u = u at hfu
    exact sub_eq_self.mp hfu
  have hFu : phaseContactSystem u = 0 := by
    have hb := norm_matrix_mulVec_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hJB (phaseContactSystem u)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hBu,
      Matrix.mulVec_zero, sub_zero] at hb
    apply norm_eq_zero.mp
    linarith [norm_nonneg (phaseContactSystem u)]
  refine ⟨u, ⟨hu_ball, hFu⟩, ?_⟩
  intro v hv
  have hcon := newton_contraction hB hBJ hJ hc hv.1 hu_ball
  rw [hv.2, hFu, Matrix.mulVec_zero, sub_zero, sub_zero] at hcon
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  linarith [norm_nonneg (v - u)]

private theorem rootCenter_box (i : Fin 9) :
    |phaseContactRootCenter i| ≤ 1 - 1 / 10 ^ 30 := by
  have h : |phaseContactRootCenter i| ≤ (999999 / 1000000 : ℝ) := by
    simpa only [phaseContactRootCenter, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (abs_phaseContactRootCenterQ_le i)
  linarith

private theorem rootPreconditioner_row (i : Fin 9) :
    ∑ j : Fin 9, |rootPreconditioner i j| ≤ (22 : ℝ) := by
  unfold rootPreconditioner
  exact_mod_cast phaseContactRootPreconditionerQ_row_le i

private theorem cast_contact_delta (i j : Fin 9) :
    ((if i.val = j.val then 1 else 0 : ℚ) : ℝ) = (if i = j then 1 else 0 : ℝ) := by
  by_cases h : i = j
  · simp [h]
  · have hv : i.val ≠ j.val := fun hv ↦ h (Fin.ext hv)
    simp [h, hv]

private theorem rootCentralMatrix_left_row_small (i : Fin 9) :
    ∑ j : Fin 9, |(1 - rootPreconditioner * rootCentralMatrix) i j| ≤ (1 / 10 ^ 9 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (phaseContactRootMatrixQ_left_error i)
  push_cast at h
  simp only [cast_contact_delta] at h
  simpa only [rootPreconditioner, rootCentralMatrix, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mul_apply] using h

private theorem rootCentralMatrix_right_row_small (i : Fin 9) :
    ∑ j : Fin 9, |(1 - rootCentralMatrix * rootPreconditioner) i j| ≤ (1 / 10 ^ 9 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (phaseContactRootMatrixQ_right_error i)
  push_cast at h
  simp only [cast_contact_delta] at h
  simpa only [rootPreconditioner, rootCentralMatrix, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mul_apply] using h

private theorem rootCentralMatrix_left_row (i : Fin 9) :
    ∑ j : Fin 9, |(1 - rootPreconditioner * rootCentralMatrix) i j| ≤ (1 / 4 : ℝ) :=
  (rootCentralMatrix_left_row_small i).trans (by norm_num)

private theorem rootCentralMatrix_right_row (i : Fin 9) :
    ∑ j : Fin 9, |(1 - rootCentralMatrix * rootPreconditioner) i j| ≤ (1 / 4 : ℝ) :=
  (rootCentralMatrix_right_row_small i).trans (by norm_num)

private theorem rootCenter_residual :
    ‖phaseContactSystem phaseContactRootCenter‖ ≤ (1 / 10 ^ 40 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs, ← rootResidual_cast]
  have h := (Rat.cast_le (K := ℝ)).mpr (abs_phaseContactRootResidualQ_le i)
  norm_num only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at h ⊢
  exact h

/-- The four-contact equations have one and only one exact solution
within `10⁻³⁰` in every coordinate of the specified rational center. -/
theorem exists_unique_phaseContactRoot :
    ∃! u : Fin 9 → ℝ, ‖u - phaseContactRootCenter‖ ≤ 1 / 10 ^ 30 ∧ phaseContactSystem u = 0 :=
  newton_root_exists_unique rootPreconditioner_row rootCentralMatrix_left_row
    rootCentralMatrix_right_row rootCentralMatrix_mulVec rootCenter_box rootCenter_residual

/-- The exact four-contact solution selected by the proved existence and
uniqueness theorem. The definition depends on no floating-point oracle. -/
def phaseContactExactRoot : Fin 9 → ℝ := exists_unique_phaseContactRoot.exists.choose

/-- The exact contact solution lies in the proved isolation ball. -/
theorem phaseContactExactRoot_dist_le :
    ‖phaseContactExactRoot - phaseContactRootCenter‖ ≤ (1 / 10 ^ 30 : ℝ) :=
  exists_unique_phaseContactRoot.exists.choose_spec.1

/-- All nine contact equations vanish exactly at the constructed root. -/
theorem phaseContactExactRoot_system : phaseContactSystem phaseContactExactRoot = 0 :=
  exists_unique_phaseContactRoot.exists.choose_spec.2

/-- Any other contact solution in the isolation ball is the same exact root. -/
theorem phaseContactExactRoot_unique {u : Fin 9 → ℝ}
    (hu : ‖u - phaseContactRootCenter‖ ≤ (1 / 10 ^ 30 : ℝ)) (hF : phaseContactSystem u = 0) :
    u = phaseContactExactRoot :=
  exists_unique_phaseContactRoot.unique ⟨hu, hF⟩
    ⟨phaseContactExactRoot_dist_le, phaseContactExactRoot_system⟩

/-- The four contact cosines remain strictly inside the true cosine interval. -/
theorem abs_phaseContactExactRoot_cosine_lt_one (j : Fin 4) :
    |phaseContactExactRoot (phaseContactCosineCoordinate j)| < 1 := by
  let k := phaseContactCosineCoordinate j
  have hdist : |phaseContactExactRoot k - phaseContactRootCenter k| ≤ (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans phaseContactExactRoot_dist_le
  have hc : |phaseContactRootCenter k| ≤ (999999 / 1000000 : ℝ) := by
    simpa only [phaseContactRootCenter, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (abs_phaseContactRootCenterQ_le k)
  have ht := abs_sub_le (phaseContactExactRoot k) (phaseContactRootCenter k) 0
  simp only [sub_zero] at ht
  change |phaseContactExactRoot k| < 1
  linarith

/-- Every contact mass at the exact solution is strictly positive. -/
theorem phaseContactExactRoot_mass_pos (j : Fin 4) :
    0 < phaseContactExactRoot (phaseContactMassCoordinate j) := by
  let k := phaseContactMassCoordinate j
  have hdist : |phaseContactExactRoot k - phaseContactRootCenter k| ≤ (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans phaseContactExactRoot_dist_le
  have hc : (1 / 100 : ℝ) ≤ phaseContactRootCenter k := by
    simpa only [phaseContactRootCenter, k, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (phaseContactRootCenterQ_mass_pos j)
  have hd := (abs_le.mp hdist).1
  change 0 < phaseContactExactRoot k
  linarith

/-- The central residual and contraction sharpen the exact solution's
distance to the rational center well inside the original isolation ball. -/
theorem phaseContactExactRoot_dist_le_refined :
    ‖phaseContactExactRoot - phaseContactRootCenter‖ ≤ (44 / 10 ^ 40 : ℝ) := by
  have h := newton_contraction rootPreconditioner_row rootCentralMatrix_left_row
    rootCentralMatrix_mulVec rootCenter_box phaseContactExactRoot_dist_le
    (show ‖phaseContactRootCenter - phaseContactRootCenter‖ ≤ (1 / 10 ^ 30 : ℝ) by simp)
  rw [phaseContactExactRoot_system, Matrix.mulVec_zero, sub_zero] at h
  have hstep : ‖(phaseContactRootCenter - rootPreconditioner *ᵥ
      phaseContactSystem phaseContactRootCenter) - phaseContactRootCenter‖ ≤ (22 / 10 ^ 40 : ℝ) := by
    have he : (phaseContactRootCenter - rootPreconditioner *ᵥ phaseContactSystem phaseContactRootCenter) -
        phaseContactRootCenter = -(rootPreconditioner *ᵥ phaseContactSystem phaseContactRootCenter) := by abel
    rw [he, norm_neg]
    have hb := norm_matrix_mulVec_le (by norm_num : (0 : ℝ) ≤ 22) rootPreconditioner_row
      (phaseContactSystem phaseContactRootCenter)
    linarith [rootCenter_residual]
  have ht := norm_sub_le_norm_sub_add_norm_sub phaseContactExactRoot
    (phaseContactRootCenter - rootPreconditioner *ᵥ phaseContactSystem phaseContactRootCenter)
    phaseContactRootCenter
  linarith

private theorem rootJacobian_error_norm (h : Fin 9 → ℝ) :
    ‖(1 - rootPreconditioner * phaseContactJacobian phaseContactExactRoot) *ᵥ h‖ ≤
      (1 / 2 : ℝ) * ‖h‖ := by
  have hcoord (k : Fin 9) : |phaseContactExactRoot k - phaseContactRootCenter k| ≤
      (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans phaseContactExactRoot_dist_le
  have hc (k : Fin 9) : |phaseContactRootCenter k| ≤ 1 :=
    (rootCenter_box k).trans (by norm_num)
  have hq (j : Fin 4) : |phaseContactExactRoot (phaseContactCosineCoordinate j)| ≤ 1 :=
    (abs_phaseContactExactRoot_cosine_lt_one j).le
  have hrem : ‖phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot h -
      rootCentralMatrix *ᵥ h‖ ≤ 16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖h‖ := by
    rw [rootCentralMatrix_mulVec]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact abs_phaseContactSecantAction_sub_diagonal_le (by norm_num) (norm_nonneg _)
      hc hq hq hcoord hcoord (fun k ↦ norm_le_pi_norm h k) i
  have he : (1 - rootPreconditioner * phaseContactJacobian phaseContactExactRoot) *ᵥ h =
      (1 - rootPreconditioner * rootCentralMatrix) *ᵥ h -
        rootPreconditioner *ᵥ (phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot h -
          rootCentralMatrix *ᵥ h) := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, phaseContactJacobian_mulVec]
    abel
  rw [he]
  calc
    _ ≤ ‖(1 - rootPreconditioner * rootCentralMatrix) *ᵥ h‖ +
        ‖rootPreconditioner *ᵥ (phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot h -
          rootCentralMatrix *ᵥ h)‖ := norm_sub_le _ _
    _ ≤ (1 / 4 : ℝ) * ‖h‖ + 22 * ‖phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot h -
        rootCentralMatrix *ᵥ h‖ := add_le_add
      (norm_matrix_mulVec_le (by norm_num) rootCentralMatrix_left_row _)
      (norm_matrix_mulVec_le (by norm_num) rootPreconditioner_row _)
    _ ≤ (1 / 4 : ℝ) * ‖h‖ + 22 * (16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖h‖) := by linarith
    _ ≤ _ := by nlinarith [norm_nonneg h]

/-- The exact contact geometry has a nonsingular linearization. Thus
its inverse determines a unique cost-normalized primal coefficient row. -/
theorem isUnit_phaseContactExactRoot_jacobian :
    IsUnit (phaseContactJacobian phaseContactExactRoot) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have h := rootJacobian_error_norm (x - y)
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    hxy, sub_sub_sub_cancel_right] at h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  linarith [norm_nonneg (x - y)]

/-- The exact contact linearization cannot shrink a vector by more than
the proved factor. This also controls its inverse without a numerical inverse oracle. -/
theorem norm_le_mul_norm_phaseContactExactRoot_jacobian (h : Fin 9 → ℝ) :
    ‖h‖ ≤ 44 * ‖phaseContactJacobian phaseContactExactRoot *ᵥ h‖ := by
  have he := rootJacobian_error_norm h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at he
  have hb := norm_matrix_mulVec_le (by norm_num : (0 : ℝ) ≤ 22) rootPreconditioner_row
    (phaseContactJacobian phaseContactExactRoot *ᵥ h)
  have ht := norm_le_norm_sub_add h (rootPreconditioner *ᵥ phaseContactJacobian phaseContactExactRoot *ᵥ h)
  linarith

private theorem rootJacobian_right_error_norm (h : Fin 9 → ℝ) :
    ‖(1 - phaseContactJacobian phaseContactExactRoot * rootPreconditioner) *ᵥ h‖ ≤
      (3 / 10 ^ 9 : ℝ) * ‖h‖ := by
  have hcoord (k : Fin 9) : |phaseContactExactRoot k - phaseContactRootCenter k| ≤
      (1 / 10 ^ 30 : ℝ) :=
    (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans phaseContactExactRoot_dist_le
  have hc (k : Fin 9) : |phaseContactRootCenter k| ≤ 1 :=
    (rootCenter_box k).trans (by norm_num)
  have hq (j : Fin 4) : |phaseContactExactRoot (phaseContactCosineCoordinate j)| ≤ 1 :=
    (abs_phaseContactExactRoot_cosine_lt_one j).le
  have hrem : ‖phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot (rootPreconditioner *ᵥ h) -
      rootCentralMatrix *ᵥ (rootPreconditioner *ᵥ h)‖ ≤
        16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖rootPreconditioner *ᵥ h‖ := by
    rw [rootCentralMatrix_mulVec]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact abs_phaseContactSecantAction_sub_diagonal_le (by norm_num) (norm_nonneg _)
      hc hq hq hcoord hcoord (fun k ↦ norm_le_pi_norm (rootPreconditioner *ᵥ h) k) i
  have he : (1 - phaseContactJacobian phaseContactExactRoot * rootPreconditioner) *ᵥ h =
      (1 - rootCentralMatrix * rootPreconditioner) *ᵥ h -
        (phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot (rootPreconditioner *ᵥ h) -
          rootCentralMatrix *ᵥ (rootPreconditioner *ᵥ h)) := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      phaseContactJacobian_mulVec]
    abel
  have hb := norm_matrix_mulVec_le (by norm_num : (0 : ℝ) ≤ 22) rootPreconditioner_row h
  rw [he]
  calc
    _ ≤ ‖(1 - rootCentralMatrix * rootPreconditioner) *ᵥ h‖ +
        ‖phaseContactSecantAction phaseContactExactRoot phaseContactExactRoot (rootPreconditioner *ᵥ h) -
          rootCentralMatrix *ᵥ (rootPreconditioner *ᵥ h)‖ := norm_sub_le _ _
    _ ≤ (1 / 10 ^ 9 : ℝ) * ‖h‖ +
        16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * ‖rootPreconditioner *ᵥ h‖ := add_le_add
      (norm_matrix_mulVec_le (by norm_num) rootCentralMatrix_right_row_small _) hrem
    _ ≤ (1 / 10 ^ 9 : ℝ) * ‖h‖ + 16 * (6 : ℝ) ^ 24 * (1 / 10 ^ 30) * (22 * ‖h‖) := by
      nlinarith
    _ ≤ _ := by nlinarith [norm_nonneg h]

/-- Every entry of the true inverse is close to the rational
preconditioner. In particular this can certify very small primal weights. -/
theorem abs_phaseContactExactRoot_inverse_sub_le (i k : Fin 9) :
    |(phaseContactJacobian phaseContactExactRoot)⁻¹ i k -
      (phaseContactRootPreconditionerQ i k : ℝ)| ≤ (132 / 10 ^ 9 : ℝ) := by
  let J := phaseContactJacobian phaseContactExactRoot
  let e : Fin 9 → ℝ := Pi.single k 1
  have hJ : J * J⁻¹ = 1 :=
    Matrix.mul_nonsing_inv J ((Matrix.isUnit_iff_isUnit_det J).mp isUnit_phaseContactExactRoot_jacobian)
  have he : J *ᵥ (J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e) = (1 - J * rootPreconditioner) *ᵥ e := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hlow := norm_le_mul_norm_phaseContactExactRoot_jacobian (J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e)
  change ‖J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e‖ ≤ 44 * ‖J *ᵥ (J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e)‖ at hlow
  rw [he] at hlow
  have hright := rootJacobian_right_error_norm e
  have hnorm : ‖e‖ = 1 := by simp only [e, Pi.norm_single, norm_one]
  rw [hnorm] at hright
  have hbound : ‖J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e‖ ≤ (132 / 10 ^ 9 : ℝ) := by linarith
  have h := (norm_le_pi_norm (J⁻¹ *ᵥ e - rootPreconditioner *ᵥ e) i).trans hbound
  simpa only [e, J, Matrix.mulVec_single_one, Matrix.col_apply, Pi.sub_apply,
    Real.norm_eq_abs, rootPreconditioner] using h

end

end RiemannGaussian
