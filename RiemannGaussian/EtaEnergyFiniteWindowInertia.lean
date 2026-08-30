/-
The positive-index spectral-subspace argument in this file is adapted from
Anthropic's `formal-math/zeta23` development.

Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/

import RiemannGaussian.EtaEnergyFiniteWindowRank
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive-index bounds for finite eta zero-window blocks

This module supplies the minimal Hermitian inertia statement needed by the
finite eta matrix.  The positive index of a Hermitian matrix is defined as
the number of its strictly positive eigenvalues.  Using the positive spectral
subspace, Lean proves directly that

`posIndex (P - N) ≤ rank P`

whenever `P` and `N` are positive semidefinite.  This is then applied to the
literal eta decomposition: the positive part is the sum of the critical-line
and off-line-real blocks, while the off-line-imaginary block is subtracted.
Consequently the complete finite eta window has positive index at most

`#critical + #upper`.

This is an exact inertia bound for the actual analytic-multiplicity-weighted
spectral-xi divisor matrix.  It is not yet a trace or Frobenius estimate and
does not by itself control the open arithmetic leading current.
-/

open Matrix Finset Unitary
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

namespace HermitianInertia

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of a Hermitian matrix: the number of its strictly
positive eigenvalues, counted with spectral multiplicity. -/
def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

/-- For a positive-semidefinite matrix, the positive index equals its rank. -/
theorem posIndex_eq_rank_of_posSemidef {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) :
    posIndex hA.isHermitian = A.rank := by
  rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  exact ⟨fun h ↦ h.ne', fun h ↦ (hA.eigenvalues_nonneg i).lt_of_ne' h⟩

private def specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i ↦ (f (hA.eigenvalues i) : 𝕜)))

private theorem specMap_id {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

private theorem hermForm_specMap {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (specMap hA f *ᵥ x)) =
      ∑ i, f (hA.eigenvalues i) *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, Matrix.star_mulVec,
      show (star U)ᴴ = U from Matrix.conjTranspose_conjTranspose U]
  unfold specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) U, hsc,
    ← hc_def,
    show star c ⬝ᵥ
        (Matrix.diagonal (fun i ↦ (f (hA.eigenvalues i) : 𝕜)) *ᵥ c) =
      ∑ i, (f (hA.eigenvalues i) : 𝕜) *
        (starRingEnd 𝕜 (c i) * c i) by
      simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply,
        RCLike.star_def]
      exact Finset.sum_congr rfl fun i _ ↦ by ring]
  simp only [RCLike.conj_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show ((f (hA.eigenvalues i) : 𝕜) * (‖c i‖ : 𝕜) ^ 2 : 𝕜) =
      ((f (hA.eigenvalues i) * ‖c i‖ ^ 2 : ℝ) : 𝕜) by
        push_cast
        ring,
    RCLike.ofReal_re]

private theorem rank_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    (specMap hA f).rank = #{i | f (hA.eigenvalues i) ≠ 0} := by
  have hdet : IsUnit (hA.eigenvectorUnitary : Matrix n n 𝕜).det :=
    Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  have hdet' : IsUnit
      (star (hA.eigenvectorUnitary : Matrix n n 𝕜)).det := by
    rw [show star (hA.eigenvectorUnitary : Matrix n n 𝕜) =
        (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ from rfl,
      Matrix.det_conjTranspose]
    exact hdet.star
  unfold specMap
  rw [conjStarAlgAut_apply,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet,
    Matrix.rank_diagonal]
  simp only [ne_eq, RCLike.ofReal_eq_zero, Fintype.card_subtype]

private def hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Matrix n n 𝕜 :=
  specMap hA (·⁺)

private theorem rank_hermPosPart {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    (hermPosPart hA).rank = posIndex hA := by
  unfold hermPosPart posIndex
  rw [rank_specMap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero,
    not_le]

private def hermForm (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ (A *ᵥ x))

private def PosDefOn (A : Matrix n n 𝕜)
    (W : Submodule 𝕜 (n → 𝕜)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermForm A x

open Unitary in
private theorem posDefOn_range_hermPosPart {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    PosDefOn A (LinearMap.range (hermPosPart hA).mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set z := (hermPosPart hA).mulVecLin y with hz_def
  change z ≠ 0 at hne
  change 0 < hermForm A z
  set d := star U *ᵥ y with hd_def
  have hc_eq : star U *ᵥ z =
      fun i ↦ (((hA.eigenvalues i)⁺ : ℝ) : 𝕜) * d i := by
    have hz' : z = hermPosPart hA *ᵥ y := rfl
    rw [hz']
    unfold hermPosPart specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc,
      ← mul_assoc, star_mul_self_of_mem hA.eigenvectorUnitary.2,
      one_mul, ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [Matrix.mulVec, diagonal_dotProduct]
  have hformA : hermForm A z =
      ∑ i, hA.eigenvalues i * ((hA.eigenvalues i)⁺) ^ 2 *
        ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by rw [specMap_id]
    unfold hermForm
    rw [hAz, hermForm_specMap hA id z, hc_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [id_eq, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring
  rw [hformA]
  have hterm_nonneg : ∀ i,
      0 ≤ hA.eigenvalues i * ((hA.eigenvalues i)⁺) ^ 2 *
        ‖d i‖ ^ 2 := by
    intro i
    rcases le_or_gt (hA.eigenvalues i) 0 with h | h
    · simp [posPart_eq_zero.mpr h]
    · exact mul_nonneg (mul_nonneg h.le (sq_nonneg _)) (sq_nonneg _)
  refine Finset.sum_pos' (fun i _ ↦ hterm_nonneg i) ?_
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have hmul : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [mul_star_self_of_mem hA.eigenvectorUnitary.2, Matrix.one_mulVec,
      Matrix.one_mulVec] at hmul
  have hc_ne :
      (fun i ↦ (((hA.eigenvalues i)⁺ : ℝ) : 𝕜) * d i) ≠ 0 := by
    rw [← hc_eq]
    intro h
    exact hne (hUinj (h.trans (Matrix.mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : 0 < hA.eigenvalues i := by
    by_contra h
    exact hi.1 (posPart_eq_zero.mpr (not_lt.mp h))
  have hdi : (0 : ℝ) < ‖d i‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hi.2) 2
  have hpp : (0 : ℝ) < ((hA.eigenvalues i)⁺) ^ 2 := by
    rw [posPart_eq_self.mpr hevi.le]
    exact pow_pos hevi 2
  exact mul_pos (mul_pos hevi hpp) hdi

private theorem finrank_range_hermPosPart {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    Module.finrank 𝕜
        (LinearMap.range (hermPosPart hA).mulVecLin) = posIndex hA := by
  rw [← rank_hermPosPart hA]
  rfl

/-- The positive index is unchanged when the underlying Hermitian matrices
are equal. -/
theorem posIndex_congr {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    posIndex hA = posIndex hB := by
  subst B
  rfl

/-- If `P` and `N` are positive semidefinite, then the number of positive
eigenvalues of `P - N` is at most the rank of `P`. -/
theorem posIndex_sub_le_rank {P N : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hN : N.PosSemidef) :
    posIndex (hP.isHermitian.sub hN.isHermitian) ≤ P.rank := by
  let hA : (P - N).IsHermitian := hP.isHermitian.sub hN.isHermitian
  let Vp : Submodule 𝕜 (n → 𝕜) :=
    LinearMap.range (hermPosPart hA).mulVecLin
  have hdim : Module.finrank 𝕜 Vp = posIndex hA :=
    finrank_range_hermPosPart hA
  have hpos : PosDefOn (P - N) Vp :=
    posDefOn_range_hermPosPart hA
  let LP : (n → 𝕜) →ₗ[𝕜] (n → 𝕜) := P.mulVecLin
  have hinj : Function.Injective (LP.domRestrict Vp) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : P *ᵥ x = 0 := hxL
    change (⟨x, hxV⟩ : Vp) = 0
    by_contra hne
    have hne' : x ≠ 0 := fun h ↦ hne (Subtype.ext h)
    have hpositive : 0 < hermForm (P - N) x := hpos x hxV hne'
    have hPzero : hermForm P x = 0 := by
      unfold hermForm
      rw [hxL']
      simp
    have hNnonneg : 0 ≤ hermForm N x := hN.re_dotProduct_nonneg x
    have hsub : hermForm (P - N) x = hermForm P x - hermForm N x := by
      unfold hermForm
      simp [Matrix.sub_mulVec, dotProduct_sub, map_sub]
    rw [hsub, hPzero] at hpositive
    linarith
  change posIndex hA ≤ P.rank
  calc
    posIndex hA = Module.finrank 𝕜 Vp := hdim.symm
    _ = Module.finrank 𝕜
        (LinearMap.range (LP.domRestrict Vp)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range LP) := by
      apply Submodule.finrank_mono
      rintro y ⟨⟨x, hxV⟩, rfl⟩
      exact ⟨x, rfl⟩
    _ = P.rank := rfl

end HermitianInertia

private theorem complexMatrixRank_add_le
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-! ## Eta-specific inertia -/

/-- The off-line hyperbolic eta block has positive index at most the number
of represented upper spectral zeros. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_posIndex_le_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.posIndex
        ((pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
            cutoff T).isHermitian.sub
          (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef
            cutoff T).isHermitian) ≤
      (spectralUpperZetaZeroWindow T).card := by
  classical
  exact
    (HermitianInertia.posIndex_sub_le_rank
      (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef cutoff T)
      (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef cutoff T)).trans
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rank_le_card
          cutoff T)

/-- The complete finite eta window has positive index at most its
critical-line zero count plus its upper off-line zero count. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_posIndex_le_critical_add_upper
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    HermitianInertia.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) ≤
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  classical
  let onLine := pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T
  let offReal := pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T
  let offImag := pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T
  let positivePart := onLine + offReal
  have hOnLine : onLine.PosSemidef :=
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T
  have hOffReal : offReal.PosSemidef :=
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef cutoff T
  have hOffImag : offImag.PosSemidef :=
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef cutoff T
  have hPositivePart : positivePart.PosSemidef := hOnLine.add hOffReal
  have hdecomp :
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T =
        positivePart - offImag := by
    rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT]
    simp only [positivePart, onLine, offReal, offImag]
    abel
  calc
    HermitianInertia.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) =
      HermitianInertia.posIndex
        (hPositivePart.isHermitian.sub hOffImag.isHermitian) :=
      HermitianInertia.posIndex_congr _ _ hdecomp
    _ ≤ positivePart.rank :=
      HermitianInertia.posIndex_sub_le_rank hPositivePart hOffImag
    _ ≤ onLine.rank + offReal.rank := complexMatrixRank_add_le _ _
    _ ≤ (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card :=
      Nat.add_le_add
        (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rank_le_card cutoff T)
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rank_le_card cutoff T)

end

end RiemannGaussian
