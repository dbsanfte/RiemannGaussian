/-
The three private generic rank lemmas in this file are adapted from
Anthropic's `formal-math/zeta23` development.

Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/

import RiemannGaussian.EtaEnergyFiniteWindowBlock
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for finite eta zero-window blocks

This module adds the finite-dimensional rank estimates needed before an
inertia or rank--trace argument can be applied to the eta zero-window matrix.
The estimates concern the literal matrices already constructed from genuine
nontrivial zeta zeros and their analytic multiplicities.

Every individual outer-product summand has rank at most one.  Rank
subadditivity therefore bounds the full, critical-line, off-line real, and
off-line imaginary blocks by the cardinality of their indexing windows.  We
also prove that a nonnegative symmetric spectral window contains exactly its
critical-line zeros plus twice its upper zeros; reflection supplies the lower
copy.

The generic finite-sum rank argument follows the elementary linear-algebra
pattern used in Anthropic's Apache-2.0 `formal-math/zeta23` development.  The
theorems below specialize it independently to this project's actual eta
features and spectral-xi divisor.
-/

open Complex
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Rank is subadditive for square complex matrices. -/
theorem matrixRank_add_le
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-- The rank of a finite matrix sum is bounded by the sum of any pointwise
rank bounds. -/
theorem matrixRank_finsetSum_le
    {n α : Type*} [Fintype n] (s : Finset α)
    (f : α → Matrix n n ℂ) (bound : α → ℕ)
    (hbound : ∀ a ∈ s, (f a).rank ≤ bound a) :
    (∑ a ∈ s, f a).rank ≤ ∑ a ∈ s, bound a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (matrixRank_add_le _ _).trans
        (Nat.add_le_add
          (hbound a (Finset.mem_insert_self a s))
          (ih fun b hb ↦ hbound b (Finset.mem_insert_of_mem hb)))

/-- A scalar multiple of a complex outer product has rank at most one. -/
theorem matrixRank_smul_vecMulVec_le
    {n : Type*} [Fintype n] (c : ℂ) (w v : n → ℂ) :
    (c • Matrix.vecMulVec w v).rank ≤ 1 := by
  rw [← Matrix.smul_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-! ## Exact spectral-window cardinality -/

/-- A nonnegative symmetric spectral zero window consists of its
critical-line part together with equally large upper and lower parts. -/
theorem spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper
    {T : ℝ} (hT : 0 ≤ T) :
    (spectralZetaZeroWindow T).card =
      (spectralCriticalZetaZeroWindow T).card +
        2 * (spectralUpperZetaZeroWindow T).card := by
  have hsplit :=
    sum_spectralZetaZeroWindow_eq_upper_add_critical_add_lower
      (fun _ : NontrivialZetaZero ↦ (1 : ℕ)) T
  have hlower :=
    sum_spectralLowerZetaZeroWindow_eq_upper_conjugatePartner hT
      (fun _ : NontrivialZetaZero ↦ (1 : ℕ))
  simp only [← Finset.card_eq_sum_ones] at hsplit hlower
  omega

/-! ## Rank-one summation bounds for the actual eta blocks -/

/-- The complete eta block has rank no larger than the number of distinct
zeros in its finite spectral window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_rank_le_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).rank ≤
      (spectralZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 1) ?_).trans ?_
  · intro rho _hrho
    exact matrixRank_smul_vecMulVec_le
      (analyticZetaZeroMultiplicity rho : ℂ)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
  · simp

/-- The critical-line eta block has rank no larger than the number of
distinct critical-line zeros in its finite window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rank_le_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T).rank ≤
      (spectralCriticalZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 1) ?_).trans ?_
  · intro rho _hrho
    exact matrixRank_smul_vecMulVec_le
      (analyticZetaZeroMultiplicity rho : ℂ)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
  · simp

/-- The positive real off-line eta block has rank no larger than the number
of distinct zeros in the upper half of its finite spectral window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rank_le_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T).rank ≤
      (spectralUpperZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 1) ?_).trans ?_
  · intro rho _hrho
    simpa only [smul_smul] using
      matrixRank_smul_vecMulVec_le
        ((analyticZetaZeroMultiplicity rho : ℂ) * 2)
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
  · simp

/-- The positive imaginary off-line eta block has rank no larger than the
number of distinct zeros in the upper half of its finite spectral window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rank_le_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T).rank ≤
      (spectralUpperZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 1) ?_).trans ?_
  · intro rho _hrho
    simpa only [smul_smul] using
      matrixRank_smul_vecMulVec_le
        ((analyticZetaZeroMultiplicity rho : ℂ) * 2)
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
  · simp

/-- In a nonnegative symmetric window, the complete eta block rank is bounded
by the critical-line count plus twice the upper off-line count. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_rank_le_critical_add_two_mul_upper
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).rank ≤
      (spectralCriticalZetaZeroWindow T).card +
        2 * (spectralUpperZetaZeroWindow T).card := by
  rw [← spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT]
  exact pairedEtaTopPrefixFiniteZeroWindowBlock_rank_le_card cutoff T

end

end RiemannGaussian
