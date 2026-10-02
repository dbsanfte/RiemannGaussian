/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszContinuumCascade

/-!
# The signed free-coordinate cancellation used by the geometry detector

An unused Boolean coordinate cancels a complete signed cube exactly.
Consequently a signed incidence monomial vanishes unless it involves
every free coordinate. The result covers arbitrary low-degree incidence
polynomials, with no shape or prime-count family assumed.

The last theorem retains a signed discrepancy after this cancellation.
It is a finite-pair floor criterion, not a native prime-inventory bound.
Hard masks, varying arithmetic weights and missing partners must enter
that discrepancy; they cannot inherit the unweighted cancellation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSignedCubeGeometry

/-- The complete cube keeps every original subset parity. -/
def signedCube {ι : Type*} (S : Finset ι) (F : Finset ι → ℂ) : ℂ :=
  ∑ A ∈ S.powerset, (-1 : ℂ)^A.card * F A

/-- Exact pairing across one coordinate, before any real part or norm. -/
theorem signedCube_insert {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : Finset ι → ℂ) {i : ι} (hi : i ∉ S) :
    signedCube (insert i S) F =
      ∑ A ∈ S.powerset, (-1 : ℂ)^A.card * (F A-F (insert i A)) := by
  unfold signedCube
  rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.mp hA h)
  rw [Finset.card_insert_of_notMem hiA,pow_succ]
  ring

/-- One genuinely unused coordinate suffices; no countwise estimate is
needed. An arithmetic weight depending on that coordinate fails the premise. -/
theorem signedCube_eq_zero_of_free_coordinate {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : Finset ι → ℂ) {i : ι} (hi : i ∈ S)
    (hF : ∀ A ∈ (S.erase i).powerset, F (insert i A)=F A) :
    signedCube S F = 0 := by
  rw [← Finset.insert_erase hi,signedCube_insert _ _ (Finset.notMem_erase _ _)]
  apply Finset.sum_eq_zero
  intro A hA
  rw [hF A hA,sub_self,mul_zero]

/-- Signed incidence moments of degree below the free dimension vanish.
This includes all first and second moments on a cube of dimension >=3. -/
theorem signedCube_monomial_eq_zero {ι : Type*} [DecidableEq ι]
    (S B : Finset ι) (hcard : B.card < S.card) (c : ℂ) :
    signedCube S (fun A => if B ⊆ A then c else 0) = 0 := by
  obtain ⟨i,hiS,hiB⟩ : ∃ i ∈ S,i ∉ B := by
    by_contra h
    have hs : S ⊆ B := by
      intro i hi
      by_contra hn
      exact h ⟨i,hi,hn⟩
    exact (not_le_of_gt hcard) (Finset.card_le_card hs)
  apply signedCube_eq_zero_of_free_coordinate S _ hiS
  intro A _
  have he : B ⊆ insert i A ↔ B ⊆ A := by
    constructor
    · intro h b hb
      rcases Finset.mem_insert.mp (h hb) with he | ha
      · exact False.elim (hiB (he ▸ hb))
      · exact ha
    · intro h b hb
      exact Finset.mem_insert_of_mem (h hb)
  simp only [he]

/-- An arbitrary signed polynomial below the free dimension cancels
jointly. The coefficient array can be complex and need not be positive. -/
theorem signedCube_polynomial_eq_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (c : Finset ι → ℂ)
    (hdegree : ∀ B ∈ T,B.card < S.card) :
    signedCube S (fun A => ∑ B ∈ T,if B ⊆ A then c B else 0) = 0 := by
  unfold signedCube
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro B hB
  exact signedCube_monomial_eq_zero S B (hdegree B hB) (c B)

/-- The signed pair discrepancies alone determine the one-sided cost.
The actual membership, weights and phase belong inside F. -/
theorem signedCube_real_floor_of_pairs {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : Finset ι → ℂ) (cost : Finset ι → ℝ)
    {i : ι} (hi : i ∉ S)
    (hcost : ∀ A ∈ S.powerset,
      -cost A ≤ (((-1 : ℂ)^A.card)*(F A-F (insert i A))).re) :
    -(∑ A ∈ S.powerset,cost A) ≤ (signedCube (insert i S) F).re := by
  rw [signedCube_insert S F hi,Complex.re_sum,← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum hcost

end RiemannGaussian.ZetaRieszSignedCubeGeometry
