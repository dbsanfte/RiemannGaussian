/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerMass

/-!
# Retaining the full source after growing owner deletion

These independent component estimates retain the original full filter,
all heights and the actual floor-defined cutoff. They preserve the full
pole-jet source but do not bound the remaining semiprime and large-owner
signed response or prove a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszOwnerCells
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells ZetaRieszArithmeticCells
open ZetaRieszConditionedEnergy ZetaArithmeticLogWindow
open ZetaRieszOwnerWindow
open ZetaRieszOwnerMass

/-- The deletion selects complete prime cells by their owner cofactor
alone, preserving all internal prime and filter correlations. -/
def ownerCells (δ L : ℝ) (N : ℕ) : Finset (ℕ × Finset ℕ) :=
  (arithmeticCells L N).filter (fun K => ¬ K.1.Prime ∧ Real.log K.1 ≤ δ * N)

theorem ownerCell_eq_fibre (δ L : ℝ) (N : ℕ) {K : ℕ × Finset ℕ}
    (hK : K ∈ ownerCells δ L N) :
    arithmeticCell L N K = (ownerBand δ N).filter (fun m => originalCellKey L m = K) := by
  obtain ⟨_, hprop⟩ := Finset.mem_filter.mp hK
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hkey⟩ := Finset.mem_filter.mp hm
    have hp : ¬ (ownerCofactor m).Prime ∧ Real.log (ownerCofactor m) ≤ δ * N := by
      change ¬ (originalCellKey L m).1.Prime ∧ Real.log (originalCellKey L m).1 ≤ δ * N
      rw [hkey]
      exact hprop
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm, hp⟩, hkey⟩
  · intro hm
    obtain ⟨hm, hkey⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, hkey⟩

theorem sum_owner_fibres {α : Type*} [AddCommMonoid α] (δ L : ℝ) (N : ℕ) (f : ℕ → α) :
    (∑ K ∈ ownerCells δ L N, ∑ m ∈ arithmeticCell L N K, f m) =
      ∑ m ∈ ownerBand δ N, f m := by
  calc
    _ = ∑ K ∈ ownerCells δ L N,
        ∑ m ∈ (ownerBand δ N).filter (fun m => originalCellKey L m = K), f m := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [ownerCell_eq_fibre δ L N hK]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro m hm
      obtain ⟨hm, hprop⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hprop⟩

/-- The aggregate norm cost of the selected whole cells is bounded by
the same absolute arithmetic mass, independently of any cycle mechanism. -/
theorem owner_cell_mass_le (δ L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∑ K ∈ ownerCells δ L N, ‖arithmeticCellResponse L P N t K‖) ≤
      ∑ m ∈ ownerBand δ N, ‖bandWeight L P N t m‖ := by
  simp_rw [arithmeticCellResponse_eq_sum]
  exact (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)).trans_eq
    (sum_owner_fibres δ L N (fun m => ‖bandWeight L P N t m‖))

/-- The new component allowance remains valid after any subdivision
into the actual complete prime cells. -/
theorem tendsto_owner_cell_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u δ : ℝ} (hu : 0 ≤ u)
    (hmass : Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0)) :
    Tendsto (fun N => u ^ (N + 1) * ∑ K ∈ ownerCells δ (SquarefreeVaughanLogSource.length u N) N,
      ‖arithmeticCellResponse (SquarefreeVaughanLogSource.length u N) P N (t N) K‖)
      atTop (nhds 0) := by
  apply squeeze_zero (fun N => mul_nonneg (pow_nonneg hu _)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (fun N => mul_le_mul_of_nonneg_left (owner_cell_mass_le δ _ P N (t N)) (pow_nonneg hu _)) hmass

/-- The exact signed contribution vanishes as a consequence of the
independent absolute-mass estimate, with all cell phases kept intact. -/
theorem tendsto_owner_cell_response (P : Polynomial ℂ) (t : ℕ → ℝ) {u δ : ℝ} (hu : 0 ≤ u)
    (hmass : Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0)) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ K ∈ ownerCells δ (SquarefreeVaughanLogSource.length u N) N,
      arithmeticCellResponse (SquarefreeVaughanLogSource.length u N) P N (t N) K)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (fun N => ?_) (tendsto_owner_cell_mass P t hu hmass)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hu _)

/-- Retain all prime cofactors and every composite cofactor above the
proved growth schedule. These cells must still be estimated jointly. -/
def remainingCells (δ L : ℝ) (N : ℕ) : Finset (ℕ × Finset ℕ) :=
  arithmeticCells L N \ ownerCells δ L N

theorem remainingCells_support (δ L : ℝ) (N : ℕ) {K : ℕ × Finset ℕ}
    (hK : K ∈ remainingCells δ L N) :
    K ∈ arithmeticCells L N ∧ (K.1.Prime ∨ δ * N < Real.log K.1) := by
  obtain ⟨hK, hnot⟩ := Finset.mem_sdiff.mp hK
  refine ⟨hK, ?_⟩
  by_cases hp : K.1.Prime
  · exact Or.inl hp
  · right
    by_contra hlog
    exact hnot (Finset.mem_filter.mpr ⟨hK, hp, le_of_not_gt hlog⟩)

theorem actual_band_eq_owner_add_remaining (δ L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      (∑ K ∈ ownerCells δ L N, arithmeticCellResponse L P N t K) +
        ∑ K ∈ remainingCells δ L N, arithmeticCellResponse L P N t K := by
  rw [actual_band_eq_arithmetic_cells]
  have h := Finset.sum_sdiff (show ownerCells δ L N ⊆ arithmeticCells L N from
    Finset.filter_subset _ _) (f := arithmeticCellResponse L P N t)
  simpa only [remainingCells, add_comm] using h.symm

/-- The full pole-jet source survives any independently paid owner
deletion. The zero need not be simple, exposed, or globally rightmost. -/
theorem tendsto_remaining_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (δ : ℝ)
    (hmass : Tendsto (fun N => (3 / 2 - rho.1.re) ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      ‖bandWeight (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im m‖) atTop (nhds 0)) :
    Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ remainingCells δ (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 ≤ (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hsource := tendsto_arithmetic_cell_source rho hrho
  have hsmall := tendsto_owner_cell_response (zetaRightHalfPoleJetFilter rho hrho)
    (fun _ => rho.1.im) hu hmass
  have h := hsource.sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← actual_band_eq_arithmetic_cells, actual_band_eq_owner_add_remaining δ]
  ring

/-- At every right-half zero except the single scalar contact, an
exponentially growing class of composite owners can be deleted with the
entire negative multiplicity source intact. This does not bound the
remaining cells or establish a zero-free region. -/
theorem exists_remaining_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (hne : 3 / 2 - rho.1.re ≠ Real.exp (-(1 / 2 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < -2 * Real.log (3 / 2 - rho.1.re) ∧
      Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ∑ K ∈ remainingCells δ (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
          arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
            (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
        atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  obtain ⟨δ, hδ, hδu, hmass⟩ := exists_growing_owner_mass_decay hu hu1 hne
  exact ⟨δ, hδ, hδu, tendsto_remaining_source rho hrho δ
    (hmass (zetaRightHalfPoleJetFilter rho hrho) (fun _ => rho.1.im))⟩

end
end RiemannGaussian.ZetaRieszOwnerCells
