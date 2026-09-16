/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszArithmeticCells
import RiemannGaussian.ZetaRieszHeadOrders
import RiemannGaussian.ZetaRieszLowerDegreeBounds

/-!
# A growing composite-cofactor part of the exact cells

Saturation kills the large-prime end of a small composite cofactor.
Its remaining products lie in a paid logarithmic window. The estimates
below keep the complete original polynomial and signed arithmetic carrier.
-/

namespace RiemannGaussian.ZetaRieszSmallCompositeCells
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells ZetaRieszArithmeticCells
open ZetaRieszConditionedEnergy ZetaRieszCentralWindow

/-- Entire owner fibres with composite cofactor at most exp(N/10).
The length test records the precise saturation requirement at early orders. -/
def smallCompositeBand (L : ℝ) (N : ℕ) : Finset ℕ :=
  (arithmeticBand N).filter (fun m =>
    ¬ (ownerCofactor m).Prime ∧ Real.log (ownerCofactor m) ≤ (N : ℝ) / 10 ∧
      Real.log (ownerCofactor m) ≤ L)

/-- Nonzero original coefficients force the owner prime below the common
cutoff once the composite cofactor is saturated. -/
theorem owner_log_lt_length {L : ℝ} {N m : ℕ} (hm : m ∈ smallCompositeBand L N)
    (hc : SquarefreeVaughanLogSource.coefficient L m ≠ 0) : Real.log (largestPrime m) < L := by
  obtain ⟨hband, hnp, _, hL⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hprod, hsf, _, hne, hnot⟩ := arithmetic_owner_factorization hband
  by_contra h
  have hz := ZetaRieszFixedCofactor.coefficient_prime_mul_eq_zero_of_large
    hsf hne hnp hp hnot hL (le_of_not_gt h)
  rw [hprod] at hz
  exact hc hz

/-- The whole exponentially growing composite-owner range falls in the
existing lower logarithmic window whenever its coefficient is nonzero. -/
theorem smallComposite_log_le {u : ℝ} (hu : 1 / 2 ≤ u) {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ smallCompositeBand (SquarefreeVaughanLogSource.length u N) N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m ≠ 0) :
    Real.log m ≤ (3 / 2 : ℝ) * N := by
  have hpL := owner_log_lt_length hm hc
  obtain ⟨hband, _, hn, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hprod, _, hn0, _, _⟩ := arithmetic_owner_factorization hband
  have hlog : Real.log m = Real.log (largestPrime m) + Real.log (ownerCofactor m) := by
    calc
      Real.log m = Real.log (largestPrime m * ownerCofactor m : ℕ) :=
        congrArg (fun a : ℕ => Real.log a) hprod.symm
      _ = _ := by rw [Nat.cast_mul, Real.log_mul
        (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hn0)]
  have hlength := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have htwo : 2 * Real.log 2 + 1 / 10 ≤ (3 / 2 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg (α := ℝ) N)
  rw [hlog]
  nlinarith

/-- Arbitrary bounded complex weights remain allowed on the entire
small-composite-owner class. All arithmetic coefficient costs are paid
by the original majorant rather than a growing cofactor-count factor. -/
theorem norm_smallComposite_sum_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 2 ≤ N)
    (hL : L = SquarefreeVaughanLogSource.length u N)
    (heta : ∀ m ∈ smallCompositeBand L N, ‖eta m‖ ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) * ∑ m ∈ smallCompositeBand L N,
      eta m * bandWeight L P N t m‖ ≤
        centralLowerRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256)) := by
  subst L
  let S := (smallCompositeBand (SquarefreeVaughanLogSource.length u N) N).filter
    (fun m => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m ≠ 0)
  have he : (∑ m ∈ smallCompositeBand (SquarefreeVaughanLogSource.length u N) N,
      eta m * bandWeight (SquarefreeVaughanLogSource.length u N) P N t m) =
      ∑ m ∈ S, (eta m * SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) m) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) m := by
    rw [show S = _ from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    rw [bandWeight, if_pos hb]
    by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m = 0
    · simp [hc]
    · simp only [if_pos hc, mul_assoc]
  rw [he]
  refine norm_lower_central_sum_le S _ ?_ P N t (by linarith) huh ?_
  · intro m hm
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hm
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (heta m hm) (norm_nonneg _)).trans
      (by simpa only [one_mul] using (SquarefreeVaughanLogSource.norm_coefficient_le
        (SquarefreeVaughanLogSource.length_pos u N) m))
  · intro m hm
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    exact smallComposite_log_le hu hN hm hc

/-- The new growing cofactor estimate controls the complete absolute
mass, not just a fortuitously cancelling sum. It therefore survives every
later selection or bounded phase mask without an extra counting cost. -/
theorem smallComposite_mass_le (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 2 ≤ N) :
    u ^ (N + 1) * ∑ m ∈ smallCompositeBand (SquarefreeVaughanLogSource.length u N) N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
        centralLowerRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256)) := by
  let w := bandWeight (SquarefreeVaughanLogSource.length u N) P N t
  let eta : ℕ → ℂ := fun m => (‖w m‖ : ℂ) / w m
  have heta (m : ℕ) : ‖eta m‖ ≤ 1 := by
    dsimp [eta]
    by_cases hw : w m = 0
    · simp [hw]
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hw)]
  have he (m : ℕ) : eta m * w m = (‖w m‖ : ℂ) := by
    by_cases hw : w m = 0
    · simp [hw]
    · exact div_mul_cancel₀ _ hw
  have h := norm_smallComposite_sum_le (SquarefreeVaughanLogSource.length u N)
    P N t eta hu huh hN rfl (fun m _ => heta m)
  change ‖(u : ℂ) ^ (N + 1) * ∑ m ∈ smallCompositeBand
    (SquarefreeVaughanLogSource.length u N) N, eta m * w m‖ ≤ _ at h
  simp_rw [he] at h
  rw [← Complex.ofReal_sum, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ u by linarith), Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h

/-- The simple exponentially growing cofactor class does not depend on
the physical length, height, polynomial filter, or choice of phase mask. -/
def smallOwnerBand (N : ℕ) : Finset ℕ :=
  (arithmeticBand N).filter (fun m =>
    ¬ (ownerCofactor m).Prime ∧ Real.log (ownerCofactor m) ≤ (N : ℝ) / 10)

/-- At all sufficiently large orders the physical cutoff automatically
saturates every cofactor up to exp(N/10); no starting order is invented. -/
theorem eventually_smallCompositeBand_eq {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      smallCompositeBand (SquarefreeVaughanLogSource.length u N) N = smallOwnerBand N := by
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 2 / 3) huh] with N hL
  ext m
  simp only [smallCompositeBand, smallOwnerBand, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The entire exponentially growing composite-owner class has an
independent geometric mass bound, uniformly even for moving heights. -/
theorem eventually_smallOwner_mass_le (P : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      u ^ (N + 1) * ∑ m ∈ smallOwnerBand N,
        ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
          centralLowerRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256)) := by
  filter_upwards [eventually_smallCompositeBand_eq hu huh, eventually_ge_atTop 2] with N he hN
  intro t
  rw [← he]
  exact smallComposite_mass_le P N t hu huh hN

/-- The full absolute allowance tends to zero for every fixed complex
polynomial and arbitrary sequence of heights, with no zero hypothesis. -/
theorem tendsto_smallOwner_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ smallOwnerBand N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => mul_nonneg
    (pow_nonneg (by linarith : 0 ≤ u) _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))))
    ((eventually_smallOwner_mass_le P hu huh).mono (fun N hN => hN (t N)))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ centralLowerRate by
      unfold centralLowerRate; positivity) centralLowerRate_lt_one).mul_const
        (u * ZetaArithmeticLogWindow.tiltConstant P (2 / 3) (257 / 256))

/-- The growing deletion consists of whole complete prime intervals,
selected by their owner cofactor alone. -/
def smallOwnerCells (L : ℝ) (N : ℕ) : Finset (ℕ × Finset ℕ) :=
  (arithmeticCells L N).filter (fun K => ¬ K.1.Prime ∧ Real.log K.1 ≤ (N : ℝ) / 10)

/-- A selected cell has no partially deleted prime fibre. -/
theorem smallOwnerCell_eq_fibre (L : ℝ) (N : ℕ) {K : ℕ × Finset ℕ}
    (hK : K ∈ smallOwnerCells L N) :
    arithmeticCell L N K = (smallOwnerBand N).filter (fun m => originalCellKey L m = K) := by
  obtain ⟨_, hprop⟩ := Finset.mem_filter.mp hK
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hkey⟩ := Finset.mem_filter.mp hm
    have hp : ¬ (ownerCofactor m).Prime ∧ Real.log (ownerCofactor m) ≤ (N : ℝ) / 10 := by
      change ¬ (originalCellKey L m).1.Prime ∧ Real.log (originalCellKey L m).1 ≤ (N : ℝ) / 10
      rw [hkey]
      exact hprop
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm, hp⟩, hkey⟩
  · intro hm
    obtain ⟨hm, hkey⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, hkey⟩

/-- Whole-cell deletion partitions every original small-cofactor atom
exactly once, for both signed sums and nonnegative norm costs. -/
theorem sum_smallOwner_fibres {α : Type*} [AddCommMonoid α] (L : ℝ) (N : ℕ) (f : ℕ → α) :
    (∑ K ∈ smallOwnerCells L N, ∑ m ∈ arithmeticCell L N K, f m) =
      ∑ m ∈ smallOwnerBand N, f m := by
  calc
    _ = ∑ K ∈ smallOwnerCells L N,
        ∑ m ∈ (smallOwnerBand N).filter (fun m => originalCellKey L m = K), f m := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [smallOwnerCell_eq_fibre L N hK]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro m hm
      obtain ⟨hm, hprop⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hprop⟩

/-- Summing cell norms in the deleted range costs no more than its
already paid full absolute arithmetic mass. -/
theorem smallOwner_cell_mass_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∑ K ∈ smallOwnerCells L N, ‖arithmeticCellResponse L P N t K‖) ≤
      ∑ m ∈ smallOwnerBand N, ‖bandWeight L P N t m‖ := by
  simp_rw [arithmeticCellResponse_eq_sum]
  exact (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)).trans_eq
    (sum_smallOwner_fibres L N (fun m => ‖bandWeight L P N t m‖))

/-- The absolute cost of all deleted cells vanishes, uniformly in moving
height. Subsequent whole-cell cycles need no further allowance for them. -/
theorem tendsto_smallOwner_cell_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => u ^ (N + 1) *
      ∑ K ∈ smallOwnerCells (SquarefreeVaughanLogSource.length u N) N,
        ‖arithmeticCellResponse (SquarefreeVaughanLogSource.length u N) P N (t N) K‖)
      atTop (nhds 0) := by
  apply squeeze_zero (fun N => mul_nonneg (pow_nonneg (by linarith : 0 ≤ u) _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (fun N => mul_le_mul_of_nonneg_left (smallOwner_cell_mass_le _ P N (t N))
      (pow_nonneg (by linarith : 0 ≤ u) _)) (tendsto_smallOwner_mass P t hu huh)

/-- The remaining cells keep every prime cofactor and only composite
cofactors whose logarithm exceeds N/10. -/
def remainingCells (L : ℝ) (N : ℕ) : Finset (ℕ × Finset ℕ) :=
  arithmeticCells L N \ smallOwnerCells L N

/-- The exact remaining arithmetic obstruction has this explicit
cofactor description; all cell signs and both prime moments remain. -/
theorem remainingCells_support (L : ℝ) (N : ℕ) {K : ℕ × Finset ℕ}
    (hK : K ∈ remainingCells L N) :
    K ∈ arithmeticCells L N ∧ (K.1.Prime ∨ (N : ℝ) / 10 < Real.log K.1) := by
  obtain ⟨hK, hnot⟩ := Finset.mem_sdiff.mp hK
  refine ⟨hK, ?_⟩
  by_cases hp : K.1.Prime
  · exact Or.inl hp
  · right
    by_contra hlog
    exact hnot (Finset.mem_filter.mpr ⟨hK, hp, le_of_not_gt hlog⟩)

/-- Splitting the full carrier loses only the independently paid class;
no artificial completion or prime-series boundary is introduced. -/
theorem actual_band_eq_small_add_remaining (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      (∑ K ∈ smallOwnerCells L N, arithmeticCellResponse L P N t K) +
        ∑ K ∈ remainingCells L N, arithmeticCellResponse L P N t K := by
  rw [actual_band_eq_arithmetic_cells]
  have h := Finset.sum_sdiff (show smallOwnerCells L N ⊆ arithmeticCells L N from
    Finset.filter_subset _ _) (f := arithmeticCellResponse L P N t)
  simpa only [remainingCells, add_comm] using h.symm

/-- The small-cell signed response vanishes because its entire absolute
mass has already been controlled, independently of its cancellations. -/
theorem tendsto_smallOwner_cell_response (P : Polynomial ℂ) (t : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ K ∈ smallOwnerCells (SquarefreeVaughanLogSource.length u N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length u N) P N (t N) K)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (fun N => ?_) (tendsto_smallOwner_cell_mass P t hu huh)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ u by linarith)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (by linarith : 0 ≤ u) _)

/-- In the stated source-radius range the full negative multiplicity
source is carried by semiprime owners and exponentially larger composite
owners alone. No source exposure or simplicity assumption is added. -/
theorem tendsto_remaining_cell_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ remainingCells (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 ≤ (3 / 2 - rho.1.re : ℝ) := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hsource := tendsto_arithmetic_cell_source rho hrho
  have hsmall := tendsto_smallOwner_cell_response (zetaRightHalfPoleJetFilter rho hrho)
    (fun _ => rho.1.im) hu huh
  have h := hsource.sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← actual_band_eq_arithmetic_cells, actual_band_eq_small_add_remaining]
  ring

end
end RiemannGaussian.ZetaRieszSmallCompositeCells
