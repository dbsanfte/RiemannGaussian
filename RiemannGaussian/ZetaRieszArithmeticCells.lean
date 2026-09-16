/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeIntervals

/-!
# The full carrier as fixed arithmetic prime intervals

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszArithmeticCells
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCells
open ZetaRieszCellOrders
open ZetaRieszOwnedCells
open ZetaRieszPrimeIntervals

/-- The arithmetic support depends on the original band and squarefree
factorization alone, independently of every filter and ordinate. -/
def arithmeticBand (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (fun m => Squarefree m ∧ 2 ≤ m.primeFactors.card)

/-- Every nonzero original atom belongs to the fixed arithmetic support. -/
theorem activeOriginalBand_subset_arithmeticBand (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ZetaRieszWholeWindow.activeOriginalBand L P N t ⊆ arithmeticBand N := by
  intro m hm
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,
    ZetaRieszWholeWindow.activeOriginalBand_support L P N t hm⟩

/-- All canonical owner properties follow from the fixed arithmetic
support, even at original atoms whose complex filter value is zero. -/
theorem arithmetic_owner_factorization {N m : ℕ} (hm : m ∈ arithmeticBand N) :
    (largestPrime m).Prime ∧ largestPrime m * ownerCofactor m = m ∧
      Squarefree (ownerCofactor m) ∧ ownerCofactor m ≠ 0 ∧ ownerCofactor m ≠ 1 ∧
      ¬ largestPrime m ∣ ownerCofactor m := by
  obtain ⟨_, hsf, hcard⟩ := Finset.mem_filter.mp hm
  have hp := largestPrime_mem_of_two hcard
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hprod : largestPrime m * ownerCofactor m = m := by
    rw [ownerCofactor, Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  have hsfprod : Squarefree (largestPrime m * ownerCofactor m) := by rw [hprod]; exact hsf
  have hg := hsfprod.of_mul_right
  have hg1 : ownerCofactor m ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hprod
    rw [← hprod, hpprime.primeFactors, Finset.card_singleton] at hcard
    omega
  exact ⟨hpprime, hprod, hg, hg.ne_zero, hg1,
    hpprime.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsfprod)⟩

/-- The owner prime lies strictly above every cofactor prime; squarefree
support discharges the strictness, not a chosen exclusion mask. -/
theorem owner_above_cofactor {N m : ℕ} (hm : m ∈ arithmeticBand N) :
    ∀ q ∈ (ownerCofactor m).primeFactors, q < largestPrime m := by
  obtain ⟨_, hprod, _, _, _, hnot⟩ := arithmetic_owner_factorization hm
  obtain ⟨_, hsf, hcard⟩ := Finset.mem_filter.mp hm
  have hne : m.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  intro q hq
  have hdiv : ownerCofactor m ∣ m := by
    exact ⟨largestPrime m, by simpa only [Nat.mul_comm] using hprod.symm⟩
  have hqm := Nat.primeFactors_mono hdiv hsf.ne_zero hq
  have hle : q ≤ largestPrime m := by
    rw [largestPrime, dif_pos hne]
    exact Finset.le_max' _ q hqm
  have hneq : q ≠ largestPrime m := by
    intro he
    exact hnot (he ▸ Nat.dvd_of_mem_primeFactors hq)
  exact lt_of_le_of_ne hle hneq

/-- The fixed arithmetic cell no longer depends on the complex filter
or height; both remain solely in its actual signed response. -/
def arithmeticCell (L : ℝ) (N : ℕ) (K : ℕ × Finset ℕ) : Finset ℕ :=
  (arithmeticBand N).filter (fun m => originalCellKey L m = K)

/-- An inserted prime above a nonunit squarefree cofactor gives a
squarefree composite original product whenever its band test succeeds. -/
theorem prime_product_mem_arithmeticBand (N : ℕ) {p n : ℕ}
    (hp : p.Prime) (hn : Squarefree n) (hn1 : n ≠ 1)
    (hmax : ∀ q ∈ n.primeFactors, q < p) (hb : p * n ∈ zetaPrimeLogBand N) :
    p * n ∈ arithmeticBand N := by
  have hnot := prime_not_dvd_of_above hp hn.ne_zero hmax
  have hsf : Squarefree (p * n) := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hnot, hp.squarefree, hn⟩
  have hncard : 1 ≤ n.primeFactors.card := by
    have hngt : 1 < n := by have := hn.ne_zero; omega
    have hne := Nat.nonempty_primeFactors.mpr hngt
    have hpos := Finset.card_pos.mpr hne
    omega
  have hpnot : p ∉ n.primeFactors := fun h => hnot (Nat.dvd_of_mem_primeFactors h)
  refine Finset.mem_filter.mpr ⟨hb, hsf, ?_⟩
  rw [Nat.primeFactors_mul hp.ne_zero hn.ne_zero, hp.primeFactors,
    Finset.singleton_union, Finset.card_insert_of_notMem hpnot]
  omega

/-- Every fixed arithmetic cell is exactly a complete prime-interval
fibre, with its unique integer product labels. No phase selection remains. -/
theorem mem_arithmeticCell_iff (L : ℝ) (N : ℕ) {n : ℕ} (D : Finset ℕ)
    (hn : Squarefree n) (hn1 : n ≠ 1) (m : ℕ) :
    m ∈ arithmeticCell L N (n, D) ↔
      ∃ p, intervalPrime L N n D p ∧ m = p * n := by
  constructor
  · intro hm
    obtain ⟨hband, hkey⟩ := Finset.mem_filter.mp hm
    obtain ⟨hp, hprod, _, _, _, _⟩ := arithmetic_owner_factorization hband
    have habove := owner_above_cofactor hband
    have hkey' : ownerCofactor m = n ∧
        activeDivisors L (ownerCofactor m) (Real.log (largestPrime m)) = D := by
      simpa only [originalCellKey, Prod.mk.injEq] using hkey
    refine ⟨largestPrime m, ⟨hp, ?_, ?_, ?_⟩, ?_⟩
    · simpa only [← hkey'.1] using habove
    · rw [← hkey'.1, hprod]
      exact (Finset.mem_filter.mp hband).1
    · simpa only [hkey'.1] using hkey'.2
    · simpa only [hkey'.1] using hprod.symm
  · rintro ⟨p, hp, rfl⟩
    refine Finset.mem_filter.mpr ⟨prime_product_mem_arithmeticBand N hp.1 hn hn1 hp.2.1 hp.2.2.1, ?_⟩
    rw [originalCellKey_mul L p n hp.1 hn.ne_zero hp.2.1, hp.2.2.2]

/-- A finite complete prime interval, with only an inessential original
upper bound used to make its enumeration finite. -/
def intervalPrimes (L : ℝ) (N n : ℕ) (D : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 ^ (32 * N))).filter (intervalPrime L N n D)

/-- The enumeration bound removes no prime satisfying the arithmetic
interval conditions. -/
theorem mem_intervalPrimes (L : ℝ) (N n : ℕ) (D : Finset ℕ) (hn : 0 < n) (p : ℕ) :
    p ∈ intervalPrimes L N n D ↔ intervalPrime L N n D p := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hp
    have hb := Finset.mem_Icc.mp (Finset.mem_filter.mp hp.2.2.1).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.1.one_le, ?_⟩, hp⟩
    exact (Nat.le_mul_of_pos_right p hn).trans hb.2

/-- Each arithmetic cell is precisely the injectively labelled image
of one complete interval of ordinary primes. -/
theorem arithmeticCell_eq_image (L : ℝ) (N : ℕ) {n : ℕ} (D : Finset ℕ)
    (hn : Squarefree n) (hn1 : n ≠ 1) :
    arithmeticCell L N (n, D) = (intervalPrimes L N n D).image (fun p => p * n) := by
  ext m
  rw [mem_arithmeticCell_iff L N D hn hn1, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hprod⟩
    exact ⟨p, (mem_intervalPrimes L N n D (Nat.pos_of_ne_zero hn.ne_zero) p).mpr hp, hprod.symm⟩
  · rintro ⟨p, hp, hprod⟩
    exact ⟨p, (mem_intervalPrimes L N n D (Nat.pos_of_ne_zero hn.ne_zero) p).mp hp, hprod.symm⟩

/-- Reindexing retains every complete complex summand and cannot duplicate
an original integer through a different prime incidence. -/
theorem sum_arithmeticCell (L : ℝ) (N : ℕ) {n : ℕ} (D : Finset ℕ)
    (hn : Squarefree n) (hn1 : n ≠ 1) (f : ℕ → ℂ) :
    ∑ m ∈ arithmeticCell L N (n, D), f m =
      ∑ p ∈ intervalPrimes L N n D, f (p * n) := by
  rw [arithmeticCell_eq_image L N D hn hn1]
  exact Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero hn.ne_zero) h)

/-- All fixed arithmetic cells, independently of height or filter. -/
def arithmeticCells (L : ℝ) (N : ℕ) : Finset (ℕ × Finset ℕ) :=
  (arithmeticBand N).image (originalCellKey L)

/-- Every attained cofactor is nonunit and squarefree without a
nonvanishing-filter assumption. -/
theorem arithmeticCells_valid (L : ℝ) (N : ℕ) {K : ℕ × Finset ℕ}
    (hK : K ∈ arithmeticCells L N) : Squarefree K.1 ∧ K.1 ≠ 0 ∧ K.1 ≠ 1 := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨_, _, hsf, hn0, hn1, _⟩ := arithmetic_owner_factorization hm
  exact ⟨hsf, hn0, hn1⟩

/-- Enlarging to the fixed arithmetic support adds only genuinely zero
original summands. No cancellation is assumed at the added terms. -/
theorem sum_arithmeticBand (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ∑ m ∈ arithmeticBand N, ZetaRieszConditionedEnergy.bandWeight L P N t m =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [← ZetaRieszWholeWindow.sum_activeOriginalBand L P N t]
  symm
  apply Finset.sum_subset (activeOriginalBand_subset_arithmeticBand L P N t)
  intro m hm hma
  by_contra hne
  exact hma (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, hne⟩)

/-- The fixed support admits the same exact cofactor profile, including
all zero-filter points needed for a complete prime interval. -/
theorem arithmetic_profile_eq_cell (L : ℝ) {N m : ℕ} (hm : m ∈ arithmeticBand N) :
    VaughanLogAverage.riesz L m =
      cellCoefficient L (originalCellKey L m).1 (originalCellKey L m).2 +
        Real.log m * divisorSlope (originalCellKey L m).2 := by
  obtain ⟨hp, hprod, _, hg0, _, hpg⟩ := arithmetic_owner_factorization hm
  have hr := ZetaRieszTargetProfile.riesz_prime_eq_target L hp hpg
  rw [hprod, targetProfile_eq_cellCoefficient] at hr
  have hlog : Real.log m = Real.log (largestPrime m) + Real.log (ownerCofactor m) := by
    calc
      Real.log m = Real.log (largestPrime m * ownerCofactor m : ℕ) :=
        congrArg (fun a : ℕ => Real.log a) hprod.symm
      _ = _ := by rw [Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hg0)]
  dsimp only [originalCellKey]
  rw [hr, hlog]
  ring

open ZetaRieszConditionedEnergy ZetaArithmeticBandCorrelation

/-- The two factorial orders remain coupled even when their individual
filter values vanish on a member of the complete arithmetic interval. -/
theorem arithmetic_atom_eq_adjacent (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {m : ℕ} (hm : m ∈ arithmeticBand N) :
    bandWeight L P N t m =
      (cellCoefficient L (originalCellKey L m).1 (originalCellKey L m).2 : ℂ) *
        bandAmplitude L P N t m +
      (divisorSlope (originalCellKey L m).2 : ℂ) * raisedBandAmplitude L P N t m := by
  rw [bandWeight_eq_amplitude_mul_riesz, arithmetic_profile_eq_cell L hm,
    ← log_mul_bandAmplitude]
  push_cast
  ring

/-- The full complex response over a fixed arithmetic cell. -/
def arithmeticCellResponse (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (K : ℕ × Finset ℕ) : ℂ :=
  (cellCoefficient L K.1 K.2 : ℂ) *
      (∑ m ∈ arithmeticCell L N K, bandAmplitude L P N t m) +
    (divisorSlope K.2 : ℂ) *
      (∑ m ∈ arithmeticCell L N K, raisedBandAmplitude L P N t m)

/-- Complete cells equal their literal signed original sums; individually
nonzero adjacent-order terms may cancel at an original zero atom. -/
theorem arithmeticCellResponse_eq_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (K : ℕ × Finset ℕ) :
    arithmeticCellResponse L P N t K = ∑ m ∈ arithmeticCell L N K, bandWeight L P N t m := by
  unfold arithmeticCellResponse
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hband, hkey⟩ := Finset.mem_filter.mp hm
  rw [arithmetic_atom_eq_adjacent L P N t hband, hkey]

/-- The prime form has complete interval support in both adjacent orders.
It is suitable for estimates for ordinary primes without phase masks. -/
theorem arithmeticCellResponse_eq_prime_moments (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) {K : ℕ × Finset ℕ} (hK : K ∈ arithmeticCells L N) :
    arithmeticCellResponse L P N t K =
      (cellCoefficient L K.1 K.2 : ℂ) *
        (∑ p ∈ intervalPrimes L N K.1 K.2, bandAmplitude L P N t (p * K.1)) +
      (divisorSlope K.2 : ℂ) *
        (∑ p ∈ intervalPrimes L N K.1 K.2, raisedBandAmplitude L P N t (p * K.1)) := by
  rcases K with ⟨n, D⟩
  obtain ⟨hn, _, hn1⟩ := arithmeticCells_valid L N hK
  unfold arithmeticCellResponse
  rw [sum_arithmeticCell L N D hn hn1, sum_arithmeticCell L N D hn hn1]

/-- The entire carrier is the sum of complete arithmetic prime-interval
responses, with every inter-cell sign still available. -/
theorem actual_band_eq_arithmetic_cells (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      ∑ K ∈ arithmeticCells L N, arithmeticCellResponse L P N t K := by
  rw [← sum_arithmeticBand L P N t]
  simp_rw [arithmeticCellResponse_eq_sum]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩) (bandWeight L P N t)

/-- The complete prime-interval decomposition preserves the arbitrary-
multiplicity pole-jet source at every right-half zero. -/
theorem tendsto_arithmetic_cell_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ arithmeticCells (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [← actual_band_eq_arithmetic_cells]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszArithmeticCells
