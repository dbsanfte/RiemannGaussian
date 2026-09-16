/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCellOrders

/-!
# Unique largest-prime ownership of the entire carrier

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszOwnedCells
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeCells
open ZetaRieszCellOrders

/-- The exact signed integer divisor mass attached to a cell. -/
def divisorSlope (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- The affine cell coefficient after changing from the prime logarithm
to the full original integer logarithm. -/
def cellCoefficient (L : ℝ) (n : ℕ) (D : Finset ℕ) : ℝ :=
  VaughanLogAverage.riesz L n -
    ∑ d ∈ D, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - Real.log d) -
      Real.log n * divisorSlope D

/-- The literal active-divisor set determines both affine coefficients
without choosing an ideal or numerical reference prime. -/
theorem targetProfile_eq_cellCoefficient (L : ℝ) (n : ℕ) (x : ℝ) :
    targetProfile L n x = cellCoefficient L n (activeDivisors L n x) +
      (Real.log n + x) * divisorSlope (activeDivisors L n x) := by
  unfold targetProfile cellCoefficient divisorSlope
  rw [riesz_eq_active]
  have ht (d : ℕ) : ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - x - Real.log d) =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (L - Real.log d) -
        x * ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Every original nonzero atom has a canonical largest prime, extending
the earlier three-prime choice to the whole squarefree composite carrier. -/
theorem largestPrime_mem_of_two {m : ℕ} (hm : 2 ≤ m.primeFactors.card) :
    ZetaRieszPrimeEndpoint.largestPrime m ∈ m.primeFactors := by
  have h : m.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  rw [ZetaRieszPrimeEndpoint.largestPrime, dif_pos h]
  exact Finset.max'_mem _ _

/-- Removing the canonical largest prime gives one unique owner cofactor. -/
def ownerCofactor (m : ℕ) : ℕ := m / ZetaRieszPrimeEndpoint.largestPrime m

/-- All arithmetic factorization premises follow from the actual
nonzero original support, without selecting a sparse subfamily. -/
theorem original_owner_factorization (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {m : ℕ} (hm : m ∈ ZetaRieszWholeWindow.activeOriginalBand L P N t) :
    (ZetaRieszPrimeEndpoint.largestPrime m).Prime ∧
      ZetaRieszPrimeEndpoint.largestPrime m * ownerCofactor m = m ∧
      Squarefree (ownerCofactor m) ∧ ownerCofactor m ≠ 0 ∧ ownerCofactor m ≠ 1 ∧
      ¬ ZetaRieszPrimeEndpoint.largestPrime m ∣ ownerCofactor m := by
  obtain ⟨hsf, hcard⟩ := ZetaRieszWholeWindow.activeOriginalBand_support L P N t hm
  have hp := largestPrime_mem_of_two hcard
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hprod : ZetaRieszPrimeEndpoint.largestPrime m * ownerCofactor m = m := by
    rw [ownerCofactor, Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  have hsfprod : Squarefree (ZetaRieszPrimeEndpoint.largestPrime m * ownerCofactor m) := by
    rw [hprod]
    exact hsf
  have hg := hsfprod.of_mul_right
  have hg1 : ownerCofactor m ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hprod
    rw [← hprod, hpprime.primeFactors, Finset.card_singleton] at hcard
    omega
  exact ⟨hpprime, hprod, hg, hg.ne_zero, hg1,
    hpprime.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsfprod)⟩

/-- The unique original cell key records its owner cofactor and its
literal active divisor set. It cannot duplicate any original term. -/
def originalCellKey (L : ℝ) (m : ℕ) : ℕ × Finset ℕ :=
  (ownerCofactor m, activeDivisors L (ownerCofactor m)
    (Real.log (ZetaRieszPrimeEndpoint.largestPrime m)))

/-- All nonzero original amplitudes retain their exact affine divisor
profile, with the physical logarithm on the unchanged original label. -/
theorem original_profile_eq_cell (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {m : ℕ} (hm : m ∈ ZetaRieszWholeWindow.activeOriginalBand L P N t) :
    VaughanLogAverage.riesz L m =
      cellCoefficient L (originalCellKey L m).1 (originalCellKey L m).2 +
        Real.log m * divisorSlope (originalCellKey L m).2 := by
  obtain ⟨hp, hprod, _, hg0, _, hpg⟩ := original_owner_factorization L P N t hm
  have hr := riesz_prime_eq_target L hp hpg
  rw [hprod, targetProfile_eq_cellCoefficient] at hr
  have hlog : Real.log m = Real.log (ZetaRieszPrimeEndpoint.largestPrime m) +
      Real.log (ownerCofactor m) := by
    calc
      Real.log m = Real.log (ZetaRieszPrimeEndpoint.largestPrime m * ownerCofactor m : ℕ) :=
        congrArg (fun a : ℕ => Real.log a) hprod.symm
      _ = _ := by rw [Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hg0)]
  dsimp only [originalCellKey]
  rw [hr, hlog]
  ring

/-- One actual original atom is an exact signed combination of adjacent
factorial orders with the same support; no analytic estimate is assumed. -/
theorem original_atom_eq_adjacent (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {m : ℕ} (hm : m ∈ ZetaRieszWholeWindow.activeOriginalBand L P N t) :
    bandWeight L P N t m =
      (cellCoefficient L (originalCellKey L m).1 (originalCellKey L m).2 : ℂ) *
        bandAmplitude L P N t m +
      (divisorSlope (originalCellKey L m).2 : ℂ) * raisedBandAmplitude L P N t m := by
  rw [bandWeight_eq_amplitude_mul_riesz, original_profile_eq_cell L P N t hm,
    ← log_mul_bandAmplitude]
  push_cast
  ring

/-- Every attained owner-and-divisor cell in the entire original band. -/
def originalCells (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) : Finset (ℕ × Finset ℕ) :=
  (ZetaRieszWholeWindow.activeOriginalBand L P N t).image (originalCellKey L)

/-- A literal cell of original labels, with no unselected cofactor incidence. -/
def originalCell (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (K : ℕ × Finset ℕ) : Finset ℕ :=
  (ZetaRieszWholeWindow.activeOriginalBand L P N t).filter (fun m => originalCellKey L m = K)

/-- The canonical adjacent-order response of one complete original cell. -/
def originalCellResponse (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (K : ℕ × Finset ℕ) : ℂ :=
  (cellCoefficient L K.1 K.2 : ℂ) *
      (∑ m ∈ originalCell L P N t K, bandAmplitude L P N t m) +
    (divisorSlope K.2 : ℂ) *
      (∑ m ∈ originalCell L P N t K, raisedBandAmplitude L P N t m)

/-- Every complete cell equals its original signed sum with no local
profile error, and its two complex responses remain coupled. -/
theorem originalCellResponse_eq_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (K : ℕ × Finset ℕ) :
    originalCellResponse L P N t K = ∑ m ∈ originalCell L P N t K, bandWeight L P N t m := by
  unfold originalCellResponse
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hactive, hkey⟩ := Finset.mem_filter.mp hm
  rw [original_atom_eq_adjacent L P N t hactive, hkey]

/-- All cofactor selection and cell membership premises are discharged:
the entire original carrier is exactly the sum of its canonical signed
adjacent-order responses. No boundary remainder or term is dropped. -/
theorem actual_band_eq_cell_responses (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      ∑ K ∈ originalCells L P N t, originalCellResponse L P N t K := by
  rw [← ZetaRieszWholeWindow.sum_activeOriginalBand L P N t]
  simp_rw [originalCellResponse_eq_sum]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩) (bandWeight L P N t)

/-- Canonical cell cancellation yields a full-original-band finite
upper bound for every complex polynomial, without a searched family. -/
theorem norm_actual_band_le_cell_mass (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      ∑ K ∈ originalCells L P N t, ‖originalCellResponse L P N t K‖ := by
  rw [actual_band_eq_cell_responses]
  exact norm_sum_le _ _

/-- The complete canonical cell sum retains the full negative
multiplicity source at every right-half zero, without exposure or simplicity. -/
theorem tendsto_original_cell_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ originalCells (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im,
        originalCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [← actual_band_eq_cell_responses]
  push_cast
  rfl

end
end RiemannGaussian.ZetaRieszOwnedCells
