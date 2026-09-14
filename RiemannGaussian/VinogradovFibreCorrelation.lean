/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFourierEvaluation

/-!
# Exact complex fibre averages and unweighted energy transfer

Average the original complex weights only over configurations with the
same complete frequency vector. The polynomial and its energy have exact
identities in these averages, so all correlations within each fibre remain
available. The maximum norm of these actual averages then transfers the
weighted energy to the unweighted energy on the identical configuration
family. This is an integrated comparison, not a pointwise comparison of
weighted and unweighted oscillating polynomials.

The transfer constant is proved at most any coefficient envelope; retaining
the complex averages first can capture cancellations that envelope loses.
Empty families and zero multiplicities are included.
-/

namespace RiemannGaussian.VinogradovFibreCorrelation
noncomputable section
open scoped Classical BigOperators NNReal
open MeasureTheory UnitAddTorus VinogradovPartitionEnergy VinogradovFourierEvaluation

/-- The original normalized Haar measure on the circle. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The exact number of original configurations on a complete frequency fibre. -/
def fibreMultiplicity {ι d : Type*} [Fintype ι] [Fintype d] (v : ι → d → ℤ) (c : d → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => v i = c)).card

/-- The original complex weights averaged on one complete frequency fibre. -/
def fibreAverage {ι d : Type*} [Fintype ι] [Fintype d] (v : ι → d → ℤ) (w : ι → ℂ) (c : d → ℤ) : ℂ :=
  frequencyWeight v w c / (fibreMultiplicity v c : ℂ)

/-- The actual largest fibre-average norm, with value zero for an empty family. -/
def correlationMaximum {ι d : Type*} [Fintype ι] [Fintype d] (v : ι → d → ℤ) (w : ι → ℂ) : ℝ :=
  ((Finset.univ.image v).sup (fun c => ‖fibreAverage v w c‖₊) : ℝ≥0)

/-- The original complex coefficient sums exactly the configurations on its fibre. -/
theorem frequencyWeight_eq_fibre_sum {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (c : d → ℤ) :
    frequencyWeight v w c = ∑ i ∈ Finset.univ.filter (fun i => v i = c), w i := by
  simp only [frequencyWeight, Finset.sum_filter]
  congr!

/-- A unit-weight frequency coefficient is exactly its original multiplicity. -/
theorem frequencyWeight_one {ι d : Type*} [Fintype ι] [Fintype d] (v : ι → d → ℤ) (c : d → ℤ) :
    frequencyWeight v (fun _ => 1) c = (fibreMultiplicity v c : ℂ) := by
  simp [frequencyWeight, fibreMultiplicity]

/-- Empty frequency fibres have zero full complex coefficient. -/
theorem frequencyWeight_eq_zero_of_multiplicity_zero {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (c : d → ℤ) (hc : fibreMultiplicity v c = 0) :
    frequencyWeight v w c = 0 := by
  have he : Finset.univ.filter (fun i => v i = c) = ∅ := Finset.card_eq_zero.mp hc
  rw [frequencyWeight_eq_fibre_sum, he, Finset.sum_empty]

/-- Recover every complex frequency coefficient exactly, including zero multiplicities. -/
theorem frequencyWeight_eq_multiplicity_average {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (c : d → ℤ) :
    frequencyWeight v w c = (fibreMultiplicity v c : ℂ) * fibreAverage v w c := by
  by_cases hc : fibreMultiplicity v c = 0
  · simp [hc, frequencyWeight_eq_zero_of_multiplicity_zero v w c hc]
  · unfold fibreAverage
    exact (mul_div_cancel₀ _ (by exact_mod_cast hc)).symm

/-- The complete oscillating polynomial keeps the actual complex averages before any norm. -/
theorem polynomial_eq_fibre_averages {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (theta : UnitAddTorus d) :
    polynomial v w theta = ∑ c ∈ Finset.univ.image v,
      (fibreMultiplicity v c : ℂ) * fibreAverage v w c * mFourier c theta := by
  rw [polynomial_eq_frequency_sum v w (Finset.univ.image v)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simp_rw [frequencyWeight_eq_multiplicity_average]

/-- Weighted torus energy is the exact multiplicity-squared sum of complex fibre-average energies. -/
theorem energy_eq_fibre_averages {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) :
    (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) =
      ∑ c ∈ Finset.univ.image v, (fibreMultiplicity v c : ℝ) ^ 2 * ‖fibreAverage v w c‖ ^ 2 := by
  rw [integral_energy_eq_frequency_weights v w (Finset.univ.image v)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simp_rw [frequencyWeight_eq_multiplicity_average, norm_mul, mul_pow, Complex.norm_natCast]

/-- Unit-weight energy counts every original equal-frequency pair. -/
theorem energy_one_eq_multiplicities {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) :
    (∫ theta : UnitAddTorus d, ‖polynomial v (fun _ => 1) theta‖ ^ 2) =
      ∑ c ∈ Finset.univ.image v, (fibreMultiplicity v c : ℝ) ^ 2 := by
  rw [integral_energy_eq_frequency_weights v (fun _ => 1) (Finset.univ.image v)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simp_rw [frequencyWeight_one, Complex.norm_natCast]

/-- The maximum of actual fibre-average norms is nonnegative. -/
theorem correlationMaximum_nonneg {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) : 0 ≤ correlationMaximum v w :=
  NNReal.coe_nonneg _

/-- Every attained complete-frequency average lies below its actual finite maximum. -/
theorem fibreAverage_norm_le_maximum {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) {c : d → ℤ} (hc : c ∈ Finset.univ.image v) :
    ‖fibreAverage v w c‖ ≤ correlationMaximum v w := by
  exact_mod_cast Finset.le_sup (f := fun c => ‖fibreAverage v w c‖₊) hc

/-- Transfer to the identical unit-weight configuration energy after retaining complete complex correlations. -/
theorem energy_le_correlation_maximum {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) :
    (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) ≤
      correlationMaximum v w ^ 2 * ∫ theta : UnitAddTorus d, ‖polynomial v (fun _ => 1) theta‖ ^ 2 := by
  rw [energy_eq_fibre_averages, energy_one_eq_multiplicities, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  rw [mul_comm (correlationMaximum v w ^ 2)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (fibreAverage_norm_le_maximum v w hc) 2) (sq_nonneg _)

/-- A coefficient envelope also bounds each complex fibre average, with no division by an empty fibre. -/
theorem fibreAverage_norm_le_of_weight_bound {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (c : d → ℤ) :
    ‖fibreAverage v w c‖ ≤ B := by
  by_cases hc : fibreMultiplicity v c = 0
  · simpa [fibreAverage, hc] using hB
  · have hcR : (0 : ℝ) < fibreMultiplicity v c := by exact_mod_cast Nat.pos_of_ne_zero hc
    rw [fibreAverage, norm_div, Complex.norm_natCast, div_le_iff₀ hcR]
    calc
      ‖frequencyWeight v w c‖ = ‖∑ i ∈ Finset.univ.filter (fun i => v i = c), w i‖ := by
        rw [frequencyWeight_eq_fibre_sum]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => v i = c), ‖w i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => v i = c), B := Finset.sum_le_sum (fun i _ => hw i)
      _ = B * (fibreMultiplicity v c : ℝ) := by simp [fibreMultiplicity, mul_comm]

/-- The correlation transfer never exceeds a supplied coefficient envelope; cancellations remain available before this optional relaxation. -/
theorem correlationMaximum_le_of_weight_bound {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) :
    correlationMaximum v w ≤ B := by
  change (((Finset.univ.image v).sup (fun c => ‖fibreAverage v w c‖₊) : ℝ≥0) : ℝ) ≤ B
  have he : (Finset.univ.image v).sup (fun c => ‖fibreAverage v w c‖₊) ≤ (⟨B, hB⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro c hc
    exact fibreAverage_norm_le_of_weight_bound v w hB hw c
  exact he

end
end RiemannGaussian.VinogradovFibreCorrelation
