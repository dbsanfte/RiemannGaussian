import RiemannGaussian.EtaMoebiusContinuumEnergy
import RiemannGaussian.EtaAlternatingReal

/-!
# The actual balanced Möbius grid as a signed parity wave

This implements the parity representation proposed in the exterior-leakage
endgame steer. The existing right-closed interval colour is used so that
the identity holds at every positive physical coordinate, including all
integer endpoints. The full coefficient cancellation removes the constant
colour before any square or norm is taken.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The signed period-two parity wave with the exact original right-closed endpoint convention. -/
def etaUnitIntervalParity (x : ℝ) : ℝ := 1 - 2 * etaUnitIntervalColour x

/-- The signed parity wave has absolute value exactly one at every real coordinate. -/
theorem abs_etaUnitIntervalParity (x : ℝ) : |etaUnitIntervalParity x| = 1 := by
  rcases etaUnitIntervalColour_eq_zero_or_one x with h | h <;> norm_num [etaUnitIntervalParity, h]

/-- The signed parity wave retains the exact period two, including at integer endpoints. -/
theorem etaUnitIntervalParity_periodic : Function.Periodic etaUnitIntervalParity 2 := by
  intro x
  simp only [etaUnitIntervalParity, etaUnitIntervalColour_periodic x]

/-- The exact signed parity sum of the original finite-difference Möbius coefficients. -/
def pairedEtaMoebiusGridParitySum (d M : ℕ) (w : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j * etaUnitIntervalParity ((j.1 + 1 : ℝ) * z)

private theorem indicator_eq_colour_exp_all (t : ℝ) :
    pairedEtaLogIndicator t = etaUnitIntervalColour (Real.exp t) := by
  by_cases ht : 0 < t
  · exact pairedEtaLogIndicator_eq_unitIntervalColour_exp ht
  · rw [pairedEtaLogIndicator_eq_zero_of_nonpos (le_of_not_gt ht),
      etaUnitIntervalColour_eq_on_cell (n := 1) ⟨by simpa using Real.exp_pos t,
        by simpa using Real.exp_le_one_iff.mpr (le_of_not_gt ht)⟩]
    norm_num

/-- Every original grid translate becomes its actual integer-frequency parity colour at a positive physical coordinate. -/
theorem pairedEtaMoebiusTrialGridColour_eq_unitColour {d : ℕ} (hd : 0 < d)
    (j : Fin d) {z : ℝ} (hz : 0 < z) :
    pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint d (j.1 + 1))
      (Real.log ((d : ℝ) * z)) = etaUnitIntervalColour ((j.1 + 1 : ℝ) * z) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hj : (0 : ℝ) < j.1 + 1 := by positivity
  rw [pairedEtaTranslatedColour, indicator_eq_colour_exp_all,
    pairedEtaMoebiusTrialGridPoint_eq_log (by omega) (by omega), Nat.cast_add, Nat.cast_one, Real.exp_sub,
    Real.exp_log (mul_pos hdp hz), Real.exp_log (div_pos hdp hj)]
  congr 1
  field_simp

/-- Exact zero coefficient mass identifies the entire original grid with minus one half of its signed parity sum, at every positive physical coordinate. -/
theorem pairedEtaMoebiusTrialGridCombination_eq_paritySum {d M : ℕ} (hd : 0 < d)
    (hMd : M ≤ d) (w : ℕ → ℝ) {z : ℝ} (hz : 0 < z) :
    pairedEtaMoebiusTrialGridCombination d M w (Real.log ((d : ℝ) * z)) =
      ((-pairedEtaMoebiusGridParitySum d M w z / 2 : ℝ) : ℂ) := by
  have hs := sum_pairedEtaMoebiusTrialCoefficient_eq_zero hMd w
  have he : (∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j *
      etaUnitIntervalColour ((j.1 + 1 : ℝ) * z)) = -pairedEtaMoebiusGridParitySum d M w z / 2 := by
    unfold pairedEtaMoebiusGridParitySum etaUnitIntervalParity
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hs]
    simp_rw [show ∀ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j *
      (2 * etaUnitIntervalColour ((j.1 + 1 : ℝ) * z)) =
      2 * (pairedEtaMoebiusTrialCoefficient d M w j * etaUnitIntervalColour ((j.1 + 1 : ℝ) * z))
      by intro j; ring, ← Finset.mul_sum]
    ring
  unfold pairedEtaMoebiusTrialGridCombination pairedEtaTranslatedCombination
  simp_rw [pairedEtaMoebiusTrialGridColour_eq_unitColour hd _ hz, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  exact congrArg (fun x : ℝ ↦ (x : ℂ)) he

/-- The full actual parity combination is exactly periodic; its finite difference coefficients remain signed. -/
theorem pairedEtaMoebiusGridParitySum_periodic (d M : ℕ) (w : ℕ → ℝ) :
    Function.Periodic (pairedEtaMoebiusGridParitySum d M w) 2 := by
  intro z
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := etaUnitIntervalParity_periodic.nat_mul (j.1 + 1)
  have he := h ((j.1 + 1 : ℝ) * z)
  simpa only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul,
    mul_add, mul_comm (2 : ℝ)] using he

/-- The signed parity sum has the complete coefficient bound; this bound is reserved for the far tail rather than replacing its near-shell covariance. -/
theorem abs_pairedEtaMoebiusGridParitySum_le (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (z : ℝ) :
    |pairedEtaMoebiusGridParitySum d M w z| ≤ 2 * M := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [abs_mul, abs_etaUnitIntervalParity, mul_one] using
    pairedEtaMoebiusTrialCoefficient_sum_abs_le d M hw

/-- Exact discrete summation by parts transfers the coefficient difference to the parity wave; both original primitive endpoints vanish and every remaining sign is retained. -/
theorem pairedEtaMoebiusGridParitySum_eq_primitive_differences {d M : ℕ} (hMd : M ≤ d)
    (w : ℕ → ℝ) (z : ℝ) :
    pairedEtaMoebiusGridParitySum d M w z =
      ∑ j ∈ Finset.range (d - 1), pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j + 2 : ℝ)) *
        (etaUnitIntervalParity ((j + 2 : ℝ) * z) - etaUnitIntervalParity ((j + 1 : ℝ) * z)) := by
  let a := fun j : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j + 1 : ℝ))
  let e := fun j : ℕ ↦ etaUnitIntervalParity ((j + 1 : ℝ) * z)
  have ha0 : a 0 = 0 := by
    dsimp [a]
    simpa only [Nat.cast_zero, zero_add, div_one] using
      pairedEtaMoebiusTrialPrimitive_eq_zero_of_cutoff_le M w (by exact_mod_cast hMd)
  have had : a d = 0 := pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one M w
    ((div_lt_one (by positivity)).mpr (by linarith))
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, (a j - a (j + 1))) = -a n := by
    rw [Finset.sum_range_sub', ha0, zero_sub]
  have hb := Finset.sum_range_by_parts e (fun j ↦ a j - a (j + 1)) d
  simp only [smul_eq_mul, hsum, had, neg_zero, mul_zero, zero_sub,
    mul_neg, Finset.sum_neg_distrib, neg_neg] at hb
  calc
    _ = ∑ j ∈ Finset.range d, e j * (a j - a (j + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp only [pairedEtaMoebiusTrialCoefficient, a, e, Nat.cast_add, Nat.cast_one,
        add_assoc, one_add_one_eq_two, mul_comm]
    _ = _ := by
      rw [hb]
      apply Finset.sum_congr rfl
      intro j _
      simp only [a, e, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, mul_comm]

end

end RiemannGaussian
