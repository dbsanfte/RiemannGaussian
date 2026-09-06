import RiemannGaussian.EtaGaussianGapExpansion

/-!
# First signed correction to the actual zero-tilt return

The Wallis expansion is normalized by the actual centered gap mass.
Its constant cancels at first order, leaving the arithmetic midpoint.
The exact multiplier retains an inverse-square-width remainder uniformly
on the original finite physical window.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A simple inverse-width estimate for the centered gap's deficit from one quarter. -/
theorem pairedEtaGaussianGapMass_zero_deficit_le {h : ℝ} (hh : 0 < h) :
    |1 / 4 - pairedEtaGaussianGapMass h 0| ≤ 1 / (4 * h) := by
  obtain ⟨hlo, hhi⟩ := pairedEtaGaussianGapMass_zero_bounds hh
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hs : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
  calc
    _ ≤ Real.log 2 / (4 * Real.sqrt Real.pi * h) := by linarith
    _ ≤ 1 / (4 * Real.sqrt Real.pi * h) := div_le_div_of_nonneg_right hlog (by positivity)
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- After actual gap normalization, the Wallis constant cancels from the
first correction, which is exactly the center divided by `sqrt(pi)*h`. -/
theorem pairedEtaGaussianGapMass_ratio_firstCorrection_error_le {h c : ℝ}
    (hh : 2 ≤ h) (hc : 0 ≤ c) :
    |pairedEtaGaussianGapMass h c / pairedEtaGaussianGapMass h 0 - 1 - c / (Real.sqrt Real.pi * h)| ≤
      18 * (1 + c) ^ 3 / h ^ 2 := by
  have hh0 : 0 < h := by linarith
  have hg := pairedEtaGaussianGapMass_pos hh0 0
  have hs : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  let E : ℝ → ℝ := fun d ↦ pairedEtaGaussianGapMass h d - 1 / 4 -
    (d - Real.log (Real.pi / 2)) / (4 * Real.sqrt Real.pi * h)
  have hcE : |E c| ≤ 2 * (1 + c) ^ 3 / h ^ 3 := pairedEtaGaussianGapMass_wallis_expansion_error_le hh0 hc
  have h0E : |E 0| ≤ 2 / h ^ 3 := by
    simpa [E] using pairedEtaGaussianGapMass_wallis_expansion_error_le hh0 (le_refl (0 : ℝ))
  have hpow : (1 : ℝ) ≤ (1 + c) ^ 3 := one_le_pow₀ (by linarith)
  have hdiff : |E c - E 0| ≤ 4 * (1 + c) ^ 3 / h ^ 3 := by
    calc
      _ ≤ |E c| + |E 0| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (E c) 0 (E 0)
      _ ≤ 2 * (1 + c) ^ 3 / h ^ 3 + 2 / h ^ 3 := add_le_add hcE h0E
      _ ≤ _ := by
        have he := div_le_div_of_nonneg_right (show 2 ≤ 2 * (1 + c) ^ 3 by linarith) (show 0 ≤ h ^ 3 by positivity)
        exact (add_le_add le_rfl he).trans_eq (by ring)
  have hshift : |(c / (Real.sqrt Real.pi * h)) * (1 / 4 - pairedEtaGaussianGapMass h 0)| ≤ c / (4 * h ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c / (Real.sqrt Real.pi * h))]
    calc
      _ ≤ (c / h) * (1 / (4 * h)) :=
        mul_le_mul (div_le_div_of_nonneg_left hc hh0 (by nlinarith))
          (pairedEtaGaussianGapMass_zero_deficit_le hh0) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : pairedEtaGaussianGapMass h c / pairedEtaGaussianGapMass h 0 - 1 - c / (Real.sqrt Real.pi * h) =
      (E c - E 0 + (c / (Real.sqrt Real.pi * h)) * (1 / 4 - pairedEtaGaussianGapMass h 0)) /
        pairedEtaGaussianGapMass h 0 := by
    dsimp only [E]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hg]
  calc
    _ ≤ (4 * (1 + c) ^ 3 / h ^ 3 + c / (4 * h ^ 2)) / pairedEtaGaussianGapMass h 0 :=
      div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add hdiff hshift)) hg.le
    _ ≤ (4 * (1 + c) ^ 3 / h ^ 3 + c / (4 * h ^ 2)) / (1 / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (pairedEtaGaussianGapMass_zero_ge_eighth hh)
    _ = 32 * (1 + c) ^ 3 / h ^ 3 + 2 * c / h ^ 2 := by ring
    _ ≤ 32 * (1 + c) ^ 3 / (2 * h ^ 2) + 2 * c / h ^ 2 := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg h)])
    _ = (16 * (1 + c) ^ 3 + 2 * c) / h ^ 2 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg h)
      nlinarith [pow_nonneg hc 3, sq_nonneg c]

/-- The actual zero-tilt multiplier has the arithmetic midpoint as its
first broad-heat correction, with uniform inverse-square-width error. -/
theorem pairedEtaZeroTiltGapMultiplier_firstCorrection_error_le {h L t u : ℝ}
    (hh : 2 ≤ h) (ht : t ∈ Icc 0 L) (hu : u ∈ Icc 0 L) :
    |pairedEtaZeroTiltGapMultiplier h t u - 1 - ((t + u) / 2) / (Real.sqrt Real.pi * h)| ≤
      19 * (1 + L) ^ 3 / h ^ 2 := by
  have hh0 : 0 < h := by linarith
  have hL : 0 ≤ L := ht.1.trans ht.2
  have hc : 0 ≤ (t + u) / 2 := by linarith [ht.1, hu.1]
  have hcL : (t + u) / 2 ≤ L := by linarith [ht.2, hu.2]
  have hs : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  let E : ℝ := Real.exp (-((u - t) ^ 2 / (16 * h ^ 2)))
  let B : ℝ := 1 + ((t + u) / 2) / (Real.sqrt Real.pi * h)
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hEerr : |E - 1| ≤ (u - t) ^ 2 / (16 * h ^ 2) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hE1)]
    have he := Real.add_one_le_exp (-((u - t) ^ 2 / (16 * h ^ 2)))
    change -(E - 1) ≤ _
    linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : B ≤ 1 + L := by
    dsimp only [B]
    apply add_le_add le_rfl
    apply (div_le_iff₀ (by positivity)).2
    have hden : 1 ≤ Real.sqrt Real.pi * h := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hden hL
    nlinarith
  have hd : (u - t) ^ 2 ≤ L ^ 2 := by
    have he := mul_nonneg (show 0 ≤ L - (u - t) by linarith [ht.1, hu.2])
      (show 0 ≤ L + (u - t) by linarith [hu.1, ht.2])
    nlinarith
  have hsecond : |(E - 1) * B| ≤ (1 + L) ^ 3 / h ^ 2 := by
    rw [abs_mul, abs_of_nonneg hB0]
    calc
      _ ≤ ((u - t) ^ 2 / (16 * h ^ 2)) * (1 + L) :=
        mul_le_mul hEerr hB hB0 (by positivity)
      _ ≤ (L ^ 2 / (16 * h ^ 2)) * (1 + L) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hd (by positivity)) (by positivity)
      _ = (L ^ 2 * (1 + L) / 16) / h ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hL 3]) (sq_nonneg h)
  have hfirst : |E * (pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 - B)| ≤
      18 * (1 + L) ^ 3 / h ^ 2 := by
    rw [abs_mul, abs_of_pos hE0]
    apply (mul_le_of_le_one_left (abs_nonneg _) hE1).trans
    have hr := pairedEtaGaussianGapMass_ratio_firstCorrection_error_le hh hc
    rw [show pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 - B =
      pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 - 1 -
        ((t + u) / 2) / (Real.sqrt Real.pi * h) by dsimp [B]; ring]
    exact hr.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + (t + u) / 2 ≤ 1 + L) 3) (by norm_num)) (sq_nonneg h))
  have he : pairedEtaZeroTiltGapMultiplier h t u - 1 - ((t + u) / 2) / (Real.sqrt Real.pi * h) =
      E * (pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 - B) + (E - 1) * B := by
    dsimp [pairedEtaZeroTiltGapMultiplier, E, B]
    ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans_eq (by ring)

end

end RiemannGaussian
