/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianExpandedRegion

/-!
# The union of the two explicit Gaussian regions

The smaller-dilation curve is wider at moderate height. The earlier
retained-cost curve has the better eventual leading coefficient. Taking
their maximum preserves both complete proofs and both closed right edges.
The existing eventual log-log component remains available with its original
unevaluated threshold. No Vinogradov--Korobov region is assumed or claimed.
-/

namespace RiemannGaussian.ZetaGaussianRegionUnion
noncomputable section
open Complex
open ZetaNearOneBudgetLimit (scale)

/-- The pointwise union keeps every height covered by either explicit proof. -/
def width (t : ℝ) : ℝ :=
  max (ZetaGaussianRetainedRegion.explicitWidth t) (ZetaGaussianExpandedRegion.explicitWidth t)

/-- The full union is positive with the enlarged physical ceiling. -/
theorem width_bounds (t : ℝ) : 0 < width t ∧ width t ≤ 1 / 40500 := by
  constructor
  · exact lt_of_lt_of_le (ZetaGaussianExpandedRegion.explicitWidth_pos t) (le_max_right _ _)
  · apply max_le
    · exact (ZetaGaussianScaledBandBudget.width_bounds (le_max_left _ _)).2.trans
        (by norm_num [GaussianStripProfile.width])
    · exact (ZetaGaussianExpandedScale.width_bounds (le_max_left _ _)).2

/-- The previous explicit curve is contained at every height. -/
theorem previous_width_le (t : ℝ) : ZetaGaussianRetainedRegion.explicitWidth t ≤ width t :=
  le_max_left _ _

/-- The new smaller-dilation component is also contained at every height. -/
theorem expanded_width_le (t : ℝ) : ZetaGaussianExpandedRegion.explicitWidth t ≤ width t :=
  le_max_right _ _

/-- The complete elementary formula retains both different paid denominators. -/
theorem width_eq_max_min {t : ℝ} (hL : 1 ≤ scale t) :
    width t = max
      (min (1 / 450000) (221 / (250 * ZetaGaussianRetainedRegion.heightCost (scale t))))
      (min (1 / 40500) (1547 / (1800 * ZetaGaussianExpandedRegion.heightCost (scale t)))) := by
  rw [width, ZetaGaussianRetainedRegion.explicitWidth_eq_min hL,
    ZetaGaussianExpandedRegion.explicitWidth_eq_min hL]

/-- Every actual nontrivial zero lies beyond the entire union's right edge. -/
theorem exact_margin (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    width ρ.1.im < 1 - ρ.1.re :=
  max_lt (ZetaGaussianRetainedRegion.exact_margin ρ ht)
    (ZetaGaussianExpandedRegion.exact_margin ρ ht)

/-- Literal zeta nonvanishing includes the closed right edge of the union. -/
theorem nonvanishing (s : ℂ) (ht : 1000000 ≤ |s.im|)
    (hσ : 1 - width s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num at ht
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  let ρ : NontrivialZetaZero := ⟨s, hz, hn, hs1⟩
  have h := exact_margin ρ ht
  change width s.im < 1 - s.re at h
  linarith

/-- Both reflected edges are retained for the literal zero set. -/
theorem exact_strip (ρ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|) :
    width ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - width ρ.1.im := by
  obtain ⟨ha, hb⟩ := ZetaGaussianRetainedRegion.exact_strip ρ ht
  obtain ⟨hc, hd⟩ := ZetaGaussianExpandedRegion.exact_strip ρ ht
  refine ⟨max_lt ha hc, ?_⟩
  have h := exact_margin ρ ht
  linarith

/-- The union gives at least a tenfold width gain throughout `1 ≤ L ≤ 64`. -/
theorem tenfold_previous_le {t : ℝ} (hL : 1 ≤ scale t) (hLu : scale t ≤ 64) :
    10 * ZetaGaussianRetainedRegion.explicitWidth t ≤ width t :=
  (ZetaGaussianExpandedRegion.tenfold_previous_le hL hLu).trans (expanded_width_le t)

/-- The signed logarithmic-height parametrization is antitone on its valid domain. -/
theorem width_antitone {t u : ℝ} (ht : 1 ≤ scale t) (htu : scale t ≤ scale u) :
    width u ≤ width t := by
  rw [width_eq_max_min ht, width_eq_max_min (ht.trans htu)]
  apply max_le_max
  · apply min_le_min_left
    have hc := ZetaGaussianRetainedRegion.heightCost_pos ht
    exact div_le_div_of_nonneg_left (by norm_num)
      (by positivity : 0 < 250 * ZetaGaussianRetainedRegion.heightCost (scale t))
      (mul_le_mul_of_nonneg_left (ZetaGaussianRetainedRegion.heightCost_mono ht htu) (by norm_num))
  · apply min_le_min_left
    have hc := ZetaGaussianExpandedRegion.heightCost_pos ht
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (ZetaGaussianExpandedRegion.heightCost_mono ht htu) (by norm_num))

/-- The existing eventual component joins the full explicit union, with
its coefficient-dependent threshold still stated separately. -/
theorem union_with_eventual {A : ℝ} (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      1000000 ≤ |ρ.1.im| →
      max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) < ρ.1.re ∧
        ρ.1.re < 1 - max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) := by
  obtain ⟨T, hT, hz⟩ := ZetaLogLogZeroFree.exists_eventual_strip hA hAlim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ ht
  obtain ⟨ha, hb⟩ := hz ρ hρ
  obtain ⟨hc, hd⟩ := exact_strip ρ ht
  refine ⟨max_lt ha hc, ?_⟩
  have hm : max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) <
      1 - ρ.1.re := max_lt (by linarith) (by linarith)
  linarith

end
end RiemannGaussian.ZetaGaussianRegionUnion
