/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiZeroFree

/-!
# A global monotone margin from the eventual Fermi region

The eventual Fermi theorem already proves the existence of its height
threshold. Choosing that witness and retaining the old margin below it
gives an unconditional exclusion at every height. A cap by the old width
at the threshold makes the new width antitone in absolute height. Beyond
another proved finite threshold it is exactly `3/(20*log(abs(t)))` and
strictly improves the old region. Neither threshold is numerically evaluated.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- A witness of the proved eventual strip theorem, enlarged to make all
logarithms in the global margin positive. This chooses a proved witness;
it does not assume a zero-free region or a numerical height certificate. -/
def zetaFermiHeightThreshold : ℝ :=
  max (Classical.choose GaussianFermiZeroFree.exists_eventual_strip) (Real.exp 4000)

/-- The chosen height satisfies the elementary logarithmic bound and the
actual zero theorem from which it was selected. -/
theorem zetaFermiHeightThreshold_spec :
    1 ≤ zetaFermiHeightThreshold ∧ 4000 ≤ Real.log zetaFermiHeightThreshold ∧
      ∀ ρ : NontrivialZetaZero, zetaFermiHeightThreshold ≤ |ρ.1.im| →
        3 / (20 * Real.log |ρ.1.im|) < ρ.1.re ∧
          ρ.1.re < 1 - 3 / (20 * Real.log |ρ.1.im|) := by
  have h := Classical.choose_spec GaussianFermiZeroFree.exists_eventual_strip
  refine ⟨h.1.trans (le_max_left _ _), ?_, ?_⟩
  · have he := Real.log_le_log (Real.exp_pos 4000)
      (le_max_right (Classical.choose GaussianFermiZeroFree.exists_eventual_strip)
        (Real.exp 4000))
    simpa only [zetaFermiHeightThreshold, Real.log_exp] using he
  · intro ρ hρ
    exact h.2 ρ ((le_max_left _ _).trans hρ)

/-- A positive all-height width retaining the old region. The new part is
capped by the old width at the proved threshold, so it remains valid even
when an analytic domain crosses that threshold. -/
def zetaFermiZeroMargin (t : ℝ) : ℝ :=
  max (zetaPoleReserveZeroMargin t)
    (min (zetaPoleReserveZeroMargin zetaFermiHeightThreshold)
      (3 / (20 * Real.log (max zetaFermiHeightThreshold |t|))))

/-- The Fermi extension never weakens the preceding all-height exclusion. -/
theorem zetaPoleReserve_margin_le_fermi (t : ℝ) :
    zetaPoleReserveZeroMargin t ≤ zetaFermiZeroMargin t := le_max_left _ _

/-- The global margin stays positive and below one quarter, uniformly
through the transition from the old to the eventual region. -/
theorem zetaFermiZeroMargin_bounds (t : ℝ) :
    0 < zetaFermiZeroMargin t ∧ zetaFermiZeroMargin t < 1 / 4 := by
  refine ⟨(zetaPoleReserveZeroMargin_bounds t).1.trans_le
    (zetaPoleReserve_margin_le_fermi t), ?_⟩
  exact max_lt (zetaPoleReserveZeroMargin_bounds t).2
    ((min_le_left _ _).trans_lt
      (zetaPoleReserveZeroMargin_bounds zetaFermiHeightThreshold).2)

/-- The combined width is antitone in absolute height. This is the
uniformity needed to use the pointwise zero-free result on entire discs. -/
theorem zetaFermiZeroMargin_antitone_abs {a b : ℝ} (h : |a| ≤ |b|) :
    zetaFermiZeroMargin b ≤ zetaFermiZeroMargin a := by
  have hT : 0 < zetaFermiHeightThreshold := by linarith [zetaFermiHeightThreshold_spec.1]
  have hlower := Real.log_le_log hT (le_max_left zetaFermiHeightThreshold |a|)
  have hlog := Real.log_le_log (hT.trans_le (le_max_left _ _))
    (max_le_max_left zetaFermiHeightThreshold h)
  apply max_le_max (zetaPoleReserveZeroMargin_antitone_abs h)
  apply min_le_min_left
  apply div_le_div_of_nonneg_left (by norm_num)
    (by linarith [zetaFermiHeightThreshold_spec.2.1])
  linarith

/-- At every height below the chosen threshold the combined margin equals
the preceding one exactly. -/
theorem zetaFermiZeroMargin_eq_poleReserve_of_le {t : ℝ}
    (ht : |t| ≤ zetaFermiHeightThreshold) :
    zetaFermiZeroMargin t = zetaPoleReserveZeroMargin t := by
  have hT : 0 ≤ zetaFermiHeightThreshold := by linarith [zetaFermiHeightThreshold_spec.1]
  have h := zetaPoleReserveZeroMargin_antitone_abs
    (show |t| ≤ |zetaFermiHeightThreshold| by simpa only [abs_of_nonneg hT] using ht)
  exact max_eq_left ((min_le_left _ _).trans h)

/-- Every actual zero satisfies the combined strict right-edge margin.
The two height cases use proved zero theorems, with no residual premise. -/
theorem zetaFermi_margin_lt_one_sub_re (ρ : NontrivialZetaZero) :
    zetaFermiZeroMargin ρ.1.im < 1 - ρ.1.re := by
  by_cases ht : |ρ.1.im| ≤ zetaFermiHeightThreshold
  · rw [zetaFermiZeroMargin_eq_poleReserve_of_le ht]
    exact zetaPoleReserve_margin_lt_one_sub_re ρ
  · have ht' := (lt_of_not_ge ht).le
    have hzero := (zetaFermiHeightThreshold_spec.2.2 ρ ht').2
    apply max_lt (zetaPoleReserve_margin_lt_one_sub_re ρ)
    apply (min_le_right _ _).trans_lt
    rw [max_eq_right ht']
    linarith

/-- Genuine horizontal reflection transports the full combined width to
the other side of the critical strip. -/
theorem zetaFermi_margin_lt_re (ρ : NontrivialZetaZero) :
    zetaFermiZeroMargin ρ.1.im < ρ.1.re := by
  have h := zetaFermi_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner ρ)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- The actual nontrivial zeros lie in this all-height strip. -/
theorem nontrivialZetaZero_mem_fermi_strip (ρ : NontrivialZetaZero) :
    ρ.1.re ∈ Set.Ioo (zetaFermiZeroMargin ρ.1.im) (1 - zetaFermiZeroMargin ρ.1.im) :=
  ⟨zetaFermi_margin_lt_re ρ, by linarith [zetaFermi_margin_lt_one_sub_re ρ]⟩

/-- Literal zeta nonvanishing on the combined closed right edge, at every
ordinate and explicitly away from the pole. -/
theorem riemannZeta_ne_zero_of_fermi_margin {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaFermiZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [(zetaFermiZeroMargin_bounds s.im).2]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_fermi_strip ρ).2
  change s.re < 1 - zetaFermiZeroMargin s.im at h
  linarith

/-- Eventually the transition cap is inactive: the global width is exactly
the stronger Fermi width and strictly exceeds the preceding margin. The
height is again proved to exist rather than numerically certified. -/
theorem exists_eventual_fermiZeroMargin_eq :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      zetaFermiZeroMargin t = 3 / (20 * Real.log |t|) ∧
        zetaPoleReserveZeroMargin t < zetaFermiZeroMargin t := by
  let c := zetaPoleReserveZeroMargin zetaFermiHeightThreshold
  have hc : 0 < c := (zetaPoleReserveZeroMargin_bounds _).1
  refine ⟨max zetaFermiHeightThreshold (Real.exp (max 4000 (1 / c))),
    zetaFermiHeightThreshold_spec.1.trans (le_max_left _ _), ?_⟩
  intro t ht
  have htT : zetaFermiHeightThreshold ≤ |t| := (le_max_left _ _).trans ht
  have htpos : 0 < |t| := by linarith [zetaFermiHeightThreshold_spec.1]
  have hlog : max 4000 (1 / c) ≤ Real.log |t| := by
    have h := Real.log_le_log (Real.exp_pos (max 4000 (1 / c)))
      ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using h
  have hlog4000 : 4000 ≤ Real.log |t| := (le_max_left _ _).trans hlog
  have hinv : 1 / c ≤ Real.log |t| := (le_max_right _ _).trans hlog
  have hcap : 3 / (20 * Real.log |t|) ≤ c := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_le_iff₀ hc).mp hinv
    nlinarith
  have hold : zetaPoleReserveZeroMargin t < 3 / (20 * Real.log |t|) := by
    have h := GaussianFermiZeroFree.old_margin_lt_fermi_width htpos hlog4000
    have he : zetaPoleReserveZeroMargin |t| = zetaPoleReserveZeroMargin t := by
      apply le_antisymm
      · exact zetaPoleReserveZeroMargin_antitone_abs (by simp)
      · exact zetaPoleReserveZeroMargin_antitone_abs (by simp)
    rwa [he] at h
  have he : zetaFermiZeroMargin t = 3 / (20 * Real.log |t|) := by
    unfold zetaFermiZeroMargin
    rw [max_eq_right htT, min_eq_right hcap, max_eq_right hold.le]
  exact ⟨he, he ▸ hold⟩

end
end RiemannGaussian
