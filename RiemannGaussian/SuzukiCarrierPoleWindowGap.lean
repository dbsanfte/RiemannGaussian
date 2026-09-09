/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierRealContour

/-!
# A positive bottom displacement preserving every genuine carrier pole

No genuine carrier pole is real: a real zero of its denominator is a xi
zero and belongs to the separately evaluated xi source. Finiteness of the
actual closed rectangle therefore provides a positive gap below its
genuine pole group. A bottom in this gap can additionally avoid every xi
and carrier singular ordinate. This choice is independent of the mixed
nodes and all complex weights.
-/

open Complex Filter Metric Set Topology
namespace RiemannGaussian
noncomputable section

private lemma mem_window {l r b u : ℝ} (hlr : l ≤ r) (hbu : b ≤ u) {c : ℂ} :
    c ∈ suzukiXiCarrierGenuinePoleWindow l r b u ↔
      (l ≤ c.re ∧ c.re ≤ r) ∧ (b ≤ c.im ∧ c.im ≤ u) ∧
        c ∈ suzukiXiCarrierSingularSet ∧ riemannXiSpectral c ≠ 0 := by
  simp only [suzukiXiCarrierGenuinePoleWindow, Finset.mem_filter,
    mem_suzukiXiCarrierPoleWindow, Complex.Rectangle, Complex.mem_reProdIm,
    ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
    mul_zero, mul_one, add_zero, zero_add, sub_zero,
    uIcc_of_le hlr, uIcc_of_le hbu, mem_Icc, and_assoc]

/-- Every genuine carrier pole in a real-bottom upper rectangle has
strictly positive height. Shared real xi/denominator zeros are not
mistaken for genuine poles. -/
theorem im_pos_of_mem_suzukiXiCarrierGenuinePoleWindow_real
    {l r u : ℝ} (hlr : l ≤ r) (hu : 0 ≤ u) {c : ℂ}
    (hc : c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u) : 0 < c.im := by
  obtain ⟨_hx, hy, hsing, hxi⟩ := (mem_window hlr hu).mp hc
  apply lt_of_le_of_ne hy.1
  intro him
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, c = (x : ℂ) :=
    ⟨c.re, Complex.ext (by simp) (by simpa using him.symm)⟩
  exact hxi (hsing.elim id riemannXiSpectral_eq_zero_of_suzukiXiEValue_ofReal_eq_zero)

/-- A sufficiently small positive lift of the bottom preserves the
entire finite genuine pole group, at every analytic order. -/
theorem exists_suzukiXiCarrierGenuinePoleWindow_bottom_gap
    {l r u : ℝ} (hlr : l ≤ r) (hu : 0 < u) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ b : ℝ, 0 < b → b < delta → b < u →
      suzukiXiCarrierGenuinePoleWindow l r b u = suzukiXiCarrierGenuinePoleWindow l r 0 u := by
  have hsmall : ∀ᶠ b : ℝ in 𝓝 0,
      ∀ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, b < c.im := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact isOpen_Iio.mem_nhds (im_pos_of_mem_suzukiXiCarrierGenuinePoleWindow_real hlr hu.le hc)
  obtain ⟨delta, hd, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨delta, hd, ?_⟩
  intro b hb hbd hbu
  have hstay : ∀ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, b < c.im :=
    hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hb] using hbd)
  ext c
  constructor
  · intro hc
    obtain ⟨hx, hy, hs, hxi⟩ := (mem_window hlr hbu.le).mp hc
    exact (mem_window hlr hu.le).mpr ⟨hx, ⟨hb.le.trans hy.1, hy.2⟩, hs, hxi⟩
  · intro hc
    obtain ⟨hx, hy, hs, hxi⟩ := (mem_window hlr hu.le).mp hc
    exact (mem_window hlr hbu.le).mpr ⟨hx, ⟨(hstay c hc).le, hy.2⟩, hs, hxi⟩

/-- A positive admissible bottom below one half preserves all genuine
carrier poles of the original real-bottom rectangle. Its existence
requires no simplicity or zero-free-real-axis premise. -/
theorem exists_suzukiXiCarrier_admissible_bottom_same_genuine_poles
    {l r u : ℝ} (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible l r b u ∧
      suzukiXiCarrierGenuinePoleWindow l r b u = suzukiXiCarrierGenuinePoleWindow l r 0 u := by
  obtain ⟨delta, hd, hgap⟩ := exists_suzukiXiCarrierGenuinePoleWindow_bottom_gap hadm.1.le hadm.2.1
  obtain ⟨b, hb, hsafe⟩ := exists_suzukiXiCarrier_safe_coordinate
    (a := 0) (b := min delta (min u (1 / 2))) (lt_min hd (lt_min hadm.2.1 (by norm_num)))
  have hbd := hb.2.trans_le (min_le_left _ _)
  have hbrest := hb.2.trans_le (min_le_right _ _)
  have hbu := hbrest.trans_le (min_le_left _ _)
  have hbhalf := hbrest.trans_le (min_le_right _ _)
  exact ⟨b, hb.1, hbhalf, ⟨hadm.1, hbu, fun c hc =>
    ⟨(hadm.2.2 c hc).1, (hadm.2.2 c hc).2.1, (hsafe c hc).2, (hadm.2.2 c hc).2.2⟩⟩,
      hgap b hb.1 hbd hbu⟩

end
end RiemannGaussian
