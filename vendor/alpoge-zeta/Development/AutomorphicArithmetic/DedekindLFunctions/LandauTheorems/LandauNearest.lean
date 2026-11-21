import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

lemma landau_nearest_equi {σ γ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (h : ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖)
    (hγ : γ ≠ ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) / (2 * (a.im - b.im))) :
    a = b := by
  have h2 : ‖(σ : ℂ) + γ * I - a‖ ^ 2 = ‖(σ : ℂ) + γ * I - b‖ ^ 2 := by rw [h]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
  have him : a.im = b.im := by
    by_contra hne
    apply hγ
    have hne' : 2 * (a.im - b.im) ≠ 0 := by
      have := sub_ne_zero.mpr hne
      positivity
    rw [eq_div_iff hne']
    linear_combination -h2
  have hsq : (b.re - a.re) * ((σ - a.re) + (σ - b.re)) = 0 := by
    rw [him] at h2
    linear_combination h2
  rcases mul_eq_zero.mp hsq with h3 | h3
  · apply Complex.ext
    · linarith
    · exact him
  · exfalso
    linarith

theorem landau_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ D : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (D - (σ - ρ₁.re)) / 2 ∧ ε ≤ (σ - D) / 2 := by
    refine ⟨min (D - (σ - ρ₁.re)) (σ - D) / 2, ?_, ?_, ?_⟩
    · have := lt_min (show 0 < D - (σ - ρ₁.re) by linarith) (show 0 < σ - D by linarith)
      linarith
    · have := min_le_left (D - (σ - ρ₁.re)) (σ - D)
      linarith
    · have := min_le_right (D - (σ - ρ₁.re)) (σ - D)
      linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, c₀ = (σ : ℂ) + ρ₁.im * I := ⟨_, rfl⟩
  have hc₀re : c₀.re = σ := by rw [hc₀]; simp
  have hF : (Z ∩ Metric.closedBall c₀ (D + ε)).Finite :=
    landau_finite hiso (by rw [hc₀re]; linarith)
  set F := Z ∩ Metric.closedBall c₀ (D + ε) with hFdef
  set B : Set ℝ := (fun p : ℂ × ℂ =>
      ((σ - p.1.re) ^ 2 + p.1.im ^ 2 - (σ - p.2.re) ^ 2 - p.2.im ^ 2) / (2 * (p.1.im - p.2.im))) ''
      (F ×ˢ F) with hB
  have hBfin : B.Finite := (hF.prod hF).image _
  obtain ⟨γ, hγI, hγB⟩ := ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).diff hBfin).nonempty
  set c : ℂ := (σ : ℂ) + γ * I with hc
  have hγε : |γ - ρ₁.im| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hγI.2], by linarith [hγI.1]⟩
  have hcc₀ : ‖c - c₀‖ = |γ - ρ₁.im| := by
    have e : c - c₀ = ((γ - ρ₁.im : ℝ) : ℂ) * I := by
      rw [hc, hc₀]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hc₀ρ₁ : ‖c₀ - ρ₁‖ = σ - ρ₁.re := by
    have e : c₀ - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc₀]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hle ρ₁ h₁))]
  have hρ₁F : ρ₁ ∈ F := by
    refine ⟨h₁, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, hc₀ρ₁]
    linarith
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩
  have hρ₁c : ‖c - ρ₁‖ < D := by
    have := norm_add_le (c - c₀) (c₀ - ρ₁)
    rw [sub_add_sub_cancel, hcc₀, hc₀ρ₁] at this
    linarith
  have hm : ‖c - ρ‖ ≤ ‖c - ρ₁‖ := hmin ρ₁ hρ₁F
  have hT : ∀ w ∈ F \ {ρ}, ‖c - ρ‖ < ‖c - w‖ := by
    intro w hw
    have hmw : ‖c - ρ‖ ≤ ‖c - w‖ := hmin w hw.1
    rcases lt_or_eq_of_le hmw with h | h
    · exact h
    · exfalso
      apply hw.2
      exact landau_nearest_equi (hle w hw.1.1) (hle ρ hρF.1) h.symm
        (fun hb => hγB ⟨(w, ρ), ⟨hw.1, hρF⟩, hb.symm⟩)
  obtain ⟨r, hr, hrT⟩ : ∃ r, ‖c - ρ‖ < r ∧ ∀ t ∈ F \ {ρ}, r ≤ ‖c - t‖ := by
    rcases (F \ {ρ}).eq_empty_or_nonempty with hTe | hTne
    · refine ⟨‖c - ρ‖ + 1, by linarith, ?_⟩
      intro t ht
      rw [hTe] at ht
      exact absurd ht (Set.notMem_empty t)
    · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {ρ}) (fun w => ‖c - w‖)
        (hF.subset Set.diff_subset) hTne
      exact ⟨‖c - t₀‖, hT t₀ ht₀, htmin⟩
  refine ⟨γ, ρ, hρF.1, min r D, lt_min hr (by linarith), min_le_right _ _, ?_⟩
  intro w hw hb
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hb
  have hwF : w ∈ F := by
    refine ⟨hw, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := norm_add_le (w - c) (c - c₀)
    rw [sub_add_sub_cancel, norm_sub_rev w c, hcc₀] at this
    linarith [min_le_right r D]
  by_contra hne
  have h3 := hrT w ⟨hwF, hne⟩
  linarith [min_le_left r D]

end Deduction

end
