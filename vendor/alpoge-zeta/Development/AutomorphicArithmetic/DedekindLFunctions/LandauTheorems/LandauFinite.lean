import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

end Deduction

end
