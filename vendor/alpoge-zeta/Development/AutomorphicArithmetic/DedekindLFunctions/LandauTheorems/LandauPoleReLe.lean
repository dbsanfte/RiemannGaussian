import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_pole_re_le_bound {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {σ : ℝ}
    (hσ : 2 < σ) : ∃ M : ℝ, ∀ s : ℂ, σ ≤ s.re → ‖Φ s‖ ≤ M := by
  obtain ⟨C, hC⟩ := hP.growth
  refine ⟨∫ u in Ioi (0 : ℝ), C * Real.exp (-(σ - 2) * u), fun s hs => ?_⟩
  rw [hP.laplace s (lt_of_lt_of_le hσ hs)]
  refine norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσ)).const_mul C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have h1 := hC u hu0
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have h2 : Real.exp (-s.re * u) ≤ Real.exp (-σ * u) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc |g u| * Real.exp (-s.re * u) ≤ (C * Real.exp (2 * u)) * Real.exp (-σ * u) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le ((abs_nonneg _).trans h1)
    _ = C * Real.exp (-(σ - 2) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem landau_pole_re_le {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) : ∀ ρ ∈ Z, ρ.re ≤ 2 := by
  intro ρ hρ
  by_contra hlt
  have hlt : 2 < ρ.re := not_le.mp hlt
  obtain ⟨M, hM⟩ := landau_pole_re_le_bound hP (σ := (2 + ρ.re) / 2) (by linarith)
  obtain ⟨c, hc, -, h, hh, hev⟩ := hP.pole ρ hρ
  have h0 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := tendsto_id.sub_const ρ
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ s in 𝓝[≠] ρ, ‖Φ s‖ ≤ M := by
    have : ∀ᶠ s in 𝓝 ρ, (2 + ρ.re) / 2 < s.re :=
      Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [this.filter_mono nhdsWithin_le_nhds] with s hs using hM s hs.le
  have h1 : Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h0 ⟨M, eventually_map.mpr hb⟩
  have h2 : Tendsto (fun s : ℂ => c + (s - ρ) * h s) (𝓝[≠] ρ) (𝓝 (c + 0 * h ρ)) :=
    (h0.mul (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).const_add c
  have h3 : (fun s : ℂ => (s - ρ) * Φ s) =ᶠ[𝓝[≠] ρ] fun s : ℂ => c + (s - ρ) * h s := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
    have : s - ρ ≠ 0 := sub_ne_zero.mpr hne
    rw [hs]; field_simp
  have := tendsto_nhds_unique (h1.congr' h3) h2
  apply hc
  simpa using this.symm

end Deduction

end
