import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleAsym
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauTails
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauKernelMax
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindowIneq
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleReLe
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCoeff
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauNearest
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauGrowthContra

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_window_contra {c d e E M C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e) (heE : e ≤ E)
    (H : ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) : False := by
  obtain ⟨η, hη, U₀, hU₀⟩ := landau_growth_contra (C := |M| + |C|) hc hd hde
  obtain ⟨U, hU, k, hk, hle⟩ := H η hη (max U₀ 0)
  have h1 := hU₀ U ((le_max_left _ _).trans hU) k hk
  have hU0 : 0 ≤ U := (le_max_right _ _).trans hU
  have he : 0 < e := hd.trans hde
  have hek : 0 < e ^ k := pow_pos he k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h2 : M / e ^ k ≤ |M| * Real.exp (η * U) / e ^ k := by
    apply div_le_div_of_nonneg_right _ hek.le
    exact (le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp)
  have h3 : C * Real.exp (η * U) / E ^ k ≤ |C| * Real.exp (η * U) / e ^ k := by
    apply div_le_div₀ (by positivity) _ hek (pow_le_pow_left₀ he.le heE k)
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have h4 : (|M| + |C|) * Real.exp (η * U) / e ^ k
      = |M| * Real.exp (η * U) / e ^ k + |C| * Real.exp (η * U) / e ^ k := by ring
  linarith

theorem landau_window_key {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧ ∀ γ : ℝ,
      ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        C * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, C, hC⟩ := landau_tails hδ
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀0 : 0 ≤ C₀ := by
    have := hC₀ 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨σ, hσ, 2 + 2 * C₀ * |C|, fun η hη U₀ => ?_⟩
  obtain ⟨U, hU, R, hR1, hR2, hR3⟩ := hW η hη (max U₀ 1)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  obtain ⟨k, hk, hk'⟩ := hC U hU1
  refine ⟨U, (le_max_left _ _).trans hU, k, hk, fun γ => ?_⟩
  have h := landau_window_ineq hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith : 0 < U) hR1 hR2 k γ
  rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
    landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
  have hst : 0 < σ - θ := by linarith
  have hstk : 0 < (σ - θ) ^ k := pow_pos hst k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h1 : 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u))
      ≤ 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) :=
    mul_le_mul_of_nonneg_left hR3 (by positivity)
  have h2 : C / σ ^ k ≤ |C| * Real.exp (η * U) / (σ - θ) ^ k := by
    apply div_le_div₀ (by positivity) _ hstk (pow_le_pow_left₀ hst.le (by linarith) k)
    exact (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hexp)
  have h3 := mul_le_mul_of_nonneg_left (hk'.trans h2) (by positivity : 0 ≤ 2 * C₀)
  have h4 : (2 + 2 * C₀ * |C|) * Real.exp (η * U) / (σ - θ) ^ k
      = 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U)
        + 2 * C₀ * (|C| * Real.exp (η * U) / (σ - θ) ^ k) := by ring
  linarith

theorem landau_window_re_pos {z w : ℂ} {r : ℝ} (hr : r ≤ z.re) (hw : w ∈ Metric.ball z r) :
    0 < w.re := by
  have h1 : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
  have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  have h3 := (abs_lt.mp (h2.trans_lt h1)).1
  simp only [Complex.sub_re] at h3
  linarith

theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ₀ h₀
  by_contra hρ₀
  rw [not_le] at hρ₀
  obtain ⟨σ, hσ, C, hkey⟩ := landau_window_key hP hθ hθ1 hδ hW
  have hle : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (landau_pole_re_le hP ρ hρ).trans_lt hσ
  rcases landau_dichotomy hP.iso hle hθ (by linarith) h₀ hρ₀ with
    ⟨D, hD, hfree, ρ₁, h₁, hρ₁⟩ | ⟨β, hβZ, hβ, r, hr1, hr2, huniq⟩
  · obtain ⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩ := landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁
    obtain ⟨c, hc, -, hp⟩ := hP.pole ρ hρ
    set z : ℂ := (σ : ℂ) + γ * I with hz
    have hzre : z.re = σ := by simp [hz]
    have hne : ρ ≠ z := by
      intro h
      have := hle ρ hρ
      rw [h, hzre] at this
      exact lt_irrefl _ this
    have hd : 0 < ‖z - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
    set d := ‖z - ρ‖ with hddef
    have hball : ρ ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [hzre]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩
    have hdiff' : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D) := by
      refine hP.diff.mono ?_
      intro w hw
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hfree w hZ hw⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    obtain ⟨M', hM'⟩ := landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)
    refine landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ) (M := M + M') (C := C)
      (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb γ
    have h2 := hM k
    have h3 := hM' k
    have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k := by
      rw [norm_div, norm_pow, pow_succ', div_div]
    have h5 : ‖(-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖
        = ‖iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖ := by
      rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)))).1
    have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
      ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))
    rw [norm_sub_rev] at h7
    rw [add_div]
    linarith
  · obtain ⟨c, -, hc, hp⟩ := hP.pole β hβZ
    obtain ⟨hc1, hc2⟩ := hc (Complex.ofReal_im β)
    have hd : 0 < σ - β := by
      have := hle β hβZ
      rw [Complex.ofReal_re] at this
      linarith
    have hne : (β : ℂ) ≠ (σ : ℂ) := by
      intro h
      have : β = σ := by exact_mod_cast h
      linarith
    have hball : (β : ℂ) ∈ Metric.ball (σ : ℂ) r := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
      exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) r \ {(β : ℂ)}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw,
        fun hZ => hw' (huniq w hZ hw)⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ)
      (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb 0
    have h2 := hM k
    have h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1
    rw [Complex.sub_re, h4] at h6
    have h7 := norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))
    linarith

end Deduction

end
