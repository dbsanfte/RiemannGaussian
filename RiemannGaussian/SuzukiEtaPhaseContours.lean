/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaDyadicPhaseBounds
import RiemannGaussian.SuzukiEtaContourGeometry

/-!
# Actual expanding contours with controlled dyadic phases

Admissible vertical sides can be chosen in open negative-cosine bands.
Such bands meet both of the required unit windows at arbitrarily large
outer scales. Thus the signed dyadic estimates are available on genuine
contours, simultaneously over both full vertical strip segments.
The complete carrier singular set is still avoided.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- Every open interval meeting a negative dyadic phase band contains
a genuine eta-compatible vertical side in the same band. -/
theorem exists_suzukiXiEtaVerticalAdmissible_negative_phase {a b v : ℝ}
    (hv : v ∈ Ioo a b) (hphase : Real.cos (v * Real.log 2) < 0) :
    ∃ w ∈ Ioo a b, SuzukiXiEtaVerticalAdmissible w ∧ Real.cos (w * Real.log 2) < 0 := by
  let U : Set ℝ := Ioo a b ∩ {w | Real.cos (w * Real.log 2) < 0}
  have hU : IsOpen U := isOpen_Ioo.inter
    (isOpen_lt (by fun_prop : Continuous (fun w : ℝ => Real.cos (w * Real.log 2))) continuous_const)
  obtain ⟨a', b', hab, hsub⟩ := hU.exists_Ioo_subset ⟨v, hv, hphase⟩
  obtain ⟨w, hw, hadm⟩ := exists_suzukiXiEtaVerticalAdmissible hab
  exact ⟨w, (hsub hw).1, hadm, (hsub hw).2⟩

/-- There are arbitrarily large outer scales whose two side windows
have their midpoint at the most negative dyadic cosine. -/
theorem exists_arbitrarily_large_negative_dyadic_phase_scale (M : ℝ) :
    ∃ R : ℝ, M < R ∧ Real.cos ((R + 1 / 2) * Real.log 2) = -1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let P := 2 * Real.pi / Real.log 2
  have hP : 0 < P := div_pos (by positivity) hl
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + 1 / 2) / P)
  have hlarge := (div_lt_iff₀ hP).mp hn
  refine ⟨(n : ℝ) * P + Real.pi / Real.log 2 - 1 / 2, ?_, ?_⟩
  · have hp : 0 < Real.pi / Real.log 2 := div_pos Real.pi_pos hl
    linarith
  · have he : ((n : ℝ) * P + Real.pi / Real.log 2 - 1 / 2 + 1 / 2) * Real.log 2 =
        (n : ℝ) * (2 * Real.pi) + Real.pi := by
      dsimp [P]
      field_simp
      ring
    rw [he, Real.cos_nat_mul_two_pi_add_pi]

/-- An outer scale with a favorable midpoint admits actual signed
Suzuki contours whose two vertical sides both have favorable phases. -/
theorem exists_suzukiXiEtaRealRectangleAdmissible_negative_phase {R : ℝ}
    (hR : 1 ≤ R) (hphase : Real.cos ((R + 1 / 2) * Real.log 2) < 0) :
    ∃ l r u : ℝ, SuzukiXiCarrierRealRectangleAdmissible l r u ∧
      SuzukiXiEtaVerticalAdmissible l ∧ SuzukiXiEtaVerticalAdmissible r ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧
      (R < u ∧ u < R + 1) ∧
      Real.cos (l * Real.log 2) < 0 ∧ Real.cos (r * Real.log 2) < 0 := by
  have hlphase : Real.cos ((-(R + 1 / 2)) * Real.log 2) < 0 := by
    simpa only [neg_mul, Real.cos_neg] using hphase
  obtain ⟨l, hl, hlsafe, hlcos⟩ := exists_suzukiXiEtaVerticalAdmissible_negative_phase
    (a := -R - 1) (b := -R) (v := -(R + 1 / 2)) ⟨by linarith, by linarith⟩ hlphase
  obtain ⟨r, hr, hrsafe, hrcos⟩ := exists_suzukiXiEtaVerticalAdmissible_negative_phase
    (a := R) (b := R + 1) (v := R + 1 / 2) ⟨by linarith, by linarith⟩ hphase
  obtain ⟨u, hu, husafe⟩ := exists_suzukiXiCarrier_safe_coordinate
    (a := R) (b := R + 1) (by linarith)
  exact ⟨l, r, u, ⟨by linarith [hl.2, hr.1], by linarith [hu.1], fun c hc =>
    ⟨hlsafe.1 c hc, hrsafe.1 c hc, (husafe c hc).2⟩⟩,
    hlsafe, hrsafe, hl, hr, hu, hlcos, hrcos⟩

/-- Favorable phases coexist with every geometric requirement of the
expanding source-energy contour limit, beyond any prescribed inner size. -/
theorem exists_suzukiXiEtaPhase_contour_family (A : ℝ) :
    ∃ R l r u : ℕ → ℝ, Tendsto R atTop atTop ∧
      ∀ n, 1 ≤ R n ∧ A ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) ∧
        Real.cos (l n * Real.log 2) < 0 ∧ Real.cos (r n * Real.log 2) < 0 := by
  let B := max 1 A
  choose R hRlarge hRphase using fun n : ℕ =>
    exists_arbitrarily_large_negative_dyadic_phase_scale ((n : ℝ) + B)
  have hR (n : ℕ) : 1 ≤ R n := by
    have := hRlarge n
    dsimp only [B] at this
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_left (1 : ℝ) A]
  have ha (n : ℕ) : A ≤ R n := by
    have := hRlarge n
    dsimp only [B] at this
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_right (1 : ℝ) A]
  have hlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => (hRlarge n).le)
      (tendsto_atTop_add_const_right atTop B tendsto_natCast_atTop_atTop)
  choose l r u hadm hlv hrv hl hr hu hlcos hrcos using fun n =>
    exists_suzukiXiEtaRealRectangleAdmissible_negative_phase (hR n) (by rw [hRphase n]; norm_num)
  exact ⟨R, l, r, u, hlim, fun n =>
    ⟨hR n, ha n, hadm n, hl n, hr n, hu n, hlv n, hrv n, hlcos n, hrcos n⟩⟩

/-- The dyadic phase is constant along the entire original vertical
line after the reflected arithmetic coordinate change. -/
theorem cos_suzukiArithmeticZetaArgument_vertical (v y : ℝ) :
    Real.cos ((suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)).im * Real.log 2) =
      Real.cos (v * Real.log 2) := by
  simp [suzukiArithmeticZetaArgument, neg_mul, Real.cos_neg]

/-- Along every favorable vertical side, the full closed strip has
the independent signed dyadic bound, uniformly in its height. -/
theorem pairedEtaFactorLogDerivative_re_vertical_strip_bounds {v : ℝ}
    (hphase : Real.cos (v * Real.log 2) ≤ 0) {y : ℝ} (hy : y ∈ Icc 0 (1 / 2)) :
    Real.log 2 / 2 ≤
        -(pairedEtaFactorLogDerivative (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I))).re ∧
      -(pairedEtaFactorLogDerivative (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I))).re ≤
        2 * Real.log 2 / 3 := by
  apply pairedEtaFactorLogDerivative_re_phase_strip_bounds
  · rw [suzukiArithmeticZetaArgument_re]
    simpa using hy.1
  · rw [suzukiArithmeticZetaArgument_re]
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    linarith [hy.2]
  · rwa [cos_suzukiArithmeticZetaArgument_vertical]

end
end RiemannGaussian
