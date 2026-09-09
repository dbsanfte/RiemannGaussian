/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaPhaseContours
import RiemannGaussian.EtaDyadicQuadrantBounds

/-!
# Contour phases matched to the two vertical orientations

The right side can have negative cosine and sine greater than one half;
the left side can have negative cosine and sine less than minus one
half. These conditions hold on actual admissible expanding contours,
with the same unit side windows as the original source comparison.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

private lemma phase_coordinate {a b v : ℝ} (o : ℝ) (hv : v ∈ Ioo a b)
    (hcos : Real.cos (v * Real.log 2) < 0) (hsin : 1 / 2 < o * Real.sin (v * Real.log 2)) :
    ∃ w ∈ Ioo a b, SuzukiXiEtaVerticalAdmissible w ∧
      Real.cos (w * Real.log 2) < 0 ∧ 1 / 2 < o * Real.sin (w * Real.log 2) := by
  let U : Set ℝ := Ioo a b ∩ {w | Real.cos (w * Real.log 2) < 0 ∧
    1 / 2 < o * Real.sin (w * Real.log 2)}
  have hU : IsOpen U := isOpen_Ioo.inter
    ((isOpen_lt (by fun_prop : Continuous (fun w : ℝ => Real.cos (w * Real.log 2))) continuous_const).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous (fun w : ℝ => o * Real.sin (w * Real.log 2)))))
  obtain ⟨a', b', hab, hsub⟩ := hU.exists_Ioo_subset ⟨v, hv, hcos, hsin⟩
  obtain ⟨w, hw, hadm⟩ := exists_suzukiXiEtaVerticalAdmissible hab
  exact ⟨w, (hsub hw).1, hadm, (hsub hw).2⟩

/-- Arbitrarily large side windows meet a fixed favorable quadrant
with a uniform signed sine margin. No zero-location premise is used. -/
theorem exists_arbitrarily_large_oriented_dyadic_phase_scale (M : ℝ) :
    ∃ R : ℝ, M < R ∧ Real.cos ((R + 1 / 2) * Real.log 2) < 0 ∧
      1 / 2 < Real.sin ((R + 1 / 2) * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let P := 2 * Real.pi / Real.log 2
  have hP : 0 < P := div_pos (by positivity) hl
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + 1 / 2) / P)
  have hlarge := (div_lt_iff₀ hP).mp hn
  let theta := Real.pi - Real.pi / 4
  have ht : 0 < theta := by dsimp [theta]; linarith [Real.pi_pos]
  have he : ((n : ℝ) * P + theta / Real.log 2 - 1 / 2 + 1 / 2) * Real.log 2 =
      theta + (n : ℝ) * (2 * Real.pi) := by
    dsimp [P]
    field_simp
    ring
  refine ⟨(n : ℝ) * P + theta / Real.log 2 - 1 / 2, ?_, ?_, ?_⟩
  · have htheta : 0 < theta / Real.log 2 := div_pos ht hl
    linarith
  · rw [he, Real.cos_add_nat_mul_two_pi]
    dsimp [theta]
    rw [Real.cos_pi_sub, Real.cos_pi_div_four]
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  · rw [he, Real.sin_add_nat_mul_two_pi]
    dsimp [theta]
    rw [Real.sin_pi_sub, Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- The opposite sine signs required by the two oriented vertical
sides are compatible with genuine contour admissibility. -/
theorem exists_suzukiXiEtaRealRectangleAdmissible_oriented_phase {R : ℝ}
    (hR : 1 ≤ R) (hcos : Real.cos ((R + 1 / 2) * Real.log 2) < 0)
    (hsin : 1 / 2 < Real.sin ((R + 1 / 2) * Real.log 2)) :
    ∃ l r u : ℝ, SuzukiXiCarrierRealRectangleAdmissible l r u ∧
      SuzukiXiEtaVerticalAdmissible l ∧ SuzukiXiEtaVerticalAdmissible r ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧ (R < u ∧ u < R + 1) ∧
      Real.cos (l * Real.log 2) < 0 ∧ Real.cos (r * Real.log 2) < 0 ∧
      Real.sin (l * Real.log 2) < -1 / 2 ∧ 1 / 2 < Real.sin (r * Real.log 2) := by
  obtain ⟨l, hl, hlv, hlcos, hlsin⟩ := phase_coordinate (-1)
    (a := -R - 1) (b := -R) (v := -(R + 1 / 2)) ⟨by linarith, by linarith⟩
    (by simpa only [neg_mul, Real.cos_neg] using hcos)
    (by simpa only [neg_mul, Real.sin_neg, one_mul, neg_neg] using hsin)
  obtain ⟨r, hr, hrv, hrcos, hrsin⟩ := phase_coordinate 1
    (a := R) (b := R + 1) (v := R + 1 / 2) ⟨by linarith, by linarith⟩ hcos
    (by simpa only [one_mul] using hsin)
  obtain ⟨u, hu, husafe⟩ := exists_suzukiXiCarrier_safe_coordinate
    (a := R) (b := R + 1) (by linarith)
  refine ⟨l, r, u, ⟨by linarith [hl.2, hr.1], by linarith [hu.1], fun c hc =>
    ⟨hlv.1 c hc, hrv.1 c hc, (husafe c hc).2⟩⟩,
    hlv, hrv, hl, hr, hu, hlcos, hrcos, ?_, ?_⟩
  · linarith
  · simpa only [one_mul] using hrsin

/-- Actual expanding contours can satisfy both oriented quadrant
conditions and start beyond every prescribed inner scale. -/
theorem exists_suzukiXiEtaOrientedPhase_contour_family (A : ℝ) :
    ∃ R l r u : ℕ → ℝ, Tendsto R atTop atTop ∧
      ∀ n, 200 ≤ R n ∧ A ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) ∧
        Real.cos (l n * Real.log 2) < 0 ∧ Real.cos (r n * Real.log 2) < 0 ∧
        Real.sin (l n * Real.log 2) < -1 / 2 ∧ 1 / 2 < Real.sin (r n * Real.log 2) := by
  let B := max 200 A
  choose R hRlarge hRcos hRsin using fun n : ℕ =>
    exists_arbitrarily_large_oriented_dyadic_phase_scale ((n : ℝ) + B)
  have hR (n : ℕ) : 200 ≤ R n := by
    have := hRlarge n
    dsimp only [B] at this
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_left (200 : ℝ) A]
  have ha (n : ℕ) : A ≤ R n := by
    have := hRlarge n
    dsimp only [B] at this
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_right (200 : ℝ) A]
  have hlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => (hRlarge n).le)
      (tendsto_atTop_add_const_right atTop B tendsto_natCast_atTop_atTop)
  choose l r u hadm hlv hrv hl hr hu hlcos hrcos hlsin hrsin using fun n =>
    exists_suzukiXiEtaRealRectangleAdmissible_oriented_phase (by linarith [hR n]) (hRcos n) (hRsin n)
  exact ⟨R, l, r, u, hlim, fun n =>
    ⟨hR n, ha n, hadm n, hl n, hr n, hu n, hlv n, hrv n, hlcos n, hrcos n, hlsin n, hrsin n⟩⟩

end
end RiemannGaussian
