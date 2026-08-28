import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaJensen

/-!
# Separation of the moving critical endpoint from local eta zeros

The paired eta function has two kinds of zeros in the moving disk: genuine
zeta zeros and zeros of the explicit factor `1 - 2 * 2 ^ (-s)`.  This module
classifies those alternatives directly from the checked eta factorization.

The quantitative contour construction already separates the critical
endpoint from every genuine zeta zero.  An eta-factor zero lies on `re s = 1`,
so it remains at least `1 / 2` away horizontally.  Since the existing
quantitative separation radius is at most `1 / 6`, one common separation
radius controls every zero in the local eta divisor.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every zero of the elementary eta factor lies on `re s = 1`. -/
lemma re_eq_one_of_pairedEtaFactor_eq_zero
    {s : ℂ} (hfactor : 1 - (2 : ℂ) * (2 : ℂ) ^ (-s) = 0) :
    s.re = 1 := by
  have heq : (2 : ℂ) * (2 : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hfactor).symm
  have hnorm := congrArg norm heq
  have hcpow : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    change ‖((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have hrpow : (2 : ℝ) ^ (1 - s.re) = (2 : ℝ) ^ (0 : ℝ) := by
    calc
      (2 : ℝ) ^ (1 - s.re) =
          (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s.re) := by
        rw [show 1 - s.re = (1 : ℝ) + (-s.re) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * ‖(2 : ℂ) ^ (-s)‖ := by
        rw [Real.rpow_one, hcpow]
      _ = ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ := by
        rw [norm_mul]
        norm_num
      _ = 1 := by rw [heq]; norm_num
      _ = (2 : ℝ) ^ (0 : ℝ) := by norm_num
  have hexponent : 1 - s.re = 0 :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      hrpow
  linarith

/-- The quantitative contour radius is always at most `1 / 6`; hence it is
smaller than the fixed horizontal separation from an eta-factor zero. -/
lemma spectralBoundarySeparation_le_one_six (n : ℕ) :
    spectralBoundarySeparation n ≤ 1 / 6 := by
  unfold spectralBoundarySeparation
  have hcardNonneg : (0 : ℝ) ≤
      ((spectralBoundaryObstructions n).card : ℝ) := Nat.cast_nonneg _
  have hcard : (2 : ℝ) ≤
      ((spectralBoundaryObstructions n).card : ℝ) + 2 := by linarith
  have hden : (6 : ℝ) ≤
      3 * (((spectralBoundaryObstructions n).card : ℝ) + 2) := by
    nlinarith
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hden)

/-- A local eta-divisor point is an actual zero of the translated eta
function. -/
lemma staticContourLocalEta_eq_zero_of_divisor_ne_zero
    {T : ℝ} {i : ℂ}
    (hi : divisor (staticContourLocalEta T)
      (ball 0 staticContourLocalEtaInnerRadius) i ≠ 0) :
    staticContourLocalEta T i = 0 := by
  have himem : i ∈ ball (0 : ℂ) staticContourLocalEtaInnerRadius :=
    (divisor (staticContourLocalEta T)
      (ball 0 staticContourLocalEtaInnerRadius)).supportWithinDomain hi
  have hanalyticOuter := analyticOnNhd_staticContourLocalEta_closedBall T
  have hanalytic : AnalyticOnNhd ℂ (staticContourLocalEta T)
      (ball 0 staticContourLocalEtaInnerRadius) :=
    hanalyticOuter.mono (fun z hz => by
      apply ball_subset_closedBall
      exact (ball_subset_ball staticContourLocalEtaInnerRadius_lt_outer.le) hz)
  by_contra hzero
  have horder : meromorphicOrderAt (staticContourLocalEta T) i = 0 :=
    (hanalytic i himem).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hzero
  rw [hanalytic.meromorphicOn.divisor_apply himem, horder] at hi
  simp at hi

/-- At quantitative heights beyond the first two unit intervals, every point
of the local eta divisor is either an explicit eta-factor zero or translates
to a nontrivial zeta zero. -/
lemma localEta_divisor_factor_zero_or_nontrivialZetaZero
    {n : ℕ} (hn : 2 ≤ n) {i : ℂ}
    (hi : divisor
      (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n))
      (ball 0 staticContourLocalEtaInnerRadius) i ≠ 0) :
    1 - (2 : ℂ) * (2 : ℂ) ^
          (-(staticContourSafeEndpoint
            (quantitativeSpectralBoundaryTruncation n) + i)) = 0 ∨
      IsNontrivialZetaZero
        (staticContourSafeEndpoint
          (quantitativeSpectralBoundaryTruncation n) + i) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let w : ℂ := staticContourSafeEndpoint T + i
  have himem : i ∈ ball (0 : ℂ) staticContourLocalEtaInnerRadius :=
    (divisor (staticContourLocalEta T)
      (ball 0 staticContourLocalEtaInnerRadius)).supportWithinDomain
        (by simpa [T] using hi)
  have hinorm : ‖i‖ < staticContourLocalEtaInnerRadius := by
    simpa [mem_ball, dist_zero_right] using himem
  have hireLower : -‖i‖ ≤ i.re :=
    (abs_le.mp (Complex.abs_re_le_norm i)).1
  have hiimLower : -‖i‖ ≤ i.im :=
    (abs_le.mp (Complex.abs_im_le_norm i)).1
  have hwre : 0 < w.re := by
    dsimp [w, staticContourSafeEndpoint]
    simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    rw [staticContourLocalEtaInnerRadius] at hinorm
    linarith
  have hT : (n : ℝ) < T := by
    simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hwim : 0 < w.im := by
    dsimp [w, staticContourSafeEndpoint]
    simp only [ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, zero_mul, add_zero]
    rw [staticContourLocalEtaInnerRadius] at hinorm
    linarith
  have hetaZero : pairedEtaCore w = 0 := by
    have hzero := staticContourLocalEta_eq_zero_of_divisor_ne_zero
      (T := T) (i := i) (by simpa [T] using hi)
    simpa [staticContourLocalEta, w] using hzero
  have heta := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    hwre hwim
  rw [heta, mul_eq_zero] at hetaZero
  rcases hetaZero with hfactor | hzeta
  · exact Or.inl (by simpa [T, w] using hfactor)
  · right
    refine ⟨hzeta, ?_, ?_⟩
    · rintro ⟨m, hm⟩
      change w = -2 * ((m : ℂ) + 1) at hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [hwre]
    · intro hwone
      change w = 1 at hwone
      have him := congrArg Complex.im hwone
      norm_num at him
      linarith [hwim]

/-- The `s`-plane distance from the critical endpoint equals the spectral
distance used by the quantitative contour theorem. -/
lemma norm_criticalLocal_sub_eq_spectralDistance
    (T : ℝ) (i : ℂ) :
    ‖((-1 : ℂ) - i)‖ =
      ‖(T : ℂ) - zetaSpectralCoordinate
        (staticContourSafeEndpoint T + i)‖ := by
  calc
    ‖((-1 : ℂ) - i)‖ = ‖-((1 : ℂ) + i)‖ := by
      congr 1
      ring
    _ = ‖(1 : ℂ) + i‖ := norm_neg _
    _ = ‖Complex.I * ((1 : ℂ) + i)‖ := by simp
    _ = ‖(T : ℂ) - zetaSpectralCoordinate
        (staticContourSafeEndpoint T + i)‖ := by
      congr 1
      simp [zetaSpectralCoordinate, staticContourSafeEndpoint]
      ring_nf
      rw [Complex.I_sq]
      simp

/-- The critical local point `-1` is separated by the existing quantitative
radius from every zero in the moving eta divisor.  This combines genuine
zeta-zero separation with the fixed half-unit gap to eta-factor zeros. -/
theorem spectralBoundarySeparation_le_norm_criticalLocal_sub_of_etaDivisor
    {n : ℕ} (hn : 2 ≤ n) {i : ℂ}
    (hi : divisor
      (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n))
      (ball 0 staticContourLocalEtaInnerRadius) i ≠ 0) :
    spectralBoundarySeparation n ≤ ‖(-1 : ℂ) - i‖ := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let w : ℂ := staticContourSafeEndpoint T + i
  rcases localEta_divisor_factor_zero_or_nontrivialZetaZero hn hi with
    hfactor | hw
  · have hwre : w.re = 1 := by
      apply re_eq_one_of_pairedEtaFactor_eq_zero
      simpa [T, w] using hfactor
    have hire : i.re = -(1 / 2 : ℝ) := by
      dsimp [w, staticContourSafeEndpoint] at hwre
      simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero] at hwre
      linarith
    calc
      spectralBoundarySeparation n ≤ 1 / 6 :=
        spectralBoundarySeparation_le_one_six n
      _ ≤ 1 / 2 := by norm_num
      _ = |(((-1 : ℂ) - i).re)| := by
        symm
        calc
          |(((-1 : ℂ) - i).re)| = |-(1 / 2 : ℝ)| := by
            congr 1
            simp [hire]
            ring
          _ = 1 / 2 := by norm_num
      _ ≤ ‖(-1 : ℂ) - i‖ := Complex.abs_re_le_norm _
  · let ρ : NontrivialZetaZero := ⟨w, hw⟩
    have hsep := quantitativeSpectralBoundaryTruncation_dist_zero_ge n 0 ρ
    rw [norm_criticalLocal_sub_eq_spectralDistance T i]
    simpa [T, w, ρ] using hsep

end

end RiemannGaussian
