/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaCurvatureGaussian
import RiemannGaussian.EtaZetaPoleBounds
import Mathlib.Analysis.Complex.Liouville

/-!
# Infinite eta curvature under Gaussian averaging

Cauchy estimates give one polynomial majorant for every eta prefix and
its first two derivatives. Dominated convergence then transports the
cutoff-independent Gaussian estimate to the actual infinite eta function
on every positive vertical line. This is a bound for the bare curvature;
the full normalized reflected source remains a separate obligation.
-/

open Complex Filter MeasureTheory Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- Every literal eta prefix has a uniform linear bound in the positive
half-plane. Its constant is independent of the prefix length. -/
theorem norm_pairedEtaCorePartialSum_le_two_div_re (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaCorePartialSum N s‖ ≤ 2 * ‖s‖ / s.re := by
  have hp : (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  have ht := norm_pairedEtaCore_sub_partialSum_le hs N
  have hb : ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤ ‖s‖ / s.re := by
    apply ht.trans
    calc
      _ ≤ ‖s‖ * (1 / s.re) := by gcongr
      _ = _ := by ring
  have h := norm_sub_le (pairedEtaCore s) (pairedEtaCore s - pairedEtaCorePartialSum N s)
  rw [sub_sub_cancel] at h
  have he := norm_pairedEtaCore_le_div_re hs
  calc
    _ ≤ ‖pairedEtaCore s‖ + ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ := h
    _ ≤ ‖s‖ / s.re + ‖s‖ / s.re := add_le_add he hb
    _ = _ := by ring

/-- Cauchy's estimate controls every fixed derivative order of every eta
prefix using the same positive-half-plane circle. -/
theorem norm_iteratedDeriv_pairedEtaCorePartialSum_le (N k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖iteratedDeriv k (pairedEtaCorePartialSum N) s‖ ≤
      (k.factorial : ℝ) * (2 * (‖s‖ + s.re / 2) / (s.re / 2)) / (s.re / 2) ^ k := by
  have hr : 0 < s.re / 2 := by positivity
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    (differentiable_pairedEtaCorePartialSum N).diffContOnCl
  intro w hw
  have hd : ‖w - s‖ = s.re / 2 := mem_sphere_iff_norm.mp hw
  have hwre : s.re / 2 ≤ w.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (w - s))).1
    rw [Complex.sub_re, hd] at h
    linarith
  have hwn : ‖w‖ ≤ ‖s‖ + s.re / 2 := by
    have h := norm_add_le (w - s) s
    rw [sub_add_cancel, hd] at h
    linarith
  apply (norm_pairedEtaCorePartialSum_le_two_div_re N (hr.trans_le hwre)).trans
  gcongr

private lemma prefix_curvature_bound (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖deriv (pairedEtaCorePartialSum N) s ^ 2 -
      pairedEtaCorePartialSum N s * deriv (deriv (pairedEtaCorePartialSum N)) s‖ ≤
      (12 / (s.re / 2) ^ 4) * (‖s‖ + s.re / 2) ^ 2 := by
  let R := s.re / 2
  let H := ‖s‖ + R
  have hR : 0 < R := by dsimp [R]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have h0 := norm_iteratedDeriv_pairedEtaCorePartialSum_le N 0 hs
  have h1 := norm_iteratedDeriv_pairedEtaCorePartialSum_le N 1 hs
  have h2 := norm_iteratedDeriv_pairedEtaCorePartialSum_le N 2 hs
  norm_num only [iteratedDeriv_zero, iteratedDeriv_one, iteratedDeriv_succ, Nat.factorial,
    Nat.cast_one, Nat.cast_ofNat, one_mul, pow_zero, div_one, pow_one] at h0 h1 h2
  calc
    _ ≤ ‖deriv (pairedEtaCorePartialSum N) s‖ ^ 2 +
        ‖pairedEtaCorePartialSum N s‖ * ‖deriv (deriv (pairedEtaCorePartialSum N)) s‖ := by
      have hn : ‖deriv (pairedEtaCorePartialSum N) s ^ 2‖ =
          ‖deriv (pairedEtaCorePartialSum N) s‖ ^ 2 := Complex.norm_pow _ _
      exact (norm_sub_le _ _).trans_eq (congrArg₂ (fun a b : ℝ => a + b) hn (norm_mul _ _))
    _ ≤ ((2 * H / R) / R) ^ 2 + (2 * H / R) * ((2 * (2 * H / R)) / R ^ 2) := by
      gcongr
    _ = _ := by dsimp [H, R]; field_simp; ring

private lemma curvature_limit {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N => deriv (pairedEtaCorePartialSum N) s ^ 2 -
      pairedEtaCorePartialSum N s * deriv (deriv (pairedEtaCorePartialSum N)) s) atTop
      (𝓝 (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s)) := by
  have h := (tendsto_pairedEtaFiniteLogGapSum hs).const_mul (-(1 / 2 : ℂ))
  have he : -(1 / 2 : ℂ) *
      (-2 * (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s)) =
      deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards with N
  exact (pairedEtaCorePartialSum_curvature_eq_logGap N s).symm

/-- The actual infinite eta curvature is Gaussian integrable and its
integral is recovered from the literal common prefixes. A single
polynomial dominator justifies the infinite-prefix exchange. -/
theorem pairedEta_curvature_gaussian_convergence {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (x : ℝ) :
    Integrable (fun t : ℝ => (translatedGaussian tau x t : ℂ) *
      (deriv pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv pairedEtaCore) ((sigma : ℂ) + (t : ℂ) * I))) ∧
    Tendsto (fun N => ∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
      (deriv (pairedEtaCorePartialSum N) ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCorePartialSum N ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv (pairedEtaCorePartialSum N)) ((sigma : ℂ) + (t : ℂ) * I))) atTop
      (𝓝 (∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
        (deriv pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
          pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) *
            deriv (deriv pairedEtaCore) ((sigma : ℂ) + (t : ℂ) * I)))) := by
  let C := 12 / (sigma / 2) ^ 4
  let L := 3 * sigma / 2 + |x|
  let B (t : ℝ) := C * (2 * L ^ 2 + 2 * (t - x) ^ 2) * translatedGaussian tau x t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : Integrable B := by
    have hq : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-tau * t ^ 2)) := by
      simpa only [Real.rpow_two] using
        (integrable_rpow_mul_exp_neg_mul_sq htau (by norm_num : (-1 : ℝ) < 2))
    have hg := (integrable_exp_neg_mul_sq htau).comp_sub_right x
    have hh := (((hg.const_mul (2 * L ^ 2)).add ((hq.comp_sub_right x).const_mul 2))).const_mul C
    convert hh using 1
    funext t
    dsimp [B, translatedGaussian]
    ring
  have hmeas (N : ℕ) := (integrable_pairedEtaCorePartialSum_curvature_gaussian N sigma htau x).aestronglyMeasurable
  have hbound (N : ℕ) (t : ℝ) :
      ‖(translatedGaussian tau x t : ℂ) *
        (deriv (pairedEtaCorePartialSum N) ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
          pairedEtaCorePartialSum N ((sigma : ℂ) + (t : ℂ) * I) *
            deriv (deriv (pairedEtaCorePartialSum N)) ((sigma : ℂ) + (t : ℂ) * I))‖ ≤ B t := by
    have hs : ((sigma : ℂ) + (t : ℂ) * I).re = sigma := by simp
    have hnorm : ‖(sigma : ℂ) + (t : ℂ) * I‖ ≤ sigma + |t| := by
      simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hsigma] using norm_add_le (sigma : ℂ) ((t : ℂ) * I)
    have ht : |t| ≤ |t - x| + |x| := by
      simpa only [sub_add_cancel] using abs_add_le (t - x) x
    have hnr : ‖(sigma : ℂ) + (t : ℂ) * I‖ + sigma / 2 ≤ L + |t - x| := by dsimp [L]; linarith
    have hnr0 : 0 ≤ ‖(sigma : ℂ) + (t : ℂ) * I‖ + sigma / 2 := by positivity
    have hsquare : (‖(sigma : ℂ) + (t : ℂ) * I‖ + sigma / 2) ^ 2 ≤
        2 * L ^ 2 + 2 * (t - x) ^ 2 := by
      have hh := (sq_le_sq₀ hnr0 (by positivity : 0 ≤ L + |t-x|)).2 hnr
      nlinarith [sq_nonneg (L - |t-x|), sq_abs (t-x)]
    have hp := prefix_curvature_bound N (s := (sigma : ℂ) + (t : ℂ) * I) (by simpa only [hs] using hsigma)
    rw [hs] at hp
    have hcurv := hp.trans (mul_le_mul_of_nonneg_left hsquare hC)
    have hgpos : 0 < translatedGaussian tau x t := Real.exp_pos _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
    exact (mul_le_mul_of_nonneg_left hcurv (Real.exp_pos _).le).trans_eq
      (by dsimp [B, C, translatedGaussian]; ring)
  have hlim (t : ℝ) := (curvature_limit (s := (sigma : ℂ) + (t : ℂ) * I)
    (by simpa using hsigma)).const_mul (translatedGaussian tau x t : ℂ)
  have hlim_ae := ae_of_all (volume : Measure ℝ) hlim
  constructor
  · apply hB.mono' (aestronglyMeasurable_of_tendsto_ae _ hmeas hlim_ae)
    exact Eventually.of_forall fun t => le_of_tendsto (hlim t).norm (Eventually.of_forall fun N => hbound N t)
  · exact tendsto_integral_of_dominated_convergence B hmeas hB
      (fun N => Eventually.of_forall (hbound N)) hlim_ae

/-- The complete infinite eta curvature obeys the same Gaussian bound
on every positive vertical line, uniformly in the Gaussian center. This
is an unconditional arithmetic estimate for the bare curvature only. -/
theorem norm_integral_pairedEta_curvature_gaussian_le {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (htime : tau ≤ Real.log 2 / 32) (x : ℝ) :
    ‖∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
      (deriv pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCore ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv pairedEtaCore) ((sigma : ℂ) + (t : ℂ) * I))‖ ≤
      2 * Real.sqrt (Real.pi / tau) * Real.exp (-(Real.log 2) ^ 2 / (8 * tau)) :=
  le_of_tendsto (pairedEta_curvature_gaussian_convergence hsigma htau x).2.norm
    (Eventually.of_forall fun N =>
      norm_integral_pairedEtaCorePartialSum_curvature_gaussian_le N hsigma.le htau htime x)

private lemma gaussian_curvature_envelope_tendsto :
    Tendsto (fun tau : ℝ => 2 * Real.sqrt (Real.pi / tau) *
      Real.exp (-(Real.log 2) ^ 2 / (8 * tau))) (𝓝[>] 0) (𝓝 0) := by
  have hc : 0 < (Real.log 2) ^ 2 / 8 := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2)
    ((Real.log 2) ^ 2 / 8) hc).const_mul (2 * Real.sqrt Real.pi)).comp tendsto_inv_nhdsGT_zero
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with tau
  change 2 * Real.sqrt Real.pi *
    (tau⁻¹ ^ (1 / 2 : ℝ) * Real.exp (-((Real.log 2) ^ 2 / 8) * tau⁻¹)) = _
  rw [div_eq_mul_inv Real.pi tau, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_eq_rpow tau⁻¹]
  have he : -((Real.log 2) ^ 2 / 8) * tau⁻¹ = -(Real.log 2) ^ 2 / (8 * tau) := by ring
  rw [he]
  ring

/-- The actual bare curvature averages vanish even along arbitrary
moving positive vertical lines and arbitrary moving centers. No bound
on those movements is assumed; Gaussian time tends to zero from above.
The completion and normalized reflection factors are not part of this
integrand. -/
theorem tendsto_pairedEta_curvature_gaussian_moving
    (sigma center : ℝ → ℝ) (hsigma : ∀ᶠ tau in 𝓝[>] (0 : ℝ), 0 < sigma tau) :
    Tendsto (fun tau : ℝ => ∫ t : ℝ, (translatedGaussian tau (center tau) t : ℂ) *
      (deriv pairedEtaCore ((sigma tau : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCore ((sigma tau : ℂ) + (t : ℂ) * I) *
          deriv (deriv pairedEtaCore) ((sigma tau : ℂ) + (t : ℂ) * I)))
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ gaussian_curvature_envelope_tendsto
  have hc : 0 < Real.log 2 / 32 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hsigma, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)] with tau hs ht hu
  exact norm_integral_pairedEta_curvature_gaussian_le hs ht hu.le (center tau)

end
end RiemannGaussian
