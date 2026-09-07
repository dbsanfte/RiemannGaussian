import RiemannGaussian.EtaPhaseProjectionMargin
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite

/-!
# Finite eta arithmetic in the projection zero margin

The boundary phase value is replaced by the original finite paired eta
prefix. Its complete analytic tail gives an explicit error at every
arithmetic cutoff. The resulting lower norm and rational zero margin
apply to every actual zero, with no numerical or analytic premise.
-/

open Complex Set

namespace RiemannGaussian

noncomputable section

/-- The literal finite paired eta prefix with its original complex boundary normalization. -/
def pairedEtaFinitePhaseBoundaryValue (N : ℕ) (y : ℝ) : ℂ :=
  pairedEtaCorePartialSum N (1 + (y : ℂ) * Complex.I) / (1 + (y : ℂ) * Complex.I)

/-- The full finite boundary-phase error is at most the reciprocal original odd endpoint. -/
theorem norm_pairedEtaPhaseBoundaryValue_sub_finite_le (N : ℕ) (y : ℝ) :
    ‖pairedEtaPhaseBoundaryValue y - pairedEtaFinitePhaseBoundaryValue N y‖ ≤ 1 / (2 * N + 1 : ℝ) := by
  let s : ℂ := 1 + (y : ℂ) * Complex.I
  have hs : s.re = 1 := by simp [s]
  have hsn : s ≠ 0 := by intro h; have hh := congrArg Complex.re h; rw [hs] at hh; norm_num at hh
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hsn
  have h := norm_pairedEtaCore_sub_partialSum_le (s := s) (by rw [hs]; norm_num) N
  rw [pairedEtaPhaseBoundaryValue_eq_core_div, pairedEtaFinitePhaseBoundaryValue, ← sub_div, norm_div]
  change ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ / ‖s‖ ≤ _
  apply (div_le_iff₀ hnorm).mpr
  simpa only [hs, neg_one_mul, Real.rpow_neg_one, div_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, one_div, mul_comm] using h

/-- One exactly evaluated prefix and the proved analytic tail give a strict global mass bound for this projection. -/
theorem norm_pairedEtaPhaseBoundaryValue_le_five_sixths (y : ℝ) :
    ‖pairedEtaPhaseBoundaryValue y‖ ≤ 5 / 6 := by
  have hprefix : pairedEtaFinitePhaseBoundaryValue 1 0 = (1 / 2 : ℂ) := by
    norm_num [pairedEtaFinitePhaseBoundaryValue, pairedEtaCorePartialSum, pairedEtaCoreSummand,
      Complex.cpow_neg_one]
  have h := norm_pairedEtaPhaseBoundaryValue_sub_finite_le 1 0
  rw [hprefix] at h
  have hnorm := norm_sub_norm_le (pairedEtaPhaseBoundaryValue 0) (1 / 2 : ℂ)
  norm_num at h hnorm
  exact (norm_pairedEtaPhaseBoundaryValue_le_zero y).trans (by linarith)

/-- A finite arithmetic lower bound for the full boundary-phase norm after its proved tail allowance. -/
def etaFinitePhaseNormLower (N : ℕ) (y : ℝ) : ℝ :=
  max 0 (‖pairedEtaFinitePhaseBoundaryValue N y‖ - 1 / (2 * N + 1 : ℝ))

/-- The finite phase lower bound is nonnegative. -/
theorem etaFinitePhaseNormLower_nonneg (N : ℕ) (y : ℝ) : 0 ≤ etaFinitePhaseNormLower N y :=
  le_max_left _ _

/-- Every finite phase lower bound is justified against the actual infinite boundary value. -/
theorem etaFinitePhaseNormLower_le_norm (N : ℕ) (y : ℝ) :
    etaFinitePhaseNormLower N y ≤ ‖pairedEtaPhaseBoundaryValue y‖ := by
  have h := norm_sub_norm_le (pairedEtaFinitePhaseBoundaryValue N y) (pairedEtaPhaseBoundaryValue y)
  rw [norm_sub_rev] at h
  unfold etaFinitePhaseNormLower
  exact max_le (norm_nonneg _) (by linarith [norm_pairedEtaPhaseBoundaryValue_sub_finite_le N y])

/-- The finite lower bound approaches the true boundary norm with a complete explicit error. -/
theorem norm_sub_etaFinitePhaseNormLower_le (N : ℕ) (y : ℝ) :
    ‖pairedEtaPhaseBoundaryValue y‖ - etaFinitePhaseNormLower N y ≤ 2 / (2 * N + 1 : ℝ) := by
  have h := norm_sub_norm_le (pairedEtaPhaseBoundaryValue y) (pairedEtaFinitePhaseBoundaryValue N y)
  have he := norm_pairedEtaPhaseBoundaryValue_sub_finite_le N y
  have hl : ‖pairedEtaFinitePhaseBoundaryValue N y‖ - 1 / (2 * N + 1 : ℝ) ≤ etaFinitePhaseNormLower N y :=
    le_max_right _ _
  rw [show 2 / (2 * N + 1 : ℝ) = 2 * (1 / (2 * N + 1 : ℝ)) by ring]
  linarith

/-- The finite arithmetic phase lower bound has the same unit normalization as the full transform. -/
theorem etaFinitePhaseNormLower_le_one (N : ℕ) (y : ℝ) : etaFinitePhaseNormLower N y ≤ 1 :=
  (etaFinitePhaseNormLower_le_norm N y).trans (norm_pairedEtaPhaseBoundaryValue_le_one y)

/-- The zero margin computed from one literal finite eta prefix and its complete tail budget. -/
def etaFinitePhaseZeroMargin (N : ℕ) (y : ℝ) : ℝ :=
  etaFinitePhaseNormLower N y / (1 + etaFinitePhaseNormLower N y)

/-- The finite arithmetic zero margin is nonnegative. -/
theorem etaFinitePhaseZeroMargin_nonneg (N : ℕ) (y : ℝ) : 0 ≤ etaFinitePhaseZeroMargin N y := by
  have h := etaFinitePhaseNormLower_nonneg N y
  unfold etaFinitePhaseZeroMargin
  positivity

/-- The finite arithmetic margin never exceeds the proved full projection margin. -/
theorem etaFinitePhaseZeroMargin_le_projection (N : ℕ) (y : ℝ) :
    etaFinitePhaseZeroMargin N y ≤ etaPhaseProjectionZeroMargin y := by
  have h0 := etaFinitePhaseNormLower_nonneg N y
  have h := etaFinitePhaseNormLower_le_norm N y
  unfold etaFinitePhaseZeroMargin etaPhaseProjectionZeroMargin
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The finite projection margin retains the natural half-strip bound. -/
theorem etaFinitePhaseZeroMargin_le_half (N : ℕ) (y : ℝ) : etaFinitePhaseZeroMargin N y ≤ 1 / 2 :=
  (etaFinitePhaseZeroMargin_le_projection N y).trans (etaPhaseProjectionZeroMargin_le_half y)

/-- The rational projection step does not increase the finite norm error. -/
theorem etaPhaseProjectionZeroMargin_sub_finite_le (N : ℕ) (y : ℝ) :
    etaPhaseProjectionZeroMargin y - etaFinitePhaseZeroMargin N y ≤ 2 / (2 * N + 1 : ℝ) := by
  let q := ‖pairedEtaPhaseBoundaryValue y‖
  let r := etaFinitePhaseNormLower N y
  have hq : 0 ≤ q := norm_nonneg _
  have hr : 0 ≤ r := etaFinitePhaseNormLower_nonneg N y
  have hrq : r ≤ q := etaFinitePhaseNormLower_le_norm N y
  have he : etaPhaseProjectionZeroMargin y - etaFinitePhaseZeroMargin N y =
      (q - r) / ((1 + q) * (1 + r)) := by
    change q / (1 + q) - r / (1 + r) = (q - r) / ((1 + q) * (1 + r))
    field_simp [show 1 + q ≠ 0 by positivity, show 1 + r ≠ 0 by positivity]
    ring
  rw [he]
  apply (div_le_self (by linarith : 0 ≤ q - r) (by nlinarith [mul_nonneg hq hr] : 1 ≤ (1 + q) * (1 + r))).trans
  exact norm_sub_etaFinitePhaseNormLower_le N y

/-- Every actual nontrivial zero satisfies the explicit margin from every original finite paired eta prefix. -/
theorem nontrivialZetaZero_mem_etaFinitePhase_strip (rho : NontrivialZetaZero) (N : ℕ) :
    rho.1.re ∈ Icc (etaFinitePhaseZeroMargin N rho.1.im) (1 - etaFinitePhaseZeroMargin N rho.1.im) := by
  have hz := nontrivialZetaZero_mem_etaPhaseProjection_strip rho
  have hm := etaFinitePhaseZeroMargin_le_projection N rho.1.im
  constructor <;> linarith [hz.1, hz.2]

end

end RiemannGaussian
