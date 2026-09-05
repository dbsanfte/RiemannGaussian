import RiemannGaussian.EtaLogSupportShift
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The critical harmonic boundary law for the eta support

The exact arithmetic displacement expansion becomes a harmonic sum at the
critical tilt. A displacement-dependent cutoff gives a quantitative error
bound for the leading term `r * log (1 / r)`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The resolved boundary harmonic sum omits the non-crossed endpoint at one. -/
theorem sum_Icc_two_inv_eq_harmonic_sub_one {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) = (harmonic M : ℝ) - 1 := by
  have hh : (harmonic M : ℝ) = ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hs := Finset.sum_erase_add (Finset.Icc 1 M) (fun n : ℕ ↦ (n : ℝ)⁻¹)
    (Finset.left_mem_Icc.mpr hM)
  rw [Finset.Icc_erase_left] at hs
  have hset : Finset.Ioc 1 M = Finset.Icc 2 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hs
  norm_num at hs
  linarith

/-- The arithmetic cutoff chosen at the scale of one displacement. -/
def pairedEtaShiftBoundaryCutoff (r : ℝ) : ℕ := ⌊1 / (2 * r)⌋₊

/-- The displacement cutoff resolves at least four boundaries and is
comparable to the reciprocal displacement, with explicit constants. -/
theorem pairedEtaShiftBoundaryCutoff_bounds {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    4 ≤ pairedEtaShiftBoundaryCutoff r ∧
      1 / (4 * r) ≤ (pairedEtaShiftBoundaryCutoff r : ℝ) ∧
      (pairedEtaShiftBoundaryCutoff r : ℝ) ≤ 1 / (2 * r) := by
  have hy : (4 : ℝ) ≤ 1 / (2 * r) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hupper : (pairedEtaShiftBoundaryCutoff r : ℝ) ≤ 1 / (2 * r) :=
    Nat.floor_le (by positivity)
  have hfloor := Nat.lt_floor_add_one (1 / (2 * r))
  change 1 / (2 * r) < (pairedEtaShiftBoundaryCutoff r : ℝ) + 1 at hfloor
  have hprod := (div_lt_iff₀ (by positivity : 0 < 2 * r)).mp hfloor
  refine ⟨Nat.le_floor hy, ?_, hupper⟩
  apply (div_le_iff₀ (by positivity)).2
  nlinarith

/-- The chosen cutoff satisfies the exact logarithmic spacing hypothesis of
the arithmetic boundary expansion. -/
theorem pairedEtaShiftBoundaryCutoff_spacing {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    r ≤ Real.log (((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) /
      pairedEtaShiftBoundaryCutoff r) := by
  obtain ⟨hM, _, hupper⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hMpos : 0 < (pairedEtaShiftBoundaryCutoff r : ℝ) := by
    exact_mod_cast (show 0 < pairedEtaShiftBoundaryCutoff r by omega)
  have hprod := (le_div_iff₀ (by positivity : 0 < 2 * r)).mp hupper
  have hrinv : r ≤ 1 / ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hid : 1 / ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) =
      1 - (((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) /
        pairedEtaShiftBoundaryCutoff r)⁻¹ := by
    field_simp
    ring
  rw [hid] at hrinv
  exact hrinv.trans (Real.one_sub_inv_le_log_of_pos (by positivity))

/-- The harmonic boundary sum differs from `log (1/r)` by a bounded amount
at the displacement-dependent cutoff. -/
theorem pairedEtaShiftBoundary_harmonic_bounds {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    let S := ∑ n ∈ Finset.Icc 2 (pairedEtaShiftBoundaryCutoff r), (n : ℝ)⁻¹
    0 ≤ S ∧ S ≤ Real.log (1 / r) ∧ Real.log (1 / r) - 4 ≤ S := by
  dsimp only
  obtain ⟨hM, hlower, hupper⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hMpos : 0 < (pairedEtaShiftBoundaryCutoff r : ℝ) := by
    exact_mod_cast (show 0 < pairedEtaShiftBoundaryCutoff r by omega)
  have hSnonneg : 0 ≤ ∑ n ∈ Finset.Icc 2 (pairedEtaShiftBoundaryCutoff r), (n : ℝ)⁻¹ := by
    apply Finset.sum_nonneg
    intro n _
    positivity
  have hh := sum_Icc_two_inv_eq_harmonic_sub_one (show 1 ≤ pairedEtaShiftBoundaryCutoff r by omega)
  have hhupper := harmonic_le_one_add_log (pairedEtaShiftBoundaryCutoff r)
  have hhlower := log_add_one_le_harmonic (pairedEtaShiftBoundaryCutoff r)
  have hlogupper : Real.log (pairedEtaShiftBoundaryCutoff r : ℝ) ≤ Real.log (1 / r) := by
    apply Real.log_le_log hMpos
    exact hupper.trans (div_le_div_of_nonneg_left (by norm_num) hr (by linarith))
  have hloglower : Real.log (1 / r) - Real.log 4 ≤
      Real.log (pairedEtaShiftBoundaryCutoff r : ℝ) := by
    calc
      Real.log (1 / r) - Real.log 4 = Real.log (1 / (4 * r)) := by
        rw [Real.log_div (by norm_num) (ne_of_gt hr),
          Real.log_div (by norm_num) (by positivity),
          Real.log_mul (by norm_num) (ne_of_gt hr), Real.log_one]
        ring
      _ ≤ _ := Real.log_le_log (by positivity) hlower
  have hlognext : Real.log (pairedEtaShiftBoundaryCutoff r : ℝ) ≤
      Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) :=
    Real.log_le_log hMpos (by linarith)
  have hlogfour := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  simp only [Nat.cast_add, Nat.cast_one] at hhlower
  exact ⟨hSnonneg, by linarith, by linarith⟩

/-- At the critical tilt, the exact resolved boundary mass is a harmonic
sum with coefficient `exp r - 1`. -/
theorem pairedEtaMismatch_half_eq_harmonic_add_tail {M : ℕ} {r : ℝ}
    (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    pairedEtaMismatch (1 / 2) r =
      (Real.exp r - 1) * (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) +
        pairedEtaMismatchTail (1 / 2) r M := by
  convert pairedEtaMismatch_eq_boundaryMass_add_tail
    (sigma := 1 / 2) (by norm_num) hM hrpos hr using 1
  norm_num [Real.rpow_neg_one]

/-- Explicit critical displacement law for the actual eta support. The
error bound is uniform throughout the stated positive small-time interval. -/
theorem pairedEtaMismatch_critical_error_le {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    |pairedEtaMismatch (1 / 2) r - r * Real.log (1 / r)| ≤ 5 * r := by
  let M := pairedEtaShiftBoundaryCutoff r
  let S : ℝ := ∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹
  let L := Real.log (1 / r)
  obtain ⟨hM, hlower, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by dsimp [M]; omega)
  have hspacing := pairedEtaShiftBoundaryCutoff_spacing hr hrsmall
  have heq := pairedEtaMismatch_half_eq_harmonic_add_tail (show 2 ≤ M by dsimp [M]; omega)
    hr hspacing
  change pairedEtaMismatch (1 / 2) r =
    (Real.exp r - 1) * S + pairedEtaMismatchTail (1 / 2) r M at heq
  obtain ⟨hSnonneg, hSupper, hSlower⟩ := pairedEtaShiftBoundary_harmonic_bounds hr hrsmall
  change 0 ≤ S at hSnonneg
  change S ≤ L at hSupper
  change L - 4 ≤ S at hSlower
  have htailnonneg := pairedEtaMismatchTail_nonneg (1 / 2) r M
  have htail := pairedEtaMismatchTail_le (sigma := 1 / 2) (by norm_num) r
    (M := M) (by exact_mod_cast hMpos)
  norm_num [Real.rpow_neg_one] at htail
  have hMinv : 1 / (M : ℝ) ≤ 4 * r := by
    apply (div_le_iff₀ hMpos).2
    have h := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hlower
    simpa only [M, mul_comm] using h
  have htailupper : pairedEtaMismatchTail (1 / 2) r M ≤ 4 * r :=
    htail.trans (by simpa only [one_div] using hMinv)
  have hexp := Real.abs_exp_sub_one_sub_id_le
    (show |r| ≤ 1 by rw [abs_of_pos hr]; linarith)
  have heupper : Real.exp r - 1 ≤ r + r ^ 2 := by
    have := (le_abs_self (Real.exp r - 1 - r)).trans hexp
    linarith
  have helower : r ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / r by positivity)
  have hrL : r * L ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog hr.le
    have hid : r * (1 / r - 1) = 1 - r := by field_simp
    rw [hid] at h
    dsimp [L]
    linarith
  have hr2L : r ^ 2 * L ≤ r := by
    have := mul_le_mul_of_nonneg_left hrL hr.le
    nlinarith
  have hmainupper : (Real.exp r - 1) * S ≤ (r + r ^ 2) * L :=
    mul_le_mul heupper hSupper hSnonneg (by positivity)
  have hmainlower : r * (L - 4) ≤ (Real.exp r - 1) * S :=
    (mul_le_mul_of_nonneg_left hSlower hr.le).trans
      (mul_le_mul_of_nonneg_right helower hSnonneg)
  change |pairedEtaMismatch (1 / 2) r - r * L| ≤ 5 * r
  rw [heq]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The real displacement kernel is genuinely integrable on every right
half-line at positive horizontal tilt. -/
theorem integrableOn_pairedEtaMismatchKernel {sigma : ℝ} (hsigma : 0 < sigma)
    (r a : ℝ) :
    IntegrableOn (fun t ↦ pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t))
      (Ioi a) := by
  apply (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) a).bdd_mul
    (measurable_pairedEtaLogShiftMismatch_time r).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg r t)]
    exact pairedEtaLogShiftMismatch_le_one r t

/-- The real arithmetic displacement is measurable as a function of its
displacement parameter. -/
theorem measurable_pairedEtaMismatch (sigma : ℝ) : Measurable (pairedEtaMismatch sigma) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      pairedEtaLogShiftMismatch p.1 p.2 * Real.exp (-(2 * sigma) * p.2)) :=
    measurable_pairedEtaLogShiftMismatch.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- A global displacement bound by the entire positive-half-line exponential
mass, independent of the shift. -/
theorem pairedEtaMismatch_le_inv {sigma : ℝ} (hsigma : 0 < sigma) (r : ℝ) :
    pairedEtaMismatch sigma r ≤ 1 / (2 * sigma) := by
  calc
    pairedEtaMismatch sigma r ≤ ∫ t in Ioi 0, Real.exp (-(2 * sigma) * t) := by
      apply integral_mono_ae (integrableOn_pairedEtaMismatchKernel hsigma r 0)
        (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) 0)
      exact Eventually.of_forall fun t ↦
        mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t)
    _ = 1 / (2 * sigma) := by
      rw [integral_exp_mul_Ioi (by linarith)]
      simp

/-- A global polynomial majorant for the critical displacement error. This
keeps the small-displacement estimate usable under Gaussian integration. -/
theorem pairedEtaMismatch_critical_error_global {r : ℝ} (hr : 0 < r) :
    |pairedEtaMismatch (1 / 2) r - r * Real.log (1 / r)| ≤ 16 * r + r ^ 2 := by
  by_cases hrsmall : r ≤ 1 / 8
  · exact (pairedEtaMismatch_critical_error_le hr hrsmall).trans (by nlinarith [sq_nonneg r])
  have hDnonneg := pairedEtaMismatch_nonneg (1 / 2) r
  have hDle : pairedEtaMismatch (1 / 2) r ≤ 1 := by
    simpa using pairedEtaMismatch_le_inv (sigma := 1 / 2) (by norm_num) r
  have hlogupper := Real.log_le_sub_one_of_pos hr
  have hloglower := Real.log_le_log (show (0 : ℝ) < 1 / 8 by norm_num)
    (show (1 : ℝ) / 8 ≤ r by linarith)
  simp only [one_div, Real.log_inv] at hloglower
  have hlogeight := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  have habslog : |Real.log r| ≤ 7 + r := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    |pairedEtaMismatch (1 / 2) r - r * Real.log (1 / r)| ≤
        |pairedEtaMismatch (1 / 2) r| + |r * Real.log (1 / r)| := abs_sub _ _
    _ = pairedEtaMismatch (1 / 2) r + r * |Real.log r| := by
      rw [abs_of_nonneg hDnonneg, abs_mul, abs_of_pos hr]
      simp only [one_div, Real.log_inv, abs_neg]
    _ ≤ 1 + r * (7 + r) :=
      add_le_add hDle (mul_le_mul_of_nonneg_left habslog hr.le)
    _ ≤ 16 * r + r ^ 2 := by nlinarith

end

end RiemannGaussian
