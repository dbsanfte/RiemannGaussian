import RiemannGaussian.EtaLogBoundaryQuadrature

/-!
# The actual eta boundary measure tested against slow complex weights

Bounded Lipschitz tests retain phase and other logarithmically varying
weights in the critical boundary law. The exact arithmetic tail remains a
complex integral. No model support replaces the alternating eta intervals.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The critical actual-support displacement tested on logarithmic time
scale `R`, without discarding the complex test. -/
def pairedEtaWeightedMismatch (r R : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∫ t in Ioi 0, (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)

/-- A bounded measurable test preserves the integrability of the critical
exponential weight on every right half-line. -/
theorem integrableOn_etaSlowTest {F : ℝ → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (R a : ℝ) :
    IntegrableOn (fun t ↦ Real.exp (-t) • F (t / R)) (Ioi a) := by
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi a) := by
    simpa only [neg_one_mul] using
      integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) a
  apply (he.const_mul B).mono'
    ((Real.continuous_exp.comp continuous_neg).measurable.smul
      (hF.comp (measurable_id.div_const R))).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    change ‖Real.exp (-t) • F (t / R)‖ ≤ B * Real.exp (-t)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hB _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

/-- Genuine integrability of the full complex weighted mismatch. -/
theorem integrableOn_pairedEtaWeightedMismatchKernel {F : ℝ → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (r R a : ℝ) :
    IntegrableOn (fun t ↦ (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R))
      (Ioi a) := by
  have h := integrableOn_pairedEtaLogShiftMismatch_mul (integrableOn_etaSlowTest hF hB R a) r
  simpa only [Complex.real_smul, Complex.ofReal_mul, mul_assoc] using h

/-- Exact finite crossing expansion of the complex weighted mismatch,
with its actual omitted tail retained. -/
theorem pairedEtaWeightedMismatch_eq_boundary_add_tail {M : ℕ} {r : ℝ}
    (hM : 2 ≤ M) (hr : 0 < r) (hspacing : r ≤ Real.log (((M : ℝ) + 1) / M))
    {F : ℝ → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (R : ℝ) :
    pairedEtaWeightedMismatch r R F =
      (∑ n ∈ Finset.Icc 2 M,
        ∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)) +
      ∫ t in Ioi (Real.log (M : ℝ)),
        (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R) := by
  have h := pairedEtaLogShiftMismatch_integral_eq_boundary_add_tail hM hr hspacing
    (integrableOn_etaSlowTest hF hB R 0)
  simpa only [pairedEtaWeightedMismatch, Complex.real_smul, Complex.ofReal_mul, mul_assoc] using h

/-- The actual omitted complex tail is bounded by the test bound times
the reciprocal arithmetic cutoff. -/
theorem norm_pairedEtaWeightedMismatch_tail_le {M : ℕ} (hM : 0 < M)
    {F : ℝ → ℂ} {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (r R : ℝ) :
    ‖∫ t in Ioi (Real.log (M : ℝ)),
      (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)‖ ≤ B / M := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi (Real.log (M : ℝ))) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ))
      (by norm_num) (Real.log (M : ℝ))
  calc
    _ ≤ ∫ t in Ioi (Real.log (M : ℝ)), B * Real.exp (-t) := by
      apply norm_integral_le_of_norm_le (he.const_mul B)
      exact Eventually.of_forall fun t ↦ by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le)]
        calc
          _ ≤ (pairedEtaLogShiftMismatch r t * Real.exp (-t)) * B :=
            mul_le_mul_of_nonneg_left (hB _)
              (mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le)
          _ ≤ Real.exp (-t) * B := mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t)) hB0
          _ = _ := mul_comm _ _
    _ = B / M := by
      rw [integral_const_mul]
      have hi := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) (Real.log (M : ℝ))
      simp only [neg_one_mul, div_neg, div_one, neg_neg] at hi
      rw [hi, Real.exp_neg, Real.exp_log (by exact_mod_cast hM)]
      rfl

/-- Freezing a slow Lipschitz test on an actual crossing strip has an
explicit error relative to that strip's exact critical mass. -/
theorem pairedEtaWeightedMismatch_strip_error_le {r R : ℝ} (hr : 0 ≤ r) (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {n : ℕ} (hn : 0 < n) :
    ‖(∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)) -
      ((Real.exp r - 1) * (n : ℝ)⁻¹) • F (Real.log n / R)‖ ≤
      ((K : ℝ) * r / R) * ((Real.exp r - 1) * (n : ℝ)⁻¹) := by
  have hmass : (∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t)) =
      (Real.exp r - 1) * (n : ℝ)⁻¹ := by
    simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul,
      one_mul, div_one, Real.rpow_neg_one] using
      integral_exp_pairedEtaLogCrossingStrip (sigma := 1 / 2) (by norm_num) hr hn
  have hi : IntegrableOn (fun t ↦ Real.exp (-t) • F (t / R)) (pairedEtaLogCrossingStrip r n) := by
    exact (((Real.continuous_exp.comp continuous_neg).smul
      (hF.continuous.comp (continuous_id.div_const R))).intervalIntegrable _ _).1
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (pairedEtaLogCrossingStrip r n) :=
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _).1
  rw [← hmass, ← integral_smul_const, ← integral_sub hi (he.smul_const _)]
  calc
    _ ≤ ∫ t in pairedEtaLogCrossingStrip r n, ((K : ℝ) * r / R) * Real.exp (-t) := by
      apply norm_integral_le_of_norm_le (he.const_mul _)
      filter_upwards [ae_restrict_mem (show MeasurableSet (pairedEtaLogCrossingStrip r n)
        from measurableSet_Ioc)] with t ht
      have hd : |t / R - Real.log (n : ℝ) / R| ≤ r / R := by
        rw [← sub_div, abs_div, abs_of_pos hR,
          abs_of_nonpos (sub_nonpos.mpr ht.2)]
        exact div_le_div_of_nonneg_right (by linarith [ht.1]) hR.le
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-t) * ((K : ℝ) * |t / R - Real.log (n : ℝ) / R|) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          simpa only [dist_eq_norm, Real.norm_eq_abs] using
            hF.dist_le_mul (t / R) (Real.log n / R)
        _ ≤ Real.exp (-t) * ((K : ℝ) * (r / R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd K.coe_nonneg) (Real.exp_pos _).le
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul, hmass]

/-- A quantitative comparison of the actual weighted displacement with
its finite complex harmonic boundary sum. -/
theorem pairedEtaWeightedMismatch_frozen_boundary_error_le {M : ℕ} {r R : ℝ}
    (hM : 2 ≤ M) (hr : 0 < r) (hR : 0 < R)
    (hspacing : r ≤ Real.log (((M : ℝ) + 1) / M))
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖pairedEtaWeightedMismatch r R F -
      (Real.exp r - 1) • (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R))‖ ≤
      B / M + ((K : ℝ) * r / R) * (Real.exp r - 1) *
        (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) := by
  let A : ℂ := ∑ n ∈ Finset.Icc 2 M,
    ∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)
  let Z : ℂ := (Real.exp r - 1) •
    (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R))
  have hAZ : ‖A - Z‖ ≤ ((K : ℝ) * r / R) * (Real.exp r - 1) *
      (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) := by
    dsimp only [A, Z]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 2 M,
          ‖(∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)) -
            (Real.exp r - 1) • ((n : ℝ)⁻¹ • F (Real.log n / R))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 M,
          ((K : ℝ) * r / R) * ((Real.exp r - 1) * (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [smul_smul]
        exact pairedEtaWeightedMismatch_strip_error_le hr.le hR hF
          (by have := (Finset.mem_Icc.mp hn).1; omega)
      _ = _ := by simp only [← mul_assoc, ← Finset.mul_sum]
  have heq := pairedEtaWeightedMismatch_eq_boundary_add_tail hM hr hspacing
    hF.continuous.measurable hB R
  change pairedEtaWeightedMismatch r R F = A + _ at heq
  have htail := norm_pairedEtaWeightedMismatch_tail_le (M := M) (by omega) hB r R
  change ‖pairedEtaWeightedMismatch r R F - Z‖ ≤ _
  rw [heq, show A + (∫ t in Ioi (Real.log (M : ℝ)),
      (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)) - Z =
      (A - Z) + (∫ t in Ioi (Real.log (M : ℝ)),
        (pairedEtaLogShiftMismatch r t * Real.exp (-t)) • F (t / R)) by abel]
  exact (norm_add_le _ _).trans ((add_le_add hAZ htail).trans (by ring_nf; rfl))

/-- The weighted arithmetic displacement is approximated by a continuous
logarithmic integral, with every cutoff and rescaling parameter explicit. -/
theorem pairedEtaWeightedMismatch_cutoff_quadrature_error_le {M : ℕ} {r R : ℝ}
    (hM : 2 ≤ M) (hr : 0 < r) (hR : 0 < R)
    (hspacing : r ≤ Real.log (((M : ℝ) + 1) / M))
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖pairedEtaWeightedMismatch r R F -
      (Real.exp r - 1) • (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R))‖ ≤
      B / M + (Real.exp r - 1) *
        (2 * B + (K : ℝ) / R * Real.log ((M : ℝ) + 1) +
          (K : ℝ) * r / R * (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹)) := by
  let S : ℂ := ∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)
  let I : ℂ := ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)
  have ha : 0 ≤ Real.exp r - 1 := sub_nonneg.mpr (Real.one_le_exp hr.le)
  have hquad : ‖(Real.exp r - 1) • S - (Real.exp r - 1) • I‖ ≤
      (Real.exp r - 1) * (2 * B + (K : ℝ) / R * Real.log ((M : ℝ) + 1)) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left
      (logBoundary_crossing_quadrature_error_le (by omega) hR hF hB) ha
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((Real.exp r - 1) • S) _).trans
    ((add_le_add (pairedEtaWeightedMismatch_frozen_boundary_error_le hM hr hR hspacing hF hB)
      hquad).trans (by ring_nf; rfl))

/-- A phase-preserving quantitative critical boundary law for every bounded
Lipschitz complex test. The time scale `R` is independent of the displacement.
At `R = log (1/r)` the error is at most `(12 B + 4 K) r`. -/
theorem pairedEtaWeightedMismatch_critical_error_le {r R : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖pairedEtaWeightedMismatch r R F -
      r • (∫ t in 0..Real.log (1 / r), F (t / R))‖ ≤
      r * (12 * B + 4 * (K : ℝ) / R * Real.log (1 / r)) := by
  let M := pairedEtaShiftBoundaryCutoff r
  let L := Real.log (1 / r)
  let Q := Real.log ((M : ℝ) + 1)
  let S : ℝ := ∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹
  let a := Real.exp r - 1
  let I : ℂ := ∫ t in 0..Q, F (t / R)
  let J : ℂ := ∫ t in 0..L, F (t / R)
  let k : ℝ := (K : ℝ) / R
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  obtain ⟨hM, hlower, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by dsimp [M]; omega)
  have hQ0 : 0 ≤ Q := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  obtain ⟨hQL, hQL'⟩ := pairedEtaShiftBoundaryCutoff_log_bounds hr hrsmall
  change L - 3 ≤ Q at hQL
  change Q ≤ L at hQL'
  have hL0 : 0 ≤ L := hQ0.trans hQL'
  obtain ⟨hS0, hSL, _⟩ := pairedEtaShiftBoundary_harmonic_bounds hr hrsmall
  change 0 ≤ S at hS0
  change S ≤ L at hSL
  have hr1 : r ≤ 1 := by linarith
  have ha0 : 0 ≤ a := sub_nonneg.mpr (Real.one_le_exp hr.le)
  have hTaylor : |a - r| ≤ r ^ 2 := Real.abs_exp_sub_one_sub_id_le
    (by rw [abs_of_pos hr]; exact hr1)
  have ha : a ≤ 2 * r := by
    have ht := (le_abs_self (a - r)).trans hTaylor
    nlinarith
  have hrL : r * L ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < 1 / r by positivity)) hr.le
    have hid : r * (1 / r - 1) = 1 - r := by field_simp
    rw [hid] at h
    change r * L ≤ _ at h
    linarith
  have htail : B / (M : ℝ) ≤ 4 * B * r := by
    have hMinv : 1 / (M : ℝ) ≤ 4 * r := by
      apply (div_le_iff₀ hM0).2
      have h := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hlower
      change 1 ≤ (M : ℝ) * (4 * r) at h
      nlinarith
    calc
      B / (M : ℝ) = B * (1 / M) := by ring
      _ ≤ B * (4 * r) := mul_le_mul_of_nonneg_left hMinv hB0
      _ = _ := by ring
  have hmain : ‖pairedEtaWeightedMismatch r R F - a • I‖ ≤
      8 * B * r + 4 * k * r * L := by
    have h := pairedEtaWeightedMismatch_cutoff_quadrature_error_le
      (M := M) (by dsimp [M]; omega) hr hR
      (pairedEtaShiftBoundaryCutoff_spacing hr hrsmall) hF hB
    change ‖pairedEtaWeightedMismatch r R F - a • I‖ ≤
      B / M + a * (2 * B + k * Q + (K : ℝ) * r / R * S) at h
    have hparts : 2 * B + k * Q + (K : ℝ) * r / R * S ≤ 2 * B + 2 * k * L := by
      have hq := mul_le_mul_of_nonneg_left hQL' hk
      have hrs : r * S ≤ L :=
        (mul_le_of_le_one_left hS0 hr1).trans hSL
      have hs := mul_le_mul_of_nonneg_left hrs hk
      have hid : (K : ℝ) * r / R * S = k * (r * S) := by dsimp [k]; ring
      rw [hid]
      linarith
    calc
      _ ≤ B / M + a * (2 * B + k * Q + (K : ℝ) * r / R * S) := h
      _ ≤ 4 * B * r + (2 * r) * (2 * B + 2 * k * L) := by
        exact add_le_add htail ((mul_le_mul_of_nonneg_left hparts ha0).trans
          (mul_le_mul_of_nonneg_right ha (by positivity)))
      _ = _ := by ring
  have hI : ‖I‖ ≤ B * Q := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := Q) (f := fun t ↦ F (t / R)) (fun t _ ↦ hB (t / R))
    simpa only [sub_zero, abs_of_nonneg hQ0] using h
  have hcoeff : ‖a • I - r • I‖ ≤ B * r := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hrQ : r ^ 2 * Q ≤ r := by
      have hq := mul_le_mul_of_nonneg_left hQL' hr.le
      have h := mul_le_mul_of_nonneg_left (hq.trans hrL) hr.le
      nlinarith
    calc
      _ ≤ r ^ 2 * (B * Q) := mul_le_mul hTaylor hI (norm_nonneg _) (sq_nonneg r)
      _ = B * (r ^ 2 * Q) := by ring
      _ ≤ B * r := mul_le_mul_of_nonneg_left hrQ hB0
  have hIJ : ‖I - J‖ ≤ 3 * B := by
    have hc : Continuous (fun t : ℝ ↦ F (t / R)) :=
      hF.continuous.comp (continuous_id.div_const R)
    dsimp only [I, J]
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := L) (b := Q) (f := fun t ↦ F (t / R)) (fun t _ ↦ hB (t / R))
    rw [abs_of_nonpos (sub_nonpos.mpr hQL')] at h
    exact h.trans (by nlinarith)
  have hend : ‖r • I - r • J‖ ≤ 3 * B * r := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hIJ hr.le).trans_eq (by ring)
  change ‖pairedEtaWeightedMismatch r R F - r • J‖ ≤ _
  calc
    _ ≤ (‖pairedEtaWeightedMismatch r R F - a • I‖ + ‖a • I - r • I‖) +
        ‖r • I - r • J‖ :=
      (norm_sub_le_norm_sub_add_norm_sub _ (r • I) _).trans
        (add_le_add (norm_sub_le_norm_sub_add_norm_sub _ (a • I) _) le_rfl)
    _ ≤ (8 * B * r + 4 * k * r * L + B * r) + 3 * B * r :=
      add_le_add (add_le_add hmain hcoeff) hend
    _ = _ := by dsimp [k, L]; ring

end

end RiemannGaussian
