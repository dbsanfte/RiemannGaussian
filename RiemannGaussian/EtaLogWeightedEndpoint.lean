import RiemannGaussian.EtaLogBoundaryFinitePart
import RiemannGaussian.EtaLogWeightedTail

/-!
# Quantitative endpoint decomposition of the actual weighted eta mismatch

The actual complex displacement retains its finite harmonic endpoint and
its evaluated Wallis tail. Their combined error decays with the test's
logarithmic scale and the real arithmetic displacement.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Freezing the resolved crossing strips retains the actual complex tail
as an exact source term instead of bounding that tail away. -/
theorem pairedEtaWeightedMismatch_boundary_remainder_le {M : ℕ} {r R : ℝ}
    (hM : 2 ≤ M) (hr : 0 < r) (hR : 0 < R)
    (hspacing : r ≤ Real.log (((M : ℝ) + 1) / M))
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖pairedEtaWeightedMismatch r R F -
      (Real.exp r - 1) • (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      pairedEtaWeightedMismatchTail r R F M‖ ≤
      ((K : ℝ) * r / R) * (Real.exp r - 1) * (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) := by
  have heq : pairedEtaWeightedMismatch r R F -
      (Real.exp r - 1) • (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      pairedEtaWeightedMismatchTail r R F M =
      ∑ n ∈ Finset.Icc 2 M, ((∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)) -
        (Real.exp r - 1) • ((n : ℝ)⁻¹ • F (Real.log n / R))) := by
    rw [pairedEtaWeightedMismatch_eq_boundary_add_tail hM hr hspacing hF.continuous.measurable hB R,
      Finset.sum_sub_distrib, ← Finset.smul_sum]
    unfold pairedEtaWeightedMismatchTail
    abel
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 M,
        ‖(∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-t) • F (t / R)) -
          (Real.exp r - 1) • ((n : ℝ)⁻¹ • F (Real.log n / R))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 M, ((K : ℝ) * r / R) * ((Real.exp r - 1) * (n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [smul_smul]
      exact pairedEtaWeightedMismatch_strip_error_le hr.le hR hF
        (by have := (Finset.mem_Icc.mp hn).1; omega)
    _ = _ := by simp only [← mul_assoc, ← Finset.mul_sum]

/-- After arithmetic normalization the crossing-strip remainder is at
most `K/R`, uniformly at the actual displacement cutoff. -/
theorem pairedEtaWeightedMismatch_cutoff_boundary_remainder_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F -
      (∑ n ∈ Finset.Icc 2 (pairedEtaShiftBoundaryCutoff r), (n : ℝ)⁻¹ • F (Real.log n / R)) -
      (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F (pairedEtaShiftBoundaryCutoff r)‖ ≤
      (K : ℝ) / R := by
  let M := pairedEtaShiftBoundaryCutoff r
  let S : ℂ := ∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr)
  obtain ⟨hM, _, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hrem := pairedEtaWeightedMismatch_boundary_remainder_le (by dsimp [M]; omega : 2 ≤ M)
    hr hR (pairedEtaShiftBoundaryCutoff_spacing hr hrsmall) hF hB
  have hSbound := (pairedEtaShiftBoundary_harmonic_bounds hr hrsmall).2.1
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / r by positivity)
  have hrlog : r * Real.log (1 / r) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hlog hr.le
    have hid : r * (1 / r - 1) = 1 - r := by field_simp
    rw [hid] at hm
    linarith
  have hrS : r * (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hSbound hr.le).trans hrlog
  change ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - S -
    (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M‖ ≤ _
  have hid : (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - S -
      (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M =
      (Real.exp r - 1)⁻¹ • (pairedEtaWeightedMismatch r R F - (Real.exp r - 1) • S -
        pairedEtaWeightedMismatchTail r R F M) := by
    rw [smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ he.ne', one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
  calc
    _ ≤ (Real.exp r - 1)⁻¹ * (((K : ℝ) * r / R) * (Real.exp r - 1) *
        (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr he.le)
    _ = ((K : ℝ) / R) * (r * (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹)) := by field_simp
    _ ≤ (K : ℝ) / R := by
      simpa using mul_le_mul_of_nonneg_left hrS (div_nonneg K.coe_nonneg hR.le)

/-- A uniform complex finite-part decomposition on the actual eta support.
The lower harmonic endpoint and the upper Wallis endpoint remain separate;
the remainder is at most `8K/R + 32(exp(r)-1)B`. -/
theorem pairedEtaWeightedMismatch_cutoff_endpoint_error_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F -
      (∫ t in 0..Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1), F (t / R)) -
      ((harmonic (pairedEtaShiftBoundaryCutoff r) : ℝ) - 1 -
        Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1)) • F 0 -
      (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r)) •
        F (Real.log (pairedEtaShiftBoundaryCutoff r : ℝ) / R)‖ ≤
      8 * (K : ℝ) / R + 32 * (Real.exp r - 1) * B := by
  let M := pairedEtaShiftBoundaryCutoff r
  let S : ℂ := ∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)
  let T : ℂ := (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatchTail r R F M
  let I : ℂ := ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)
  let A : ℂ := ((harmonic M : ℝ) - 1 - Real.log ((M : ℝ) + 1)) • F 0
  let C : ℂ := (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * M)) • F (Real.log (M : ℝ) / R)
  have hM : 1 ≤ M := by
    have := (pairedEtaShiftBoundaryCutoff_bounds hr hrsmall).1
    dsimp [M]
    omega
  have hboundary := pairedEtaWeightedMismatch_cutoff_boundary_remainder_le hr hrsmall hR hF hB
  have hquad := logBoundary_crossing_finite_part_error_le hM hR hF
  have htail := pairedEtaWeightedMismatchTail_cutoff_error_le hr hrsmall hR hF hB
  change ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - I - A - C‖ ≤ _
  rw [show (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - I - A - C =
    (((Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - S - T) + (S - I - A)) + (T - C) by abel]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  calc
    _ ≤ ((K : ℝ) / R + 3 * (K : ℝ) / R) +
        (4 * (K : ℝ) / R + 32 * (Real.exp r - 1) * B) :=
      add_le_add (add_le_add hboundary hquad) htail
    _ = _ := by ring

end

end RiemannGaussian
