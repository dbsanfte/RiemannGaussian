import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaResidual
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# A logarithmic bound for the zero-free local eta residual

The selected local eta residual is analytic and zero-free on a disk of radius
strictly larger than `17 / 16`.  This module constructs its normalized
analytic logarithm directly from the logarithmic derivative and proves the
exponential recovery identity.

The residual's linear disk upper bound and uniform positive value at the
origin give a real-part bound of size
`log (staticContourLocalEtaJensenConstant * (T + 4))`.  A checked
Borel--Carathéodory argument then controls the full logarithm.  In particular,
its value at the translated critical endpoint `-1` is at most thirty-two
times that logarithmic majorant.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The constant comparing the local eta disk upper bound with its safe-center
lower floor is at least one. -/
lemma one_le_staticContourLocalEtaJensenConstant :
    1 ≤ staticContourLocalEtaJensenConstant := by
  have hfloorLeOne : staticContourSafeEtaFactorFloor ≤ 1 := by
    unfold staticContourSafeEtaFactorFloor
    have hpow : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hmassProduct :
      1 ≤ staticContourLocalEtaMass * staticContourSafeZetaDirichletMass :=
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ staticContourLocalEtaMass * staticContourSafeZetaDirichletMass :=
        mul_le_mul one_le_staticContourLocalEtaMass
          one_le_staticContourSafeZetaDirichletMass (by norm_num)
          (zero_le_one.trans one_le_staticContourLocalEtaMass)
  unfold staticContourLocalEtaJensenConstant
  rw [le_div_iff₀ staticContourSafeEtaFactorFloor_pos]
  simpa using hfloorLeOne.trans hmassProduct

/-- The residual-to-center ratio is exactly the Jensen constant times the
shifted height. -/
lemma staticContourLocalEta_upper_div_centerFloor_eq (T : ℝ) :
    staticContourLocalEtaMass * (T + 4) /
        (staticContourSafeEtaFactorFloor /
          staticContourSafeZetaDirichletMass) =
      staticContourLocalEtaJensenConstant * (T + 4) := by
  unfold staticContourLocalEtaJensenConstant
  field_simp [staticContourSafeEtaFactorFloor_pos.ne',
    (one_pos.trans_le one_le_staticContourSafeZetaDirichletMass).ne']

/-- The logarithmic majorant used for the `n`th local eta residual. -/
def staticContourLocalEtaCanonicalLogMajorant (n : ℕ) : ℝ :=
  Real.log
    (staticContourLocalEtaJensenConstant *
      (quantitativeSpectralBoundaryTruncation n + 4))

lemma staticContourLocalEtaCanonicalLogMajorant_pos (n : ℕ) :
    0 < staticContourLocalEtaCanonicalLogMajorant n := by
  apply Real.log_pos
  have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
    (Nat.cast_nonneg n).trans_lt
      (quantitativeSpectralBoundaryTruncation_spec n).1
  calc
    (1 : ℝ) < quantitativeSpectralBoundaryTruncation n + 4 := by linarith
    _ = 1 * (quantitativeSpectralBoundaryTruncation n + 4) := by ring
    _ ≤ staticContourLocalEtaJensenConstant *
        (quantitativeSpectralBoundaryTruncation n + 4) :=
      mul_le_mul_of_nonneg_right one_le_staticContourLocalEtaJensenConstant
        (by linarith)

/-! ## The normalized analytic logarithm -/

/-- The zero-free local eta residual has a logarithmic derivative primitive
on its selected disk, normalized to vanish at the origin. -/
theorem exists_staticContourLocalEtaCanonicalLog (n : ℕ) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      ∀ z ∈ ball 0 (staticContourLocalEtaCanonicalRadius n),
        HasDerivAt L
          (logDeriv (staticContourLocalEtaCanonicalResidual n) z) z := by
  let R := staticContourLocalEtaCanonicalRadius n
  let g := staticContourLocalEtaCanonicalResidual n
  have hdiff : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have hg := (staticContourLocalEtaCanonicalResidual_decomp n).analyticOnNhd z
      (ball_subset_closedBall (by simpa [R] using hz))
    have hlog : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((staticContourLocalEtaCanonicalResidual_decomp n).ne_zero z
          (ball_subset_closedBall (by simpa [R, g] using hz)))
    exact hlog.differentiableAt.differentiableWithinAt
  simpa [R, g] using hdiff.isExactOn_ball.with_val_at 0 0

/-- A fixed normalized analytic logarithm of the local eta residual. -/
noncomputable def staticContourLocalEtaCanonicalLog (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_staticContourLocalEtaCanonicalLog n)

@[simp] theorem staticContourLocalEtaCanonicalLog_zero (n : ℕ) :
    staticContourLocalEtaCanonicalLog n 0 = 0 :=
  (Classical.choose_spec (exists_staticContourLocalEtaCanonicalLog n)).1

theorem staticContourLocalEtaCanonicalLog_hasDerivAt
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (staticContourLocalEtaCanonicalRadius n)) :
    HasDerivAt (staticContourLocalEtaCanonicalLog n)
      (logDeriv (staticContourLocalEtaCanonicalResidual n) z) z :=
  (Classical.choose_spec (exists_staticContourLocalEtaCanonicalLog n)).2 z hz

/-- Exponentiating the normalized primitive recovers the local eta residual,
with its value at the origin as the normalizing constant. -/
theorem exp_staticContourLocalEtaCanonicalLog_mul_zero_eq
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (staticContourLocalEtaCanonicalRadius n)) :
    Complex.exp (staticContourLocalEtaCanonicalLog n z) *
        staticContourLocalEtaCanonicalResidual n 0 =
      staticContourLocalEtaCanonicalResidual n z := by
  let R := staticContourLocalEtaCanonicalRadius n
  let g := staticContourLocalEtaCanonicalResidual n
  let L := staticContourLocalEtaCanonicalLog n
  let q : ℂ → ℂ := (fun w => Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := by
    exact mem_ball_self (by
      simpa [R] using staticContourLocalEtaCanonicalRadius_pos n)
  have hqdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := staticContourLocalEtaCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)
    have hg := (staticContourLocalEtaCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    exact (by
      simpa [q, L, g] using
        (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt
          |>.differentiableWithinAt)
  have hqderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := staticContourLocalEtaCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)
    have hg := (staticContourLocalEtaCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    have hqHas : HasDerivAt q
        (Complex.exp (-L w) *
            (-logDeriv g w) * g w +
          Complex.exp (-L w) * deriv g w) w := by
      simpa [q, L, g] using hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hqHas.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply]
    have hgne : g w ≠ 0 :=
      (staticContourLocalEtaCanonicalResidual_decomp n).ne_zero w
        (ball_subset_closedBall (by simpa [R, g] using hw))
    rw [mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ hgne]
    ring
  have hqeq : q 0 = q z :=
    isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
      hqdiff hqderiv hzero (by simpa [R] using hz)
  have hg0eq : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, staticContourLocalEtaCanonicalLog_zero] using hqeq
  change Complex.exp (L z) * g 0 = g z
  rw [hg0eq, ← mul_assoc, ← Complex.exp_add]
  simp

/-! ## Real-part and Borel--Carathéodory bounds -/

/-- The disk upper bound divided by the safe-center lower floor controls the
real part of the normalized residual logarithm. -/
theorem staticContourLocalEtaCanonicalLog_re_le
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (staticContourLocalEtaCanonicalRadius n)) :
    (staticContourLocalEtaCanonicalLog n z).re ≤
      staticContourLocalEtaCanonicalLogMajorant n := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let g := staticContourLocalEtaCanonicalResidual n
  let L := staticContourLocalEtaCanonicalLog n
  let c : ℝ := staticContourSafeEtaFactorFloor /
    staticContourSafeZetaDirichletMass
  have hcpos : 0 < c := by
    dsimp [c]
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hid := congrArg norm
    (exp_staticContourLocalEtaCanonicalLog_mul_zero_eq n hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : c ≤ ‖g 0‖ := by
    simpa [c, g] using
      staticContourSafeEtaFactorFloor_div_mass_le_norm_canonicalResidual_zero n
  have hgBound :
      ‖g z‖ ≤ staticContourLocalEtaMass * (T + 4) := by
    apply norm_staticContourLocalEtaCanonicalResidual_le n
    exact ball_subset_closedBall (by simpa [T, g] using hz)
  have hexpTimesFloor :
      Real.exp (L z).re * c ≤
        staticContourLocalEtaMass * (T + 4) := by
    calc
      Real.exp (L z).re * c ≤ Real.exp (L z).re * ‖g 0‖ :=
        mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
      _ = ‖g z‖ := hid
      _ ≤ staticContourLocalEtaMass * (T + 4) := hgBound
  have hargpos :
      0 < staticContourLocalEtaJensenConstant *
        (quantitativeSpectralBoundaryTruncation n + 4) := by
    have hT : 0 < T :=
      (Nat.cast_nonneg n).trans_lt
        (by simpa [T] using
          (quantitativeSpectralBoundaryTruncation_spec n).1)
    simpa [T] using
      (mul_pos staticContourLocalEtaJensenConstant_pos (by linarith : 0 < T + 4))
  apply Real.exp_le_exp.mp
  rw [staticContourLocalEtaCanonicalLogMajorant, Real.exp_log hargpos]
  calc
    Real.exp (L z).re ≤
        staticContourLocalEtaMass * (T + 4) / c :=
      (le_div_iff₀ hcpos).2 hexpTimesFloor
    _ = staticContourLocalEtaJensenConstant * (T + 4) := by
      simpa [c] using staticContourLocalEta_upper_div_centerFloor_eq T

/-- Borel--Carathéodory turns the one-sided real-part estimate into a norm
bound throughout the selected local eta disk. -/
theorem norm_staticContourLocalEtaCanonicalLog_le
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (staticContourLocalEtaCanonicalRadius n)) :
    ‖staticContourLocalEtaCanonicalLog n z‖ ≤
      2 * staticContourLocalEtaCanonicalLogMajorant n * ‖z‖ /
        (staticContourLocalEtaCanonicalRadius n - ‖z‖) := by
  let R := staticContourLocalEtaCanonicalRadius n
  let L := staticContourLocalEtaCanonicalLog n
  have hR : 0 < R := staticContourLocalEtaCanonicalRadius_pos n
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (staticContourLocalEtaCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero
    (M := staticContourLocalEtaCanonicalLogMajorant n)
    (staticContourLocalEtaCanonicalLogMajorant_pos n) hdiff
  · intro w hw
    exact staticContourLocalEtaCanonicalLog_re_le n
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact staticContourLocalEtaCanonicalLog_zero n

/-- At the translated critical endpoint `-1`, the normalized local residual
logarithm is bounded by an explicit logarithmic-height majorant. -/
theorem norm_staticContourLocalEtaCanonicalLog_neg_one_le (n : ℕ) :
    ‖staticContourLocalEtaCanonicalLog n (-1)‖ ≤
      32 * staticContourLocalEtaCanonicalLogMajorant n := by
  let R := staticContourLocalEtaCanonicalRadius n
  let M := staticContourLocalEtaCanonicalLogMajorant n
  have hR : 17 / 16 < R := by
    simpa [R] using (staticContourLocalEtaCanonicalRadius_spec n).1
  have hden : 0 < R - 1 := by linarith
  have hz : (-1 : ℂ) ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    simpa using one_lt_staticContourLocalEtaCanonicalRadius n
  have hraw := norm_staticContourLocalEtaCanonicalLog_le n hz
  have hM : 0 ≤ M := by
    simpa [M] using (staticContourLocalEtaCanonicalLogMajorant_pos n).le
  calc
    ‖staticContourLocalEtaCanonicalLog n (-1)‖ ≤
        2 * M * ‖(-1 : ℂ)‖ / (R - ‖(-1 : ℂ)‖) := by
      simpa [M, R] using hraw
    _ = 2 * M / (R - 1) := by norm_num
    _ ≤ 32 * M := by
      rw [div_le_iff₀ hden]
      have hgap : (1 / 16 : ℝ) ≤ R - 1 := by linarith
      have hscale := mul_le_mul_of_nonneg_left hgap
        (show 0 ≤ 32 * M by positivity)
      nlinarith

end

end RiemannGaussian
