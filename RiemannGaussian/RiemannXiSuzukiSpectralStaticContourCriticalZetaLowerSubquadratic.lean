import RiemannGaussian.FiniteToEntireBoundaryLowerBound
import RiemannGaussian.RiemannXiSuzukiWeilVertical
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper

/-!
# Subquadratic lower control at the critical zeta endpoints

The canonical xi factorization previously supplied a very coarse lower floor
on the selected zero-free contour endpoints. This module retains the proved
three-halves global growth of xi throughout the zero-count and
Borel--Carathéodory estimates. It obtains an explicit lower floor with
exponent of order `T^(3/2) log T` and proves that the negative logarithms of
both spectral xi and critical-line zeta are `o(T²)` along the quantitative
endpoint sequence.

This is strict, unconditional progress toward the static-contour frontier. It
does not prove the still-needed `o(T)` estimate; closing that remaining
half-power gap requires additional cancellation or rigidity beyond global
growth and zero separation.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexOrder Topology

namespace RiemannGaussian

noncomputable section

/-- The canonical xi residual inherits the three-halves exponential growth bound on its disk. -/
lemma norm_riemannXiCanonicalResidual_le_of_threeHalves_growth
    {A : ℝ} (_hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ ≤
      Real.exp
        (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (riemannXiCanonicalResidual_decomp n).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_riemannXiCanonicalResidual_eq_on_sphere n hw]
    have hxi := hbound w
    have hwnorm : ‖w‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hw
    simpa [R, hwnorm] using hxi
  · rwa [closure_ball 0 hR.ne']

/-- The real part of the normalized canonical logarithm is bounded by xi's
three-halves growth. -/
lemma riemannXiCanonicalLog_re_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    (riemannXiCanonicalLog n z).re ≤
      A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  have hid := congrArg norm (exp_riemannXiCanonicalLog_mul_zero_eq n hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hgBound : ‖g z‖ ≤
      Real.exp (A * (R + 1) ^ (3 / 2 : ℝ)) := by
    apply norm_riemannXiCanonicalResidual_le_of_threeHalves_growth hA hbound n
    exact ball_subset_closedBall (by simpa [R] using hz)
  apply Real.exp_le_exp.mp
  calc
    Real.exp (L z).re = Real.exp (L z).re * 1 := by ring
    _ ≤ Real.exp (L z).re * ‖g 0‖ :=
      mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
    _ = ‖g z‖ := hid
    _ ≤ Real.exp (A * (R + 1) ^ (3 / 2 : ℝ)) := hgBound

/-- Borel--Carathéodory turns the real-part bound into a norm bound for the
canonical logarithm. -/
lemma norm_riemannXiCanonicalLog_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalLog n z‖ ≤
      2 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) * ‖z‖ /
        (xiCanonicalRadius n - ‖z‖) := by
  let R := xiCanonicalRadius n
  let L := riemannXiCanonicalLog n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero
    (M := A * (R + 1) ^ (3 / 2 : ℝ))
    (by positivity) hdiff
  · intro w hw
    exact riemannXiCanonicalLog_re_le_of_threeHalves_growth hA hbound n
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact riemannXiCanonicalLog_zero n

/-- Canonical decomposition gives a quantitative lower bound for xi at an
inner point separated from every zero in the enclosing divisor. -/
theorem exp_neg_xiCanonicalThreeHalvesLowerExponent_le_norm_riemannXi
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * (‖w‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hz : ‖z‖ ≤ xiCanonicalRadius n / 4)
    (hxi : riemannXi z ≠ 0)
    (hsep : ∀ i,
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 →
        delta ≤ ‖z - i‖) :
    Real.exp (- (
        2 * A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) +
        (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤
      ‖riemannXi z‖ := by
  let R : ℝ := xiCanonicalRadius n
  let g : ℂ → ℂ := riemannXiCanonicalResidual n
  let L : ℂ → ℂ := riemannXiCanonicalLog n
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let C : ℝ := Real.log (1 + 2 * R / delta)
  let M : ℝ := 2 * A * (R + 1) ^ (3 / 2 : ℝ)
  let N : ℝ := (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) * C
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hzball : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt (by dsimp only [R] at hz ⊢; linarith)
  have hzclosed : z ∈ closedBall 0 R := ball_subset_closedBall hzball
  have hLraw := norm_riemannXiCanonicalLog_le_of_threeHalves_growth
    hA hbound n hzball
  have hden : 0 < R - ‖z‖ := by
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hratio : ‖z‖ / (R - ‖z‖) ≤ 1 := by
    rw [div_le_one hden]
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hL : ‖L z‖ ≤ M := by
    calc
      ‖L z‖ ≤ 2 * (A * (R + 1) ^ (3 / 2 : ℝ)) * ‖z‖ /
          (R - ‖z‖) := by simpa [L, R] using hLraw
      _ = (2 * A * (R + 1) ^ (3 / 2 : ℝ)) *
          (‖z‖ / (R - ‖z‖)) := by ring
      _ ≤ (2 * A * (R + 1) ^ (3 / 2 : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = M := by simp [M]
  have hnormResidual := congrArg norm
    (exp_riemannXiCanonicalLog_mul_zero_eq n hzball)
  have hnormResidual' :
      Real.exp (L z).re * ‖g 0‖ = ‖g z‖ := by
    simpa [L, g, norm_mul, Complex.norm_exp] using hnormResidual
  have hLre : -‖L z‖ ≤ (L z).re :=
    (abs_le.mp (Complex.abs_re_le_norm (L z))).1
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hexpResidual : Real.exp (-M) ≤ ‖g z‖ := by
    calc
      Real.exp (-M) ≤ Real.exp (-‖L z‖) :=
        Real.exp_le_exp.mpr (neg_le_neg hL)
      _ ≤ Real.exp (L z).re := Real.exp_le_exp.mpr hLre
      _ = Real.exp (L z).re * 1 := by ring
      _ ≤ Real.exp (L z).re * ‖g 0‖ :=
        mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
      _ = ‖g z‖ := hnormResidual'
  have hlogResidual : -M ≤ Real.log ‖g z‖ := by
    calc
      -M = Real.log (Real.exp (-M)) := by rw [Real.log_exp]
      _ ≤ Real.log ‖g z‖ :=
        Real.log_le_log (Real.exp_pos _) hexpResidual
  have hdFinite : (Function.support d).Finite := by
    simpa [d, R] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  have hC : 0 ≤ C := by
    apply Real.log_nonneg
    have hquot : 0 ≤ 2 * R / delta := by positivity
    linarith
  have hfactorLog : ∀ i, d i ≠ 0 →
      Real.log ‖Complex.canonicalFactor R i z‖ ≤ C := by
    intro i hi
    have hiBall : i ∈ ball 0 R :=
      (divisor riemannXi (ball 0 R)).supportWithinDomain
        (by simpa [d] using hi)
    have hsepi : delta ≤ ‖z - i‖ := by
      apply hsep i
      simpa [d, R] using hi
    have hfactor := norm_canonicalFactor_le_of_inner_of_separated
      hR hdelta hiBall (by simpa [R] using hz) hsepi
    have hzi : z ≠ i := by
      intro hzi
      subst i
      simpa using (hdelta.trans_le hsepi).ne'
    have hfactorPos : 0 < ‖Complex.canonicalFactor R i z‖ :=
      norm_pos_iff.mpr
        (Complex.canonicalFactor_ne_zero hiBall hzclosed hzi)
    apply Real.log_le_log hfactorPos
    exact hfactor.trans (by linarith)
  have hcanonicalRaw := finsum_intCast_mul_le_of_nonneg
    hdFinite hdnonneg hfactorLog
  have hcount := sum_divisor_riemannXi_ball_le_threeHalves_of_growth hA hbound n
  have hcanonical :
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) ≤ N := by
    calc
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) ≤
        ((∑ᶠ i, d i : ℤ) : ℝ) * C := hcanonicalRaw
      _ ≤ (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) * C := by
        apply mul_le_mul_of_nonneg_right
        · simpa [d, R] using hcount
        · exact hC
      _ = N := by rfl
  have horder : meromorphicOrderAt riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    hzclosed horder hR
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      simpa [R] using
        divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i ↦ by simp)
  have htrailing : meromorphicTrailingCoeffAt riemannXi z = riemannXi z :=
    (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi
  change Real.log ‖g z‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  simp only [sub_zero] at hlog
  have hlogXi : Real.log ‖riemannXi z‖ =
      Real.log ‖g z‖ -
        (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) := by
    change Real.log ‖g z‖ =
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) +
          Real.log ‖riemannXi z‖ at hlog
    linarith
  have hlowerLog : -(M + N) ≤ Real.log ‖riemannXi z‖ := by
    rw [hlogXi]
    linarith
  have hlower := Real.exp_le_exp.mpr hlowerLog
  rw [Real.exp_log (norm_pos_iff.mpr hxi)] at hlower
  simpa only [M, N, C, R, neg_add_rev] using hlower

/-- The explicit three-halves-growth exponent controlling xi on the
quantitative vertical boundary. -/
noncomputable def xiQuantitativeBoundaryThreeHalvesLowerExponent
    (A : ℝ) (n : ℕ) : ℝ :=
  2 * A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) +
    (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
      Real.log
        (1 + 2 * xiCanonicalRadius n / spectralBoundarySeparation n)

/-- Spectral xi is bounded below by the explicit three-halves exponent
throughout the selected segment. -/
theorem exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤
        Real.exp (A * (‖w‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {y : ℝ} (hylo : -1 ≤ y) (hyhi : y ≤ 1) :
    Real.exp (-xiQuantitativeBoundaryThreeHalvesLowerExponent A n) ≤
      ‖riemannXiSpectral
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ := by
  let w : ℂ :=
    (quantitativeSpectralBoundaryTruncation n : ℂ) +
      (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate w
  have hlower :=
    exp_neg_xiCanonicalThreeHalvesLowerExponent_le_norm_riemannXi
      hA hbound n (z := s) (delta := spectralBoundarySeparation n)
        (spectralBoundarySeparation_pos n)
        (by simpa [s, w] using
          norm_quantitativeCompletedCoordinate_le_quarter n hylo hyhi)
        (by simpa [s, w] using
          riemannXi_quantitativeCompletedCoordinate_ne_zero n y)
        (fun i hi ↦ by
          simpa [s, w] using
            spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero
              n y hi)
  simpa [xiQuantitativeBoundaryThreeHalvesLowerExponent,
    riemannXiSpectral, s, w] using hlower

/-- An unconditional three-halves-growth lower floor exists on every selected
vertical boundary. -/
theorem exists_riemannXiSpectral_quantitativeVerticalBoundary_threeHalves_lower_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) {y : ℝ}, -1 ≤ y → y ≤ 1 →
      Real.exp (-xiQuantitativeBoundaryThreeHalvesLowerExponent A n) ≤
        ‖riemannXiSpectral
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA, fun n y hylo hyhi ↦
    exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral
      hA hbound n hylo hyhi⟩

/-- A polynomial-logarithmic majorant for the quantitative lower exponent. -/
noncomputable def xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant
    (A : ℝ) (n : ℕ) : ℝ :=
  2 * A *
      (14 * (quantitativeSpectralBoundaryTruncation n + 1)) ^
        (3 / 2 : ℝ) +
    ((A / Real.log 2) *
        (27 * (quantitativeSpectralBoundaryTruncation n + 1)) ^
          (3 / 2 : ℝ)) *
      (Real.log (1 + 78 * (25 * (A / Real.log 2) + 4)) +
        3 * Real.log (quantitativeSpectralBoundaryTruncation n + 1))

/-- The canonical lower exponent is at most the explicit
polynomial-logarithmic majorant. -/
lemma xiQuantitativeBoundaryThreeHalvesLowerExponent_le_polynomialLog
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    xiQuantitativeBoundaryThreeHalvesLowerExponent A n ≤
      xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant A n := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := xiCanonicalRadius n
  let delta : ℝ := spectralBoundarySeparation n
  let X : ℝ := T + 1
  let B : ℝ := A / Real.log 2
  let D : ℝ := 1 + 78 * (25 * B + 4)
  have hA0 : 0 ≤ A := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hT0 : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1.le)
  have hX1 : 1 ≤ X := by dsimp [X]; linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hRpos : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hdelta : 0 < delta := by
    simpa [delta] using spectralBoundarySeparation_pos n
  have hRupper : R ≤ 13 * X := by
    have hr := (xiCanonicalRadius_spec n).2.1
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [R, T, X]
    linarith
  have hRone : R + 1 ≤ 14 * X := by
    linarith
  have htwoRone : 2 * R + 1 ≤ 27 * X := by
    calc
      2 * R + 1 ≤ 2 * (13 * X) + 1 := by gcongr
      _ ≤ 27 * X := by linarith
  have hbase : 2 * ((n : ℝ) + 2) + 1 ≤ 5 * X := by
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [T, X]
    linarith
  have hbaseRpow :
      (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) ≤
        (5 * X) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hfiveXOne : 1 ≤ 5 * X := by nlinarith
  have hthreeHalvesTwo :
      (5 * X) ^ (3 / 2 : ℝ) ≤ (5 * X) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hfiveXOne (by norm_num)
  have hsepRaw := one_div_spectralBoundarySeparation_le_threeHalves_of_growth
    hA hbound n
  have hsep : 1 / delta ≤ 3 * (25 * B + 4) * X ^ 2 := by
    calc
      1 / delta ≤
          3 *
            (A * (2 * ((n : ℝ) + 2) + 1) ^ (3 / 2 : ℝ) /
                Real.log 2 + 4) := by
        simpa [delta] using hsepRaw
      _ ≤ 3 * (A * (5 * X) ^ (3 / 2 : ℝ) / Real.log 2 + 4) := by
        gcongr
      _ ≤ 3 * (A * (5 * X) ^ (2 : ℝ) / Real.log 2 + 4) := by
        gcongr
      _ = 3 * (25 * B * X ^ 2 + 4) := by
        rw [Real.rpow_two]
        dsimp [B]
        ring
      _ ≤ 3 * (25 * B + 4) * X ^ 2 := by
        have hXsq : 1 ≤ X ^ 2 := by nlinarith
        nlinarith
  have hquot : 2 * R / delta ≤ 78 * (25 * B + 4) * X ^ 3 := by
    rw [div_eq_mul_inv]
    calc
      2 * R * delta⁻¹ ≤ 2 * (13 * X) * (3 * (25 * B + 4) * X ^ 2) := by
        gcongr
        simpa [one_div] using hsep
      _ = 78 * (25 * B + 4) * X ^ 3 := by ring
  have hlogArg :
      Real.log (1 + 2 * R / delta) ≤ Real.log (D * X ^ 3) := by
    apply Real.log_le_log
    · positivity
    · calc
        1 + 2 * R / delta ≤
            1 + 78 * (25 * B + 4) * X ^ 3 := by linarith
        _ ≤ D * X ^ 3 := by
          have hXcube : 1 ≤ X ^ 3 := by nlinarith
          dsimp [D]
          nlinarith [mul_nonneg (by positivity : 0 ≤ 78 * (25 * B + 4))
            (sub_nonneg.mpr hXcube)]
  have hlog : Real.log (1 + 2 * R / delta) ≤
      Real.log D + 3 * Real.log X := by
    calc
      Real.log (1 + 2 * R / delta) ≤ Real.log (D * X ^ 3) := hlogArg
      _ = Real.log D + 3 * Real.log X := by
        rw [Real.log_mul hDpos.ne' (pow_ne_zero 3 hXpos.ne'), Real.log_pow]
        norm_num
  have hlogNonneg : 0 ≤ Real.log (1 + 2 * R / delta) := by
    apply Real.log_nonneg
    have hquotNonneg : 0 ≤ 2 * R / delta := by positivity
    linarith
  have hRoneRpow :
      (R + 1) ^ (3 / 2 : ℝ) ≤ (14 * X) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hRone (by norm_num)
  have htwoRoneRpow :
      (2 * R + 1) ^ (3 / 2 : ℝ) ≤
        (27 * X) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) htwoRone (by norm_num)
  have hmain :
      2 * A * (R + 1) ^ (3 / 2 : ℝ) +
          (B * (2 * R + 1) ^ (3 / 2 : ℝ)) *
            Real.log (1 + 2 * R / delta) ≤
        2 * A * (14 * X) ^ (3 / 2 : ℝ) +
          (B * (27 * X) ^ (3 / 2 : ℝ)) *
            (Real.log D + 3 * Real.log X) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hRoneRpow (by positivity)
    · exact mul_le_mul
        (mul_le_mul_of_nonneg_left htwoRoneRpow hB0)
        hlog hlogNonneg (by positivity)
  dsimp [xiQuantitativeBoundaryThreeHalvesLowerExponent,
    xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant,
    R, T, delta, X, B, D] at hmain ⊢
  convert hmain using 1
  ring

/-- The polynomial-logarithmic majorant is little-o of the squared endpoint
height. -/
lemma tendsto_xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant_div_sq_zero
    (A : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ 2)
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun n ↦ quantitativeSpectralBoundaryTruncation n + 1
  let D : ℝ := 1 + 78 * (25 * (A / Real.log 2) + 4)
  let K₁ : ℝ := 2 * A * 14 ^ (3 / 2 : ℝ)
  let K₂ : ℝ := (A / Real.log 2) * 27 ^ (3 / 2 : ℝ)
  let L : ℝ := Real.log D
  have hX : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hXpos (n : ℕ) : 0 < X n := by
    have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
      (Nat.cast_nonneg n).trans_lt
        (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [X]
    linarith
  have hinvSqrt : Tendsto (fun n : ℕ ↦ X n ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hX
  have hlogInvSqrt : Tendsto
      (fun n : ℕ ↦ Real.log (X n) * X n ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ ↦ Real.log x / x ^ (1 / 2 : ℝ))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
        |>.tendsto_div_nhds_zero
    refine (hraw.comp hX).congr' (Eventually.of_forall fun n ↦ ?_)
    simp only [Function.comp_apply]
    rw [Real.rpow_neg (hXpos n).le]
    ring
  have hcombined : Tendsto
      (fun n : ℕ ↦
        K₁ * X n ^ (-(1 / 2 : ℝ)) +
          K₂ * L * X n ^ (-(1 / 2 : ℝ)) +
          3 * K₂ *
            (Real.log (X n) * X n ^ (-(1 / 2 : ℝ))))
      atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : ℕ ↦ K₁ * X n ^ (-(1 / 2 : ℝ)))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hinvSqrt
    have h₂ : Tendsto
        (fun n : ℕ ↦ K₂ * L * X n ^ (-(1 / 2 : ℝ)))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hinvSqrt
    have h₃ : Tendsto
        (fun n : ℕ ↦ 3 * K₂ *
          (Real.log (X n) * X n ^ (-(1 / 2 : ℝ))))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hlogInvSqrt
    simpa using (h₁.add h₂).add h₃
  refine hcombined.congr' (Eventually.of_forall fun n ↦ ?_)
  have h14 : (14 * X n) ^ (3 / 2 : ℝ) =
      14 ^ (3 / 2 : ℝ) * X n ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (hXpos n).le]
  have h27 : (27 * X n) ^ (3 / 2 : ℝ) =
      27 ^ (3 / 2 : ℝ) * X n ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (hXpos n).le]
  have hratio : X n ^ (3 / 2 : ℝ) / X n ^ 2 =
      X n ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_sub (hXpos n)]
    norm_num
  symm
  change
    xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant A n / X n ^ 2 = _
  calc
    xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant A n / X n ^ 2 =
        K₁ * (X n ^ (3 / 2 : ℝ) / X n ^ 2) +
          K₂ * L * (X n ^ (3 / 2 : ℝ) / X n ^ 2) +
          3 * K₂ *
            (Real.log (X n) *
              (X n ^ (3 / 2 : ℝ) / X n ^ 2)) := by
      rw [xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant,
        show quantitativeSpectralBoundaryTruncation n + 1 = X n by rfl,
        h14, h27]
      dsimp [D, K₁, K₂, L]
      ring
    _ = K₁ * X n ^ (-(1 / 2 : ℝ)) +
          K₂ * L * X n ^ (-(1 / 2 : ℝ)) +
          3 * K₂ *
            (Real.log (X n) * X n ^ (-(1 / 2 : ℝ))) := by
      rw [hratio]

/-- The quantitative three-halves lower exponent is nonnegative. -/
lemma xiQuantitativeBoundaryThreeHalvesLowerExponent_nonneg
    {A : ℝ} (hA : 1 ≤ A) (n : ℕ) :
    0 ≤ xiQuantitativeBoundaryThreeHalvesLowerExponent A n := by
  unfold xiQuantitativeBoundaryThreeHalvesLowerExponent
  have hA0 : 0 ≤ A := by linarith
  have hR : 0 < xiCanonicalRadius n := xiCanonicalRadius_pos n
  have hdelta : 0 < spectralBoundarySeparation n :=
    spectralBoundarySeparation_pos n
  have hlog : 0 ≤ Real.log
      (1 + 2 * xiCanonicalRadius n /
        spectralBoundarySeparation n) := by
    apply Real.log_nonneg
    have hquot : 0 ≤ 2 * xiCanonicalRadius n /
        spectralBoundarySeparation n := by positivity
    linarith
  positivity

/-- The canonical lower exponent is little-o of the squared endpoint height. -/
lemma tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryThreeHalvesLowerExponent A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      exact div_nonneg
        (xiQuantitativeBoundaryThreeHalvesLowerExponent_nonneg hA n)
        (by positivity)
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
        (xiQuantitativeBoundaryThreeHalvesLowerExponent_le_polynomialLog
          hA hbound n)
      positivity
  · exact
      tendsto_xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant_div_sq_zero A

/-- The negative logarithm of spectral xi at the selected critical endpoints
is subquadratic. -/
theorem tendsto_riemannXiSpectral_quantitativeCritical_log_negativePart_div_sq_zero :
    Tendsto
      (fun n : ℕ ↦
        max 0
            (-Real.log ‖riemannXiSpectral
              (quantitativeSpectralBoundaryTruncation n : ℂ)‖) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ 2)
      atTop (nhds 0) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hbound⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
      · apply max_le
        · exact xiQuantitativeBoundaryThreeHalvesLowerExponent_nonneg hA n
        · have hlower :=
            exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral
              hA hbound n (y := 0) (by norm_num) (by norm_num)
          have hlog := Real.log_le_log (Real.exp_pos _) hlower
          rw [Real.log_exp] at hlog
          have hlog' :
              -xiQuantitativeBoundaryThreeHalvesLowerExponent A n ≤
                Real.log ‖riemannXiSpectral
                  (quantitativeSpectralBoundaryTruncation n : ℂ)‖ := by
            simpa using hlog
          linarith
      · positivity
  · exact
      tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero
        hA hbound

/-- The uniform gamma-strip mass used in the critical-line comparison is
positive. -/
lemma gammaStripMass_pos : 0 < gammaStripMass := by
  have hbound := norm_Gamma_strip_le
    (s := (1 / 4 : ℂ)) (by norm_num) (by norm_num)
  exact (norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by norm_num))).trans_le hbound

/-- A positive uniform upper mass for the completed gamma factor on the
critical line. -/
noncomputable def staticContourCriticalGammaRUpperMass : ℝ :=
  max 1 (Real.pi ^ (-(1 / 4 : ℝ)) * gammaStripMass)

/-- The critical completed-gamma upper mass is at least one. -/
lemma one_le_staticContourCriticalGammaRUpperMass :
    1 ≤ staticContourCriticalGammaRUpperMass := by
  exact le_max_left _ _

/-- The completed gamma factor is uniformly bounded at every critical contour
endpoint. -/
lemma norm_GammaR_staticContourCriticalEndpoint_le_mass (T : ℝ) :
    ‖Complex.Gammaℝ (staticContourCriticalEndpoint T)‖ ≤
      staticContourCriticalGammaRUpperMass := by
  let s : ℂ := staticContourCriticalEndpoint T
  have hGamma := norm_Gamma_strip_le
    (s := s / 2) (by norm_num [s, staticContourCriticalEndpoint])
      (by norm_num [s, staticContourCriticalEndpoint])
  have hcpow :
      ‖((Real.pi : ℂ) ^ (-s / 2))‖ =
        Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp [s, staticContourCriticalEndpoint]
    ring
  rw [Complex.Gammaℝ_def, norm_mul, hcpow]
  exact (mul_le_mul_of_nonneg_left hGamma (by positivity)).trans
    (le_max_right _ _)

/-- The logarithm of the completed gamma norm is uniformly bounded at critical
endpoints. -/
lemma log_norm_GammaR_staticContourCriticalEndpoint_le_log_mass (T : ℝ) :
    Real.log ‖Complex.Gammaℝ (staticContourCriticalEndpoint T)‖ ≤
      Real.log staticContourCriticalGammaRUpperMass := by
  have hGamma : Complex.Gammaℝ (staticContourCriticalEndpoint T) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp [staticContourCriticalEndpoint])
  exact Real.log_le_log (norm_pos_iff.mpr hGamma)
    (norm_GammaR_staticContourCriticalEndpoint_le_mass T)

/-- The polynomial factor in completed xi contributes at most twice the
logarithmic height. -/
lemma log_norm_staticContourCriticalPolynomial_le_two_log_add_one
    {T : ℝ} (hT : 0 ≤ T) :
    Real.log ‖staticContourCriticalEndpoint T *
        (1 - staticContourCriticalEndpoint T)‖ ≤
      2 * Real.log (T + 1) := by
  let s : ℂ := staticContourCriticalEndpoint T
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, staticContourCriticalEndpoint] at hre
  have hs1 : 1 - s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, staticContourCriticalEndpoint] at hre
  have hnorm : ‖s * (1 - s)‖ ≤ (T + 1) ^ 2 := by
    have hsNorm := norm_staticContourCriticalEndpoint_le_add_one hT
    have hstar : ‖starRingEnd ℂ s‖ = ‖s‖ := by
      exact norm_star s
    rw [show 1 - s = starRingEnd ℂ s by
      simpa [s] using one_sub_staticContourCriticalEndpoint T,
      norm_mul, hstar]
    nlinarith [norm_nonneg s]
  have hlog := Real.log_le_log
    (norm_pos_iff.mpr (mul_ne_zero hs0 hs1)) hnorm
  rw [Real.log_pow] at hlog
  simpa [s] using hlog

/-- The critical zeta negative logarithm is controlled by the xi lower
exponent and elementary factors. -/
lemma criticalZeta_log_negativePart_le_threeHalvesLowerExponent
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    max 0
        (-Real.log ‖riemannZeta
          (staticContourCriticalEndpoint
            (quantitativeSpectralBoundaryTruncation n))‖) ≤
      xiQuantitativeBoundaryThreeHalvesLowerExponent A n +
        2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) +
        Real.log staticContourCriticalGammaRUpperMass := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let s : ℂ := staticContourCriticalEndpoint T
  let E : ℝ := xiQuantitativeBoundaryThreeHalvesLowerExponent A n
  let G : ℝ := staticContourCriticalGammaRUpperMass
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hxi : riemannXi s ≠ 0 := by
    simpa [s, T] using
      riemannXi_staticContourCriticalEndpoint_quantitative_ne_zero n
  have hsre : 0 < s.re := by simp [s, staticContourCriticalEndpoint]
  have hsone : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, staticContourCriticalEndpoint] at hre
  have hlower :=
    exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral
      hA hbound n (y := 0) (by norm_num) (by norm_num)
  have hlower' : Real.exp (-E) ≤ ‖riemannXi s‖ := by
    simpa [E, s, T, riemannXiSpectral, completedSpectralCoordinate,
      staticContourCriticalEndpoint, mul_comm] using hlower
  have hxiLog : -E ≤ Real.log ‖riemannXi s‖ := by
    have hlog := Real.log_le_log (Real.exp_pos _) hlower'
    simpa using hlog
  have hsplit := log_norm_riemannXi_eq_polynomial_add_GammaR_add_zeta
    hsre hsone hxi
  have hpoly : Real.log ‖s * (1 - s)‖ ≤
      2 * Real.log (T + 1) := by
    simpa [s] using
      log_norm_staticContourCriticalPolynomial_le_two_log_add_one hT.le
  have hgamma : Real.log ‖Complex.Gammaℝ s‖ ≤ Real.log G := by
    simpa [s, G] using
      log_norm_GammaR_staticContourCriticalEndpoint_le_log_mass T
  have hE0 : 0 ≤ E := by
    simpa [E] using
      xiQuantitativeBoundaryThreeHalvesLowerExponent_nonneg hA n
  have hlogT0 : 0 ≤ Real.log (T + 1) :=
    Real.log_nonneg (by linarith)
  have hlogG0 : 0 ≤ Real.log G :=
    Real.log_nonneg (by
      simpa [G] using one_le_staticContourCriticalGammaRUpperMass)
  have hnegative : -Real.log ‖riemannZeta s‖ ≤
      E + 2 * Real.log (T + 1) + Real.log G := by
    linarith
  change max 0 (-Real.log ‖riemannZeta s‖) ≤
    E + 2 * Real.log (T + 1) + Real.log G
  exact max_le (by positivity) hnegative

/-- The full critical-zeta negative-log majorant is little-o of the squared
endpoint height. -/
lemma tendsto_criticalZeta_threeHalvesNegativeMajorant_div_sq_zero
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (xiQuantitativeBoundaryThreeHalvesLowerExponent A n +
            2 * Real.log
              (quantitativeSpectralBoundaryTruncation n + 1) +
            Real.log staticContourCriticalGammaRUpperMass) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ 2)
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun n ↦ quantitativeSpectralBoundaryTruncation n + 1
  have hX : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hXsq : Tendsto (fun n : ℕ ↦ X n ^ 2) atTop atTop := by
    have hraw := (tendsto_rpow_atTop (y := (2 : ℝ)) (by norm_num)).comp hX
    change Tendsto (fun n : ℕ ↦ X n ^ (2 : ℝ)) atTop atTop at hraw
    simpa only [Real.rpow_two] using hraw
  have hE : Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryThreeHalvesLowerExponent A n / X n ^ 2)
      atTop (nhds 0) := by
    simpa [X] using
      tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero
        hA hbound
  have hlog : Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ 2)
      atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ ↦ Real.log x / x ^ (2 : ℝ))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2))
        |>.tendsto_div_nhds_zero
    have hcomposed := hraw.comp hX
    change Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ (2 : ℝ))
      atTop (nhds 0) at hcomposed
    simpa only [Real.rpow_two] using hcomposed
  have htwoLog : Tendsto
      (fun n : ℕ ↦ 2 * (Real.log (X n) / X n ^ 2))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hconstant : Tendsto
      (fun n : ℕ ↦
        Real.log staticContourCriticalGammaRUpperMass / X n ^ 2)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hXsq
  have hsum : Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryThreeHalvesLowerExponent A n / X n ^ 2 +
          2 * (Real.log (X n) / X n ^ 2) +
          Real.log staticContourCriticalGammaRUpperMass / X n ^ 2)
      atTop (nhds 0) := by
    simpa only [add_zero] using (hE.add htwoLog).add hconstant
  refine hsum.congr' (Eventually.of_forall fun n ↦ ?_)
  dsimp [X]
  ring

/-- Along the selected nonzero critical endpoints, the negative logarithm of
zeta is subquadratic. -/
theorem tendsto_criticalZeta_log_negativePart_div_quantitative_sq_zero :
    Tendsto
      (fun n : ℕ ↦
        max 0
            (-Real.log ‖riemannZeta
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ 2)
      atTop (nhds 0) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hbound⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
        (criticalZeta_log_negativePart_le_threeHalvesLowerExponent
          hA hbound n)
      positivity
  · exact tendsto_criticalZeta_threeHalvesNegativeMajorant_div_sq_zero
      hA hbound

end

end RiemannGaussian
