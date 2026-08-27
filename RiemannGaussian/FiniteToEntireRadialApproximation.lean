import RiemannGaussian.FiniteToEntireRadialBoundary
import RiemannGaussian.FiniteToEntireExpandingPinned

/-!
# Radial approximation below the xi boundary floor

The expanding spectral circles carry a rigorously proved lower modulus for
xi.  This file reindexes the exact-root Taylor construction at an explicit
single-exponential rate.  The geometric Taylor and root-pinning errors, and
the separately normalized separability perturbation, then fall strictly
below that lower modulus on every selected circle.  The same schedule retains
a single-exponential degree bound, which is essential for the later Gaussian
tail argument.
-/

open Complex Filter Metric Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Powers of one half have a convenient exponential majorant. -/
theorem half_pow_le_exp_neg_half (N : ℕ) :
    ((1 : ℝ) / 2) ^ N ≤ Real.exp (-((N : ℝ) / 2)) := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  calc
    ((1 : ℝ) / 2) ^ N = (Real.exp (-Real.log 2)) ^ N := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ = Real.exp ((N : ℝ) * (-Real.log 2)) :=
      (Real.exp_nat_mul (-Real.log 2) N).symm
    _ ≤ Real.exp (-((N : ℝ) / 2)) := by
      apply Real.exp_le_exp.mpr
      have hN : 0 ≤ (N : ℝ) := by positivity
      nlinarith

/-- The fixed coefficient in the geometric finite-homotopy residual bound. -/
noncomputable def finiteERootPinnedResidualConstant
    (A eta : ℝ) (z : ℂ) : ℝ :=
  (1 + |eta|) * 2 * Real.exp (A * (2 * ‖z‖ + 4) ^ 2)

/-- A positive coefficient simultaneously majorizing the Taylor error and
the affine exact-root correction on every nonnegative radial disk. -/
noncomputable def finiteERootPinnedRadialConstant
    (A eta : ℝ) (z : ℂ) : ℝ :=
  let K := finiteERootPinnedResidualConstant A eta z
  2 + K + (K / |z.im + eta|) * (|z.re| + 1)

/-- The radial pinned-error coefficient is positive. -/
theorem finiteERootPinnedRadialConstant_pos
    {A eta : ℝ} {z : ℂ} :
    0 < finiteERootPinnedRadialConstant A eta z := by
  let K := finiteERootPinnedResidualConstant A eta z
  have hK : 0 ≤ K := by
    dsimp [K, finiteERootPinnedResidualConstant]
    positivity
  have hquot : 0 ≤ K / |z.im + eta| := by positivity
  dsimp only [finiteERootPinnedRadialConstant]
  positivity

/-- One growth constant gives a geometric bound for both raw Taylor
approximation and the analytic finite-homotopy residual. -/
theorem exists_riemannXiSpectral_taylor_and_finiteE_geometric_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      (∀ {r : ℝ}, 0 < r → ∀ {N : ℕ} {w : ℂ}, ‖w‖ ≤ r →
        ‖((riemannXiSpectralRealTaylorPolynomial N).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
          2 * (Real.exp (A * (2 * r + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ N)) ∧
      (∀ (eta : ℝ) (z : ℂ) (N : ℕ),
        ‖(finiteEPolynomial
              (riemannXiSpectralRealTaylorPolynomial N) eta).eval z -
            analyticEValue riemannXiSpectral eta z‖ ≤
          (1 + |eta|) *
            (2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
              ((1 : ℝ) / 2) ^ N))) := by
  obtain ⟨A, hA, hTaylor⟩ :=
    exists_riemannXiSpectral_taylor_fixedDisk_geometric_bound
  obtain ⟨B, hB, hE⟩ :=
    exists_riemannXiSpectral_taylor_finiteE_geometric_bound
  let G : ℝ := max A B
  have hG : 1 ≤ G := hA.trans (le_max_left _ _)
  refine ⟨G, hG, ?_, ?_⟩
  · intro r hr N w hw
    have hraw := hTaylor hr (N := N) hw
    have hexp :
        Real.exp (A * (2 * r + 2) ^ 2) ≤
          Real.exp (G * (2 * r + 2) ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_max_left A B) (sq_nonneg _)
    exact hraw.trans (by gcongr)
  · intro eta z N
    have hraw := hE eta z N
    have hexp :
        Real.exp (B * (2 * ‖z‖ + 4) ^ 2) ≤
          Real.exp (G * (2 * ‖z‖ + 4) ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_max_right A B) (sq_nonneg _)
    exact hraw.trans (by gcongr)

/-- Exact affine root pinning preserves a fully explicit geometric radial
error bound. -/
theorem exists_riemannXiSpectral_pinnedTaylor_radial_geometric_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {eta : ℝ} {z : ℂ},
      analyticEValue riemannXiSpectral eta z = 0 →
      z.im + eta ≠ 0 →
      ∀ {N : ℕ} {r : ℝ}, 0 < r → ∀ {w : ℂ}, ‖w‖ ≤ r →
      ‖((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta z).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        finiteERootPinnedRadialConstant A eta z * (r + 1) *
          Real.exp (A * (2 * r + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ N := by
  obtain ⟨A, hA, hTaylor, hE⟩ :=
    exists_riemannXiSpectral_taylor_and_finiteE_geometric_bound
  refine ⟨A, hA, ?_⟩
  intro eta z hroot hden N r hr w hw
  let K : ℝ := finiteERootPinnedResidualConstant A eta z
  let D : ℝ := |z.im + eta|
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  let E : ℝ := Real.exp (A * (2 * r + 2) ^ 2)
  let q : ℝ := ((1 : ℝ) / 2) ^ N
  have hA0 : 0 ≤ A := hA.trans' zero_le_one
  have hK : 0 ≤ K := by
    dsimp [K, finiteERootPinnedResidualConstant]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    exact abs_pos.mpr hden
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (mul_nonneg hA0 (sq_nonneg _))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hres :
      ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial N) eta).eval z‖ ≤
        K * q := by
    calc
      ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial N) eta).eval z‖ =
          ‖(finiteEPolynomial
              (riemannXiSpectralRealTaylorPolynomial N) eta).eval z -
            analyticEValue riemannXiSpectral eta z‖ := by
        rw [hroot, sub_zero]
      _ ≤ (1 + |eta|) *
          (2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ N)) := hE eta z N
      _ = K * q := by
        simp only [K, q, finiteERootPinnedResidualConstant]
        ring
  have hpin := norm_finiteERootPinnedPolynomial_sub_le_residual
    (riemannXiSpectralRealTaylorPolynomial N) eta z w
  have hpin' :
      ‖((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta z).map
              Complex.ofRealHom).eval w -
          ((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval w‖ ≤
        (K + K / D * (|z.re| + r)) * q := by
    calc
      ‖((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta z).map
              Complex.ofRealHom).eval w -
          ((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval w‖ ≤
        ‖(finiteEPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta).eval z‖ +
          (‖(finiteEPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta).eval z‖ /
              |z.im + eta|) * (|z.re| + ‖w‖) := hpin
      _ ≤ K * q + (K * q / D) * (|z.re| + r) := by
        apply add_le_add hres
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hres (abs_nonneg _)
        · linarith
        · exact add_nonneg (abs_nonneg _) (norm_nonneg _)
        · positivity
      _ = (K + K / D * (|z.re| + r)) * q := by ring
  have hTaylor' :
      ‖((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        2 * E * q := by
    simpa only [E, q, mul_assoc] using hTaylor hr hw
  have hzr : |z.re| + r ≤ (|z.re| + 1) * (r + 1) := by
    have hz0 : 0 ≤ |z.re| := abs_nonneg _
    nlinarith [mul_nonneg hz0 hr.le]
  have hrE : 1 ≤ (r + 1) * E := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (r + 1) * E :=
        mul_le_mul (by linarith) hEone (by norm_num) (by linarith)
  have hcoeff :
      2 * E + K + K / D * (|z.re| + r) ≤
        L * (r + 1) * E := by
    have hKD : 0 ≤ K / D := by positivity
    have hrone : 1 ≤ r + 1 := by linarith
    have htwo : 2 * E ≤ 2 * E * (r + 1) := by
      simpa using
        mul_le_mul_of_nonneg_left hrone (show 0 ≤ 2 * E by positivity)
    have hKscale : K ≤ K * ((r + 1) * E) := by
      simpa using mul_le_mul_of_nonneg_left hrE hK
    have hrscale : r + 1 ≤ (r + 1) * E := by
      simpa using mul_le_mul_of_nonneg_left hEone (by linarith : 0 ≤ r + 1)
    have hthird :
        K / D * (|z.re| + r) ≤
          K / D * ((|z.re| + 1) * ((r + 1) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hKD
      calc
        |z.re| + r ≤ (|z.re| + 1) * (r + 1) := hzr
        _ ≤ (|z.re| + 1) * ((r + 1) * E) :=
          mul_le_mul_of_nonneg_left hrscale (by positivity)
    calc
      2 * E + K + K / D * (|z.re| + r) ≤
          2 * E * (r + 1) + K * ((r + 1) * E) +
            (K / D) * ((|z.re| + 1) * ((r + 1) * E)) := by
        exact add_le_add (add_le_add htwo hKscale) hthird
      _ = L * (r + 1) * E := by
        simp only [L, finiteERootPinnedRadialConstant, K, D]
        ring
  calc
    ‖((finiteERootPinnedPolynomial
          (riemannXiSpectralRealTaylorPolynomial N) eta z).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ =
        ‖(((finiteERootPinnedPolynomial
              (riemannXiSpectralRealTaylorPolynomial N) eta z).map
                Complex.ofRealHom).eval w -
            ((riemannXiSpectralRealTaylorPolynomial N).map
              Complex.ofRealHom).eval w) +
          (((riemannXiSpectralRealTaylorPolynomial N).map
              Complex.ofRealHom).eval w - riemannXiSpectral w)‖ := by
      congr 1
      ring
    _ ≤ ‖((finiteERootPinnedPolynomial
              (riemannXiSpectralRealTaylorPolynomial N) eta z).map
                Complex.ofRealHom).eval w -
            ((riemannXiSpectralRealTaylorPolynomial N).map
              Complex.ofRealHom).eval w‖ +
          ‖((riemannXiSpectralRealTaylorPolynomial N).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ :=
      norm_add_le _ _
    _ ≤ (K + K / D * (|z.re| + r)) * q + 2 * E * q :=
      add_le_add hpin' hTaylor'
    _ = (2 * E + K + K / D * (|z.re| + r)) * q := by ring
    _ ≤ (L * (r + 1) * E) * q :=
      mul_le_mul_of_nonneg_right hcoeff hq0
    _ = finiteERootPinnedRadialConstant A eta z * (r + 1) *
          Real.exp (A * (2 * r + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ N := by
      rfl

/-- Explicit Taylor index scheduled to beat the radial xi lower-modulus
exponent while retaining single-exponential growth. -/
noncomputable def radialRoucheIndex
    (A L C : ℝ) (n : ℕ) : ℕ :=
  let r := quantitativeSpectralRadialBoundary n
  ⌈2 * (L + r + A * (2 * r + 2) ^ 2 +
    C * Real.exp (5 * r) + 2)⌉₊

/-- The real scheduling target is below the cast of its natural ceiling. -/
theorem radialRoucheIndex_target_le_cast
    (A L C : ℝ) (n : ℕ) :
    2 * (L + quantitativeSpectralRadialBoundary n +
        A * (2 * quantitativeSpectralRadialBoundary n + 2) ^ 2 +
        C * Real.exp (5 * quantitativeSpectralRadialBoundary n) + 2) ≤
      (radialRoucheIndex A L C n : ℝ) := by
  exact Nat.le_ceil _

/-- For nonnegative parameters, the scheduled Taylor index is at least the
selected circle radius. -/
theorem quantitativeSpectralRadialBoundary_le_radialRoucheIndex
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (n : ℕ) :
    quantitativeSpectralRadialBoundary n ≤
      (radialRoucheIndex A L C n : ℝ) := by
  let r := quantitativeSpectralRadialBoundary n
  have hr : 0 ≤ r := by
    simpa [r] using (quantitativeSpectralRadialBoundary_pos n).le
  have htarget := radialRoucheIndex_target_le_cast A L C n
  have hAterm : 0 ≤ A * (2 * r + 2) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  have hCterm : 0 ≤ C * Real.exp (5 * r) := by positivity
  change r ≤ (radialRoucheIndex A L C n : ℝ)
  have htarget' :
      2 * (L + r + A * (2 * r + 2) ^ 2 +
        C * Real.exp (5 * r) + 2) ≤
        (radialRoucheIndex A L C n : ℝ) := by
    simpa [r] using htarget
  linarith

/-- Every positive-parameter radial Rouché schedule tends to infinity. -/
theorem tendsto_radialRoucheIndex_atTop
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    Tendsto (radialRoucheIndex A L C) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hradial := tendsto_quantitativeSpectralRadialBoundary_atTop
  rw [tendsto_atTop_atTop] at hradial
  obtain ⟨n, hn⟩ :=
    hradial (b : ℝ)
  refine ⟨n, fun m hnm => ?_⟩
  have hbRadius : (b : ℝ) ≤ quantitativeSpectralRadialBoundary m :=
    hn m hnm
  have hRadiusIndex :=
    quantitativeSpectralRadialBoundary_le_radialRoucheIndex
      hA hL hC m
  exact_mod_cast hbRadius.trans hRadiusIndex

/-- The harmless numerical factor used to make the final comparison
strict. -/
theorem exp_neg_two_lt_half :
    Real.exp (-2) < (1 : ℝ) / 2 := by
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num
  exact Real.exp_one_gt_two.trans
    (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2))

/-- At the scheduled index, the pinned Taylor geometric majorant is below
the xi floor times the strict slack factor `exp (-2)`. -/
theorem radialRoucheIndex_pinned_geometric_bound
    (A L C : ℝ) (n : ℕ) :
    L * (quantitativeSpectralRadialBoundary n + 1) *
          Real.exp
            (A * (2 * quantitativeSpectralRadialBoundary n + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ (radialRoucheIndex A L C n) ≤
      Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) *
        Real.exp (-2) := by
  let r : ℝ := quantitativeSpectralRadialBoundary n
  let N : ℕ := radialRoucheIndex A L C n
  let S : ℝ := L + r + A * (2 * r + 2) ^ 2
  have hr : 0 ≤ r := by
    simpa [r] using (quantitativeSpectralRadialBoundary_pos n).le
  have hN :
      2 * (S + C * Real.exp (5 * r) + 2) ≤ (N : ℝ) := by
    simpa [S, r, N, add_assoc] using
      radialRoucheIndex_target_le_cast A L C n
  have hhalf := half_pow_le_exp_neg_half N
  have hLexp : L ≤ Real.exp L := by
    exact (by linarith : L ≤ L + 1).trans (Real.add_one_le_exp L)
  have hrexp : r + 1 ≤ Real.exp r := Real.add_one_le_exp r
  have hcoefficient :
      L * (r + 1) * Real.exp (A * (2 * r + 2) ^ 2) ≤
        Real.exp S := by
    calc
      L * (r + 1) * Real.exp (A * (2 * r + 2) ^ 2) ≤
          Real.exp L * Real.exp r *
            Real.exp (A * (2 * r + 2) ^ 2) := by
        gcongr
      _ = Real.exp S := by
        rw [← Real.exp_add, ← Real.exp_add]
  calc
    L * (quantitativeSpectralRadialBoundary n + 1) *
          Real.exp
            (A * (2 * quantitativeSpectralRadialBoundary n + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ (radialRoucheIndex A L C n) =
        (L * (r + 1) * Real.exp (A * (2 * r + 2) ^ 2)) *
          ((1 : ℝ) / 2) ^ N := by rfl
    _ ≤ Real.exp S * Real.exp (-((N : ℝ) / 2)) :=
      mul_le_mul hcoefficient hhalf (by positivity) (by positivity)
    _ = Real.exp (S - (N : ℝ) / 2) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-C * Real.exp (5 * r) - 2) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp (-C * Real.exp (5 * r)) * Real.exp (-2) := by
      rw [← Real.exp_add]
      congr 1
    _ = Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) *
        Real.exp (-2) := by rfl

/-- The separability perturbation at the scheduled index has an even
smaller bound on the same xi-floor scale. -/
theorem radialRoucheIndex_separable_error_bound
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hC : 0 ≤ C)
    (n : ℕ) :
    Real.exp (-(radialRoucheIndex A L C n : ℝ)) / 2 ≤
      (Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) *
        Real.exp (-2)) / 2 := by
  let r : ℝ := quantitativeSpectralRadialBoundary n
  let N : ℕ := radialRoucheIndex A L C n
  let S : ℝ := L + r + A * (2 * r + 2) ^ 2
  have hr : 0 ≤ r := by
    simpa [r] using (quantitativeSpectralRadialBoundary_pos n).le
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hN :
      2 * (S + C * Real.exp (5 * r) + 2) ≤ (N : ℝ) := by
    simpa [S, r, N, add_assoc] using
      radialRoucheIndex_target_le_cast A L C n
  have hNfloor : C * Real.exp (5 * r) + 2 ≤ (N : ℝ) := by
    have hCterm : 0 ≤ C * Real.exp (5 * r) := by positivity
    linarith
  calc
    Real.exp (-(radialRoucheIndex A L C n : ℝ)) / 2 =
        Real.exp (-(N : ℝ)) / 2 := by rfl
    _ ≤ Real.exp (-C * Real.exp (5 * r) - 2) / 2 := by
      gcongr
      linarith
    _ = (Real.exp (-C * Real.exp (5 * r)) * Real.exp (-2)) / 2 := by
      rw [← Real.exp_add]
      congr 2
    _ = (Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) *
        Real.exp (-2)) / 2 := by rfl

/-- A convenient explicit coefficient in the schedule's upper growth
bound. -/
def radialRoucheIndexGrowthConstant (A L C : ℝ) : ℝ :=
  2 * (L + 4 * A + C + 3) + 1

/-- The scheduled degree remains bounded by a fixed multiple of
`exp (5 * r_n)`. -/
theorem radialRoucheIndex_cast_lt_exponential
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (n : ℕ) :
    (radialRoucheIndex A L C n : ℝ) <
      radialRoucheIndexGrowthConstant A L C *
        Real.exp (5 * quantitativeSpectralRadialBoundary n) := by
  let r : ℝ := quantitativeSpectralRadialBoundary n
  let E : ℝ := Real.exp (5 * r)
  let X : ℝ := 2 * (L + r + A * (2 * r + 2) ^ 2 + C * E + 2)
  have hr : 0 ≤ r := by
    simpa [r] using (quantitativeSpectralRadialBoundary_pos n).le
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (by positivity)
  have hrexp : r + 1 ≤ Real.exp r := Real.add_one_le_exp r
  have hexp25 : Real.exp (2 * r) ≤ E := by
    dsimp [E]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsquare : (r + 1) ^ 2 ≤ E := by
    calc
      (r + 1) ^ 2 ≤ (Real.exp r) ^ 2 :=
        (sq_le_sq₀ (by linarith) (by positivity)).mpr hrexp
      _ = Real.exp (2 * r) := by
        rw [show 2 * r = (2 : ℕ) * r by norm_num]
        exact (Real.exp_nat_mul r 2).symm
      _ ≤ E := hexp25
  have hquadratic : A * (2 * r + 2) ^ 2 ≤ 4 * A * E := by
    calc
      A * (2 * r + 2) ^ 2 = 4 * A * (r + 1) ^ 2 := by ring
      _ ≤ 4 * A * E :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
  have hrE : r ≤ E := by
    exact (by linarith : r ≤ r + 1).trans
      (hrexp.trans (by
        exact Real.exp_le_exp.mpr (by linarith)))
  have hsum :
      L + r + A * (2 * r + 2) ^ 2 + C * E + 2 ≤
        (L + 4 * A + C + 3) * E := by
    have hLE : L ≤ L * E := by
      simpa using mul_le_mul_of_nonneg_left hEone hL
    have htwoE : 2 ≤ 2 * E := by
      simpa using
        mul_le_mul_of_nonneg_left hEone (by norm_num : (0 : ℝ) ≤ 2)
    calc
      L + r + A * (2 * r + 2) ^ 2 + C * E + 2 ≤
          L * E + E + 4 * A * E + C * E + 2 * E := by
        linarith
      _ = (L + 4 * A + C + 3) * E := by ring
  have hX0 : 0 ≤ X := by positivity
  have hceil : (radialRoucheIndex A L C n : ℝ) < X + 1 := by
    simpa [radialRoucheIndex, r, E, X] using
      (Nat.ceil_lt_add_one hX0)
  have hXbound :
      X + 1 ≤ (2 * (L + 4 * A + C + 3) + 1) * E := by
    change
      2 * (L + r + A * (2 * r + 2) ^ 2 + C * E + 2) + 1 ≤
        (2 * (L + 4 * A + C + 3) + 1) * E
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  calc
    (radialRoucheIndex A L C n : ℝ) < X + 1 := hceil
    _ ≤ (2 * (L + 4 * A + C + 3) + 1) * E := hXbound
    _ = radialRoucheIndexGrowthConstant A L C *
        Real.exp (5 * quantitativeSpectralRadialBoundary n) := by
      rfl

/-- If RH fails, there is a separable exact-root finite Hardy sequence whose
scheduled approximation error is strictly below spectral xi on every
selected expanding circle.  Its Taylor indices tend to infinity and remain
bounded by a fixed multiple of `exp (5 * r_n)`. -/
theorem exists_radialRouche_canonicalFiniteHardyFrontier_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
        ∃ B : ℕ → ℝ[X],
          let L := finiteERootPinnedRadialConstant A eta z
          Tendsto (radialRoucheIndex A L C) atTop atTop ∧
          TendstoLocallyUniformlyOn
            (fun n w => ((B n).map Complex.ofRealHom).eval w)
            riemannXiSpectral atTop Set.univ ∧
          (∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
            (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3) ∧
          (∀ n, (radialRoucheIndex A L C n : ℝ) <
            radialRoucheIndexGrowthConstant A L C *
              Real.exp (5 * quantitativeSpectralRadialBoundary n)) ∧
          (∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
              Real.exp
                  (-C * Real.exp
                    (5 * quantitativeSpectralRadialBoundary n)) ≤
                ‖riemannXiSpectral w‖) ∧
          ∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
            ‖((B n).map Complex.ofRealHom).eval w -
                riemannXiSpectral w‖ <
              Real.exp
                (-C * Real.exp
                  (5 * quantitativeSpectralRadialBoundary n)) ∧
            ‖((B n).map Complex.ofRealHom).eval w -
                riemannXiSpectral w‖ < ‖riemannXiSpectral w‖ := by
  obtain ⟨eta, heta, z, hz, hroot⟩ :=
    exists_positive_riemannXiSpectral_analyticEValue_upper_root_of_not_rh hRH
  have hden : z.im + eta ≠ 0 := by linarith
  obtain ⟨A, hA, hPinned⟩ :=
    exists_riemannXiSpectral_pinnedTaylor_radial_geometric_bound
  obtain ⟨C, hC, hfloor⟩ :=
    exists_riemannXiSpectral_quantitativeRadialBoundary_lower_bound
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  let P : ℕ → ℝ[X] := fun m =>
    finiteERootPinnedPolynomial
      (riemannXiSpectralRealTaylorPolynomial m) eta z
  let R : ℕ → ℝ := fun m => (m : ℝ)
  have hL : 0 < L := by
    simpa [L] using
      (finiteERootPinnedRadialConstant_pos (A := A) (eta := eta) (z := z))
  have hPspec :=
    riemannXiSpectralRealTaylorPinnedPolynomial_spec eta hroot hden
  obtain ⟨Braw, hBrawLimit, hBraw⟩ :=
    exists_separable_finiteERoot_polynomial_sequence_with_expanding_control
      P heta hz hPspec.1 hPspec.2 R (fun m => by simp [R])
  let index : ℕ → ℕ := radialRoucheIndex A L C
  let B : ℕ → ℝ[X] := fun n => Braw (index n)
  have hA0 : 0 ≤ A := hA.trans' zero_le_one
  have hIndex : Tendsto index atTop atTop := by
    simpa [index] using
      tendsto_radialRoucheIndex_atTop hA0 hL.le hC.le
  have hBlimit : TendstoLocallyUniformlyOn
      (fun n w => ((B n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ := by
    intro u hu x hx
    obtain ⟨t, ht, hevent⟩ := hBrawLimit u hu x hx
    refine ⟨t, ht, ?_⟩
    simpa [B, index] using hIndex.eventually hevent
  have hPdegree (m : ℕ) : (P m).natDegree ≤ max m 1 := by
    calc
      (P m).natDegree ≤
          max (riemannXiSpectralRealTaylorPolynomial m).natDegree 1 := by
        exact finiteERootPinnedPolynomial_natDegree_le _ _ _
      _ ≤ max m 1 := max_le_max
        (entireRealTaylorPolynomial_natDegree_le riemannXiSpectral m) le_rfl
  have hB (n : ℕ) : CanonicalFiniteHardyFrontier (B n) eta z ∧
      (B n).natDegree ≤ max (index n) 3 := by
    have hraw := hBraw (index n)
    constructor
    · exact canonicalFiniteHardyFrontier_of_finiteE_root
        hraw.1 heta hz hraw.2.1
    · calc
        (B n).natDegree ≤ max (P (index n)).natDegree 3 := hraw.2.2.1
        _ ≤ max (max (index n) 1) 3 :=
          max_le_max (hPdegree (index n)) le_rfl
        _ = max (index n) 3 := by omega
  refine ⟨eta, heta, z, hz, A, hA, C, hC, B, ?_⟩
  dsimp only
  refine ⟨by simpa [index, L] using hIndex,
    hBlimit, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [index, L] using hB n
  · intro n
    simpa [L] using
      radialRoucheIndex_cast_lt_exponential hA0 hL.le hC.le n
  · intro n w hw
    exact hfloor n hw
  · intro n w hw
    let N : ℕ := index n
    let F : ℝ := Real.exp
      (-C * Real.exp (5 * quantitativeSpectralRadialBoundary n))
    have hRadiusIndex :
        quantitativeSpectralRadialBoundary n ≤ (N : ℝ) := by
      simpa [N, index] using
        quantitativeSpectralRadialBoundary_le_radialRoucheIndex
          hA0 hL.le hC.le n
    have hwIndex : ‖w‖ ≤ R N := by
      simpa [R, hw] using hRadiusIndex
    have hPerturb :
        ‖((B n).map Complex.ofRealHom).eval w -
            ((P N).map Complex.ofRealHom).eval w‖ ≤
          Real.exp (-(N : ℝ)) / 2 := by
      simpa [B, N] using (hBraw N).2.2.2 w hwIndex
    have hPinned :
        ‖((P N).map Complex.ofRealHom).eval w -
            riemannXiSpectral w‖ ≤
          L * (quantitativeSpectralRadialBoundary n + 1) *
            Real.exp
              (A * (2 * quantitativeSpectralRadialBoundary n + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ N := by
      simpa [P, L] using
        hPinned hroot hden
          (quantitativeSpectralRadialBoundary_pos n) hw.le
    have hPinnedFloor :
        ‖((P N).map Complex.ofRealHom).eval w -
            riemannXiSpectral w‖ ≤ F * Real.exp (-2) := by
      exact hPinned.trans (by
        simpa [F, N, index] using
          radialRoucheIndex_pinned_geometric_bound A L C n)
    have hPerturbFloor :
        ‖((B n).map Complex.ofRealHom).eval w -
            ((P N).map Complex.ofRealHom).eval w‖ ≤
          (F * Real.exp (-2)) / 2 := by
      exact hPerturb.trans (by
        simpa [F, N, index] using
          radialRoucheIndex_separable_error_bound hA0 hL hC.le n)
    have hErrorFloor :
        ‖((B n).map Complex.ofRealHom).eval w -
            riemannXiSpectral w‖ < F := by
      have hF : 0 < F := by dsimp [F]; positivity
      have hslack : Real.exp (-2) / 2 + Real.exp (-2) < 1 := by
        linarith [exp_neg_two_lt_half]
      calc
        ‖((B n).map Complex.ofRealHom).eval w -
            riemannXiSpectral w‖ =
          ‖(((B n).map Complex.ofRealHom).eval w -
              ((P N).map Complex.ofRealHom).eval w) +
            (((P N).map Complex.ofRealHom).eval w -
              riemannXiSpectral w)‖ := by
          congr 1
          ring
        _ ≤ ‖((B n).map Complex.ofRealHom).eval w -
                ((P N).map Complex.ofRealHom).eval w‖ +
              ‖((P N).map Complex.ofRealHom).eval w -
                riemannXiSpectral w‖ := norm_add_le _ _
        _ ≤ (F * Real.exp (-2)) / 2 + F * Real.exp (-2) :=
          add_le_add hPerturbFloor hPinnedFloor
        _ = F * (Real.exp (-2) / 2 + Real.exp (-2)) := by ring
        _ < F * 1 := mul_lt_mul_of_pos_left hslack hF
        _ = F := by ring
    have hXiFloor : F ≤ ‖riemannXiSpectral w‖ := by
      simpa [F] using hfloor n hw
    exact ⟨by simpa [F] using hErrorFloor,
      hErrorFloor.trans_le hXiFloor⟩

end

end RiemannGaussian
