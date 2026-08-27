import RiemannGaussian.FiniteToEntireGaussianTail

/-!
# Degree control for the root-pinned xi approximants

The quantitative Gaussian tail bound depends on the number of polynomial
roots, hence on polynomial degree.  This file tracks degree through every
step of the actual approximation construction: Taylor truncation, affine root
pinning, conditional cubic lifting, and the separable quadratic perturbation.

The resulting separable, root-pinned spectral-xi approximants have degree at
most `max n 3` at index `n`.  Consequently the explicit Gaussian envelope
vanishes at every fixed positive proper time if unused roots are separated
from the observation point by `sqrt n`.  The final theorem proves remainder
vanishing from precisely that separation hypothesis; establishing it for an
expanding family of genuine xi clusters is the remaining localization task.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The first `N` formal-series terms produce a polynomial of degree at most
`N`, including when leading coefficients vanish. -/
theorem realFormalPowerSeriesPartialPolynomial_natDegree_le
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) :
    (realFormalPowerSeriesPartialPolynomial p N).natDegree ≤ N := by
  rw [realFormalPowerSeriesPartialPolynomial]
  apply natDegree_sum_le_of_forall_le
  intro k hk
  calc
    (C (p.coeff k).re * X ^ k : ℝ[X]).natDegree ≤
        (X ^ k : ℝ[X]).natDegree := natDegree_C_mul_le _ _
    _ = k := natDegree_X_pow k
    _ ≤ N := (Finset.mem_range.mp hk).le

/-- The `N`th entire real Taylor polynomial has degree at most `N`. -/
theorem entireRealTaylorPolynomial_natDegree_le
    (f : ℂ → ℂ) (N : ℕ) :
    (entireRealTaylorPolynomial f N).natDegree ≤ N := by
  exact realFormalPowerSeriesPartialPolynomial_natDegree_le _ _

/-- The affine root-pinning correction raises degree to at most one. -/
theorem finiteERootPinnedPolynomial_natDegree_le
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    (finiteERootPinnedPolynomial A eta z).natDegree ≤
      max A.natDegree 1 := by
  unfold finiteERootPinnedPolynomial
  calc
    (A + C (finiteERootPinIntercept A eta z) +
          C (finiteERootPinSlope A eta z) * X).natDegree ≤
        max (A + C (finiteERootPinIntercept A eta z)).natDegree
          (C (finiteERootPinSlope A eta z) * X).natDegree :=
      natDegree_add_le _ _
    _ ≤ max (max A.natDegree 0) 1 := by
      apply max_le_max
      · exact (natDegree_add_le _ _).trans
          (max_le_max le_rfl (by simp))
      · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    _ = max A.natDegree 1 := by omega

/-- Conditional cubic lifting raises degree to at most three. -/
theorem finiteERootDegreeLift_natDegree_le
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) (r : ℝ) :
    (finiteERootDegreeLift A eta z r).natDegree ≤
      max A.natDegree 3 := by
  rw [finiteERootDegreeLift]
  split_ifs
  · exact (natDegree_add_le _ _).trans <|
      max_le_max le_rfl <|
        (natDegree_C_mul_le _ _).trans <|
          (finiteERootKernelCubic_natDegree eta z).le
  · exact le_max_left _ _

/-- Adding a scalar multiple of the quadratic homotopy kernel raises degree
to at most two. -/
theorem add_C_mul_finiteERootKernelQuadratic_natDegree_le
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) (t : ℝ) :
    (A + C t * finiteERootKernelQuadratic eta z).natDegree ≤
      max A.natDegree 2 := by
  exact (natDegree_add_le _ _).trans <|
    max_le_max le_rfl <|
      (natDegree_C_mul_le _ _).trans <|
        (finiteERootKernelQuadratic_natDegree eta z).le

/-- The constrained separability construction can be performed while
retaining an explicit degree bound at every index. -/
theorem exists_separable_finiteERoot_polynomial_sequence_with_natDegree_le
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ} {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hroot : ∀ n, (finiteEPolynomial (A n) eta).eval z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max (A n).natDegree 3 := by
  have hzeta : z.im + eta ≠ 0 := by linarith
  let r : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  let D : ℕ → ℝ[X] := fun n ↦
    finiteERootDegreeLift (A n) eta z (r n)
  have hr : Tendsto r atTop (nhds 0) := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp only [r]
    positivity
  have hDlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((D n).map Complex.ofRealHom).eval w)
      f atTop Set.univ := by
    exact finiteERootDegreeLift_tendstoLocallyUniformlyOn
      A eta z r hA hr
  have hDdegree (n : ℕ) : 2 < (D n).natDegree := by
    exact finiteERootDegreeLift_natDegree_gt_two eta z
      (ne_of_gt (hrpos n))
  have hDdegreeUpper (n : ℕ) :
      (D n).natDegree ≤ max (A n).natDegree 3 := by
    exact finiteERootDegreeLift_natDegree_le (A n) eta z (r n)
  have hDroot (n : ℕ) :
      (finiteEPolynomial (D n) eta).eval z = 0 := by
    exact finiteERootDegreeLift_isRoot (hroot n) hzeta (r n)
  have hexists (n : ℕ) :
      ∃ t : ℝ, 0 < t ∧ t < r n ∧
        (D n + C t * finiteERootKernelQuadratic eta z).Separable ∧
        (finiteEPolynomial
          (D n + C t * finiteERootKernelQuadratic eta z) eta).eval z = 0 :=
    exists_separable_finiteERootKernelQuadratic_perturbation
      heta hz (hDdegree n) (hDroot n) (hrpos n)
  choose t htpos htbound htsep htroot using hexists
  let B : ℕ → ℝ[X] := fun n ↦
    D n + C (t n) * finiteERootKernelQuadratic eta z
  have ht : Tendsto t atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n ↦ (htpos n).le
    · exact fun n ↦ (htbound n).le
    · exact hr
  refine ⟨B, ?_, ?_⟩
  · exact add_C_mul_fixedPolynomial_tendstoLocallyUniformlyOn
      D (finiteERootKernelQuadratic eta z) t hDlimit ht
  · intro n
    refine ⟨htsep n, htroot n, ?_⟩
    calc
      (B n).natDegree ≤ max (D n).natDegree 2 := by
        exact add_C_mul_finiteERootKernelQuadratic_natDegree_le
          (D n) eta z (t n)
      _ = (D n).natDegree := max_eq_left (hDdegree n).le
      _ ≤ max (A n).natDegree 3 := hDdegreeUpper n

/-- Spectral-xi specialization: the actual separable root-pinned
approximants can be chosen with degree at most `max n 3` at index `n`. -/
theorem exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence_with_natDegree_le
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hroot : analyticEValue riemannXiSpectral eta z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max n 3 := by
  let A : ℕ → ℝ[X] := fun n ↦
    finiteERootPinnedPolynomial
      (riemannXiSpectralRealTaylorPolynomial n) eta z
  have hzeta : z.im + eta ≠ 0 := by linarith
  have hspec :=
    riemannXiSpectralRealTaylorPinnedPolynomial_spec eta hroot hzeta
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_separable_finiteERoot_polynomial_sequence_with_natDegree_le
      A heta hz hspec.1 hspec.2
  refine ⟨B, hBlimit, ?_⟩
  intro n
  obtain ⟨hBsep, hBroot, hBdegree⟩ := hB n
  refine ⟨hBsep, hBroot, hBdegree.trans ?_⟩
  have hAdegree : (A n).natDegree ≤ max n 1 := by
    calc
      (A n).natDegree ≤
          max (riemannXiSpectralRealTaylorPolynomial n).natDegree 1 :=
        finiteERootPinnedPolynomial_natDegree_le _ _ _
      _ ≤ max n 1 := max_le_max
        (entireRealTaylorPolynomial_natDegree_le riemannXiSpectral n) le_rfl
  calc
    max (A n).natDegree 3 ≤ max (max n 1) 3 :=
      max_le_max hAdegree le_rfl
    _ = max n 3 := by omega

/-- A known degree majorant may replace the polynomial's literal degree in
the radial Gaussian heat-tail bound. -/
theorem realPolynomialUpperHeatTailOutsideClosedBall_le_of_natDegree_le
    {A : ℝ[X]} {d : ℕ} (hdegree : A.natDegree ≤ d)
    (z : ℂ) {R tau : ℝ} (hR : 0 ≤ R) (htau : 0 < tau) :
    realPolynomialUpperHeatTailOutsideClosedBall A z R tau ≤
      (d : ℝ) * (tau⁻¹ * Real.exp (-(R ^ 2 * tau))) := by
  have hC : 0 ≤ tau⁻¹ * Real.exp (-(R ^ 2 * tau)) :=
    mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le
  exact
    (realPolynomialUpperHeatTailOutsideClosedBall_le_degreeGaussian
      A z hR htau).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hC)

/-- For a linearly degree-controlled sequence, the exact remainder vanishes
whenever its chosen radial Gaussian envelope does. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideBalls_zero_of_indexGaussian
    {iota : Type*} [Fintype iota] (B : ℕ → ℝ[X])
    (hdegree : ∀ n, (B n).natDegree ≤ max n 3)
    (a : ℕ → iota → ℂ) (r : ℕ → iota → ℝ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hdist : ∀ᶠ n in atTop, ∀ alpha ∈
      realPolynomialUpperRootMultiset (B n) -
        ∑ i : iota,
          realPolynomialRootMultisetInBall (B n) (a n i) (r n i),
      R n ≤ dist z alpha)
    (henvelope : Tendsto
      (fun n ↦ ((max n 3 : ℕ) : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideBalls
        (B n) (a n) (r n) z tau)
      atTop (nhds 0) := by
  apply
    tendsto_realPolynomialUpperHeatRemainderOutsideBalls_zero_of_degreeGaussian
      B a r hz htau R hR hdist
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((B n).natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) := by
    filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le)
  have hle : ∀ᶠ n : ℕ in atTop,
      ((B n).natDegree : ℝ) *
          (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) ≤
        ((max n 3 : ℕ) : ℝ) *
          (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) := by
    filter_upwards with n
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hdegree n
    · exact mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le
  exact squeeze_zero' hnonneg hle henvelope

/-- For a linearly degree-controlled sequence and arbitrarily varying
selected root multisets, complement heat vanishes whenever the index-based
Gaussian envelope does. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_indexGaussian
    (B : ℕ → ℝ[X])
    (hdegree : ∀ n, (B n).natDegree ≤ max n 3)
    (selected : ℕ → Multiset ℂ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hdist : ∀ᶠ n in atTop, ∀ alpha ∈
      realPolynomialUpperRootMultiset (B n) - selected n,
      R n ≤ dist z alpha)
    (henvelope : Tendsto
      (fun n ↦ ((max n 3 : ℕ) : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (selected n) z tau)
      atTop (nhds 0) := by
  apply
    tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_degreeGaussian
      B selected hz htau R hR hdist
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((B n).natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) := by
    filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le)
  have hle : ∀ᶠ n : ℕ in atTop,
      ((B n).natDegree : ℝ) *
          (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) ≤
        ((max n 3 : ℕ) : ℝ) *
          (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))) := by
    filter_upwards with n
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hdegree n
    · exact mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le
  exact squeeze_zero' hnonneg hle henvelope

/-- At every positive proper time, a linear degree factor times the Gaussian
at radius `sqrt n` tends to zero. -/
theorem tendsto_indexGaussian_sqrt
    {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ ↦ ((max n 3 : ℕ) : ℝ) *
        (tau⁻¹ * Real.exp
          (-((Real.sqrt (n : ℝ)) ^ 2 * tau))))
      atTop (nhds 0) := by
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) tau htau).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlinear : Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        (tau⁻¹ * Real.exp (-((n : ℝ) * tau))))
      atTop (nhds 0) := by
    simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm] using
      hbase.const_mul tau⁻¹
  apply hlinear.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [max_eq_left hn]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- For a linearly degree-controlled sequence and arbitrarily varying
selected root multisets, separation of every unused root by `sqrt n` is
sufficient for the exact complement heat to vanish. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_sqrtIndexSeparation
    (B : ℕ → ℝ[X])
    (hdegree : ∀ n, (B n).natDegree ≤ max n 3)
    (selected : ℕ → Multiset ℂ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (hdist : ∀ᶠ n in atTop, ∀ alpha ∈
      realPolynomialUpperRootMultiset (B n) - selected n,
      Real.sqrt (n : ℝ) ≤ dist z alpha) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (selected n) z tau)
      atTop (nhds 0) := by
  apply
    tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_indexGaussian
      B hdegree selected hz htau (fun n ↦ Real.sqrt (n : ℝ))
  · filter_upwards with n
    exact Real.sqrt_nonneg _
  · exact hdist
  · exact tendsto_indexGaussian_sqrt htau

/-- For a linearly degree-controlled sequence, radial separation of every
unused root by `sqrt n` is sufficient for the exact heat remainder to
vanish. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideBalls_zero_of_sqrtIndexSeparation
    {iota : Type*} [Fintype iota] (B : ℕ → ℝ[X])
    (hdegree : ∀ n, (B n).natDegree ≤ max n 3)
    (a : ℕ → iota → ℂ) (r : ℕ → iota → ℝ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (hdist : ∀ᶠ n in atTop, ∀ alpha ∈
      realPolynomialUpperRootMultiset (B n) -
        ∑ i : iota,
          realPolynomialRootMultisetInBall (B n) (a n i) (r n i),
      Real.sqrt (n : ℝ) ≤ dist z alpha) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideBalls
        (B n) (a n) (r n) z tau)
      atTop (nhds 0) := by
  apply tendsto_realPolynomialUpperHeatRemainderOutsideBalls_zero_of_indexGaussian
    B hdegree a r hz htau (fun n ↦ Real.sqrt (n : ℝ))
  · filter_upwards with n
    exact Real.sqrt_nonneg _
  · exact hdist
  · exact tendsto_indexGaussian_sqrt htau

/-- The complete canonical finite Hardy frontier can be carried by the same
spectral-xi approximants that satisfy the linear degree bound. -/
theorem exists_degreeControlled_riemannXiSpectral_canonicalFiniteHardyFrontier_sequence
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hroot : analyticEValue riemannXiSpectral eta z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      ∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
        (B n).natDegree ≤ max n 3 := by
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence_with_natDegree_le
      heta hz hroot
  refine ⟨B, hBlimit, ?_⟩
  intro n
  exact ⟨canonicalFiniteHardyFrontier_of_finiteE_root
    (hB n).1 heta hz (hB n).2.1, (hB n).2.2⟩

/-- If RH fails, the entire canonical finite Hardy reductio sequence may be
chosen with the explicit degree bound `natDegree (B n) ≤ max n 3`. -/
theorem exists_degreeControlled_canonicalFiniteHardyFrontier_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        ∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
          (B n).natDegree ≤ max n 3 := by
  obtain ⟨eta, heta, z, hz, hroot⟩ :=
    exists_positive_riemannXiSpectral_analyticEValue_upper_root_of_not_rh hRH
  obtain ⟨B, hBlimit, hB⟩ :=
    exists_degreeControlled_riemannXiSpectral_canonicalFiniteHardyFrontier_sequence
      heta hz hroot
  exact ⟨eta, heta, z, hz, B, hBlimit, hB⟩

end

end RiemannGaussian
