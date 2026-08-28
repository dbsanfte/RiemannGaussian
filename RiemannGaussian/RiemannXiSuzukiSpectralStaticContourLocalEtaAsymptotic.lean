import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaProduct
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaLowerNearLinear

/-!
# Sublinear negative logarithm of paired eta on the selected heights

The exact local canonical-product estimate contains one remaining
height-dependent input: the logarithm of the reciprocal quantitative
separation radius.  The already-proved log-linear growth theorem for xi bounds
that reciprocal by a polynomial in the height.  Consequently the local
factor logarithm is `O(log T)`.

This module makes that domination explicit, expands the resulting local eta
majorant into constant, logarithmic, and squared-logarithmic terms, and proves
that the majorant divided by the selected height tends to zero.  A squeeze
then establishes that the negative part of the critical paired-eta logarithm
is `o(T)`.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Log-linear xi growth supplies a fixed constant bounding every local
canonical-factor logarithm by a constant plus twice the logarithm of height. -/
theorem exists_staticContourLocalEtaCanonicalFactorLogMajorant_le_log :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ n : ℕ,
      staticContourLocalEtaCanonicalFactorLogMajorant n ≤
        Real.log D +
          2 * Real.log (quantitativeSpectralBoundaryTruncation n + 4) := by
  rcases riemannXi_logLinearGrowth with ⟨A, hA, hxi⟩
  let K : ℝ := 18 * A / Real.log 2 + 12
  let D : ℝ := 1 + (9 / 4 : ℝ) * K
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA0 : 0 ≤ A := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith
  refine ⟨D, hD, fun n => ?_⟩
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let X : ℝ := T + 4
  let u : ℝ := 2 * ((n : ℝ) + 2) + 1
  let delta : ℝ := spectralBoundarySeparation n
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hnT : (n : ℝ) < T := by
    simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huTwo : u ≤ 2 * X := by
    dsimp [u, X]
    linarith
  have huThree : u + 1 ≤ 3 * X := by
    dsimp [u, X]
    linarith
  have hscale := xiLogLinearScale_le_mul_one_add_log_mul
    (u := u) (k := 2) (c := 3) (X := X)
    hu (by norm_num) (by norm_num) hXpos huTwo huThree
  have hlog3 : Real.log 3 ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num
  have hlogX : Real.log X ≤ X - 1 :=
    Real.log_le_sub_one_of_pos hXpos
  have hparenthesis : 1 + Real.log 3 + Real.log X ≤ 3 * X := by
    linarith
  have hscaleSix : xiLogLinearScale u ≤ 6 * X ^ 2 := by
    calc
      xiLogLinearScale u ≤
          2 * X * (1 + Real.log 3 + Real.log X) := hscale
      _ ≤ 2 * X * (3 * X) :=
        mul_le_mul_of_nonneg_left hparenthesis (by positivity)
      _ = 6 * X ^ 2 := by ring
  have hdelta : 0 < delta := by
    simpa [delta] using spectralBoundarySeparation_pos n
  have hsepRaw := one_div_spectralBoundarySeparation_le_logLinear_of_growth
    hA hxi n
  have hsep : 1 / delta ≤ K * X ^ 2 := by
    calc
      1 / delta ≤
          3 * (A * xiLogLinearScale u / Real.log 2 + 4) := by
        simpa [delta, u] using hsepRaw
      _ ≤ 3 * (A * (6 * X ^ 2) / Real.log 2 + 4) := by
        gcongr
      _ ≤ K * X ^ 2 := by
        have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hX
        calc
          3 * (A * (6 * X ^ 2) / Real.log 2 + 4) =
              (18 * A / Real.log 2) * X ^ 2 + 12 := by ring
          _ ≤ (18 * A / Real.log 2) * X ^ 2 + 12 * X ^ 2 := by
            have h12 : (12 : ℝ) ≤ 12 * X ^ 2 :=
              by nlinarith
            linarith
          _ = K * X ^ 2 := by dsimp [K]; ring
  have hquot :
      (9 / 4 : ℝ) / delta ≤ (9 / 4 : ℝ) * K * X ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      (9 / 4 : ℝ) * delta⁻¹ ≤ (9 / 4 : ℝ) * (K * X ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa [one_div] using hsep)
          (show 0 ≤ (9 / 4 : ℝ) by norm_num)
      _ = (9 / 4 : ℝ) * K * X ^ 2 := by ring
  have hargument :
      1 + (9 / 4 : ℝ) / delta ≤ D * X ^ 2 := by
    have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hX
    dsimp [D]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hXsq)]
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  calc
    staticContourLocalEtaCanonicalFactorLogMajorant n =
        Real.log (1 + (9 / 4 : ℝ) / delta) := by
      rfl
    _ ≤ Real.log (D * X ^ 2) := by
      apply Real.log_le_log
      · have hquotPos : 0 < (9 / 4 : ℝ) / delta :=
          div_pos (by norm_num) hdelta
        linarith
      · exact hargument
    _ = Real.log D + 2 * Real.log X := by
      rw [Real.log_mul hDpos.ne' (pow_ne_zero 2 hXpos.ne'),
        Real.log_pow]
      norm_num
    _ = Real.log D +
        2 * Real.log (quantitativeSpectralBoundaryTruncation n + 4) := by
      rfl

/-- A nonnegative explicit majorant for the negative paired-eta logarithm. -/
def staticContourLocalEtaCriticalNegativeLogMajorant
    (D : ℝ) (n : ℕ) : ℝ :=
  max 0
      (-Real.log
        (staticContourSafeEtaFactorFloor /
          staticContourSafeZetaDirichletMass)) +
    32 * staticContourLocalEtaCanonicalLogMajorant n +
    staticContourLocalEtaCanonicalCountMajorant n *
      (Real.log D +
        2 * Real.log (quantitativeSpectralBoundaryTruncation n + 4))

lemma staticContourLocalEtaCriticalNegativeLogMajorant_nonneg
    {D : ℝ} (hD : 1 ≤ D) (n : ℕ) :
    0 ≤ staticContourLocalEtaCriticalNegativeLogMajorant D n := by
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
    (Nat.cast_nonneg n).trans_lt
      (quantitativeSpectralBoundaryTruncation_spec n).1
  have hlogT : 0 ≤
      Real.log (quantitativeSpectralBoundaryTruncation n + 4) :=
    Real.log_nonneg (by linarith)
  have hM : 0 ≤ staticContourLocalEtaCanonicalLogMajorant n :=
    (staticContourLocalEtaCanonicalLogMajorant_pos n).le
  have hB : 0 ≤ staticContourLocalEtaCanonicalCountMajorant n :=
    staticContourLocalEtaCanonicalCountMajorant_nonneg n
  have hfactor : 0 ≤ Real.log D +
      2 * Real.log (quantitativeSpectralBoundaryTruncation n + 4) := by
    positivity
  unfold staticContourLocalEtaCriticalNegativeLogMajorant
  exact add_nonneg
    (add_nonneg (le_max_left _ _) (mul_nonneg (by norm_num) hM))
    (mul_nonneg hB hfactor)

/-- For every fixed positive `D`, the explicit constant/log/log-squared eta
majorant is sublinear in the selected height. -/
theorem tendsto_staticContourLocalEtaCriticalNegativeLogMajorant_div_zero
    (D : ℝ) :
    Tendsto
      (fun n : ℕ =>
        staticContourLocalEtaCriticalNegativeLogMajorant D n /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let X : ℕ → ℝ := fun n => T n + 4
  let c : ℝ := staticContourSafeEtaFactorFloor /
    staticContourSafeZetaDirichletMass
  let a : ℝ := Real.log staticContourLocalEtaJensenConstant
  let q : ℝ := Real.log (10 / 9 : ℝ)
  let d : ℝ := Real.log D
  let k : ℝ := max 0 (-Real.log c)
  let P₀ : ℝ := k + 32 * a + a * d / q
  let P₁ : ℝ := 32 + (2 * a + d) / q
  let P₂ : ℝ := 2 / q
  have hT : Tendsto T atTop atTop :=
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hX : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 hT
  have hTpos (n : ℕ) : 0 < T n :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hXpos (n : ℕ) : 0 < X n := by
    dsimp [X]
    linarith [hTpos n]
  have hq : 0 < q := by
    dsimp [q]
    exact Real.log_pos (by norm_num)
  have hone : Tendsto (fun n : ℕ => 1 / T n) atTop (nhds 0) := by
    simpa only [one_div] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div_atTop hT)
  have hlog : Tendsto
      (fun n : ℕ => Real.log (X n) / T n) atTop (nhds 0) := by
    have hraw :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 1 one_ne_zero).comp hX
    refine hraw.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    dsimp [X, T]
    ring
  have hlogSq : Tendsto
      (fun n : ℕ => Real.log (X n) ^ 2 / T n) atTop (nhds 0) := by
    have hraw :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 2 one_ne_zero).comp hX
    refine hraw.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, one_mul]
    congr 1
    dsimp [X, T]
    ring
  have hcombined : Tendsto
      (fun n : ℕ =>
        P₀ * (1 / T n) +
          P₁ * (Real.log (X n) / T n) +
          P₂ * (Real.log (X n) ^ 2 / T n))
      atTop (nhds 0) := by
    have hzero : Tendsto (fun n : ℕ => P₀ * (1 / T n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hone
    have hlinear : Tendsto
        (fun n : ℕ => P₁ * (Real.log (X n) / T n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hlog
    have hquadratic : Tendsto
        (fun n : ℕ => P₂ * (Real.log (X n) ^ 2 / T n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hlogSq
    simpa using (hzero.add hlinear).add hquadratic
  refine hcombined.congr' (Eventually.of_forall fun n => ?_)
  have hC : 0 < staticContourLocalEtaJensenConstant :=
    staticContourLocalEtaJensenConstant_pos
  have hlogProduct :
      staticContourLocalEtaCanonicalLogMajorant n =
        a + Real.log (X n) := by
    unfold staticContourLocalEtaCanonicalLogMajorant
    rw [Real.log_mul hC.ne' (hXpos n).ne']
  change
    P₀ * (1 / T n) +
        P₁ * (Real.log (X n) / T n) +
          P₂ * (Real.log (X n) ^ 2 / T n) =
      staticContourLocalEtaCriticalNegativeLogMajorant D n / T n
  unfold staticContourLocalEtaCriticalNegativeLogMajorant
    staticContourLocalEtaCanonicalCountMajorant
  rw [hlogProduct]
  dsimp [c, a, q, d, k,
    P₀, P₁, P₂, X, T]
  field_simp [hq.ne', (hTpos n).ne']
  ring

/-- The negative part of the critical paired-eta logarithm is `o(T)` along
the quantitative contour heights. -/
theorem tendsto_pairedEtaCore_critical_log_negativePart_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        max 0
            (-Real.log
              ‖pairedEtaCore
                (staticContourCriticalEndpoint
                  (quantitativeSpectralBoundaryTruncation n))‖) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  rcases exists_staticContourLocalEtaCanonicalFactorLogMajorant_le_log with
    ⟨D, hD, hfactor⟩
  let P : ℕ → ℝ := fun n =>
    staticContourLocalEtaCriticalNegativeLogMajorant D n
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by
      have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
        (Nat.cast_nonneg n).trans_lt
          (quantitativeSpectralBoundaryTruncation_spec n).1
      exact div_nonneg (le_max_left _ _) hT.le
  · filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
    have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
      (Nat.cast_nonneg n).trans_lt
        (quantitativeSpectralBoundaryTruncation_spec n).1
    have heta := neg_log_norm_pairedEtaCore_critical_quantitative_le n hn
    have hB : 0 ≤ staticContourLocalEtaCanonicalCountMajorant n :=
      staticContourLocalEtaCanonicalCountMajorant_nonneg n
    have hfactorProduct := mul_le_mul_of_nonneg_left (hfactor n) hB
    have hraw :
        -Real.log
            ‖pairedEtaCore
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖ ≤ P n := by
      dsimp [P, staticContourLocalEtaCriticalNegativeLogMajorant]
      linarith [le_max_right 0
        (-Real.log
          (staticContourSafeEtaFactorFloor /
            staticContourSafeZetaDirichletMass))]
    have hP : 0 ≤ P n := by
      dsimp [P]
      exact staticContourLocalEtaCriticalNegativeLogMajorant_nonneg hD n
    have hmax :
        max 0
            (-Real.log
              ‖pairedEtaCore
                (staticContourCriticalEndpoint
                  (quantitativeSpectralBoundaryTruncation n))‖) ≤ P n :=
      max_le hP hraw
    exact div_le_div_of_nonneg_right hmax hT.le
  · simpa [P] using
      tendsto_staticContourLocalEtaCriticalNegativeLogMajorant_div_zero
        D

end

end RiemannGaussian
