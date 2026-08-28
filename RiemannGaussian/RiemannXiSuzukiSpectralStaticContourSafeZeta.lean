import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourZetaReduction

/-!
# Uniform zeta bounds at the safe static-contour endpoint

The absolutely convergent Dirichlet series bounds zeta uniformly on
`Re s = 3/2`.  The equally absolutely convergent Möbius Dirichlet series,
together with the checked convolution identity, supplies the same bound for
the reciprocal.  This gives a height-independent bound on `|log |zeta||` and
proves that the safe endpoint contributes `o(T)`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped ArithmeticFunction.Moebius Classical ComplexConjugate ENNReal
  Interval LSeries.notation Topology

namespace RiemannGaussian

noncomputable section

/-- The positive Dirichlet-series mass at abscissa `3/2`. -/
def staticContourSafeZetaDirichletMass : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

/-- The safe-line Dirichlet mass is finite. -/
theorem summable_staticContourSafeZetaDirichletSeries :
    Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  exact Real.summable_nat_rpow_inv.mpr (by norm_num)

/-- The safe-line Dirichlet mass is at least one. -/
theorem one_le_staticContourSafeZetaDirichletMass :
    1 ≤ staticContourSafeZetaDirichletMass := by
  unfold staticContourSafeZetaDirichletMass
  have hone : (((1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ = 1 := by norm_num
  rw [← hone]
  apply summable_staticContourSafeZetaDirichletSeries.le_tsum 1
  intro n _hn
  positivity

/-- Every Riemann-zeta value on `Re s = 3/2` is bounded by the fixed
positive Dirichlet mass. -/
theorem norm_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖riemannZeta s‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum := summable_riemannZetaSummand hsOne
  rw [← tsum_riemannZetaSummand hsOne]
  calc
    ‖∑' n : ℕ, riemannZetaSummandHom
        (Complex.ne_zero_of_one_lt_re hsOne) n‖ ≤
        ∑' n : ℕ, ‖riemannZetaSummandHom
          (Complex.ne_zero_of_one_lt_re hsOne) n‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = staticContourSafeZetaDirichletMass := by
      unfold staticContourSafeZetaDirichletMass
      apply tsum_congr
      intro n
      simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk,
        ZeroHom.coe_mk]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
          (by rw [neg_re, hs]; norm_num),
        neg_re, hs, Real.rpow_neg (Nat.cast_nonneg n)]

/-- A Möbius Dirichlet summand on `Re s = 3/2` is bounded by the
corresponding positive zeta summand. -/
theorem norm_moebius_LSeries_term_safeLine_le
    {s : ℂ} (hs : s.re = 3 / 2) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦
        ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos hnpos, hs]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The Möbius L-series, hence the reciprocal of zeta, has the same uniform
safe-line bound. -/
theorem norm_moebius_LSeries_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖L (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
      staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum : LSeriesSummable
      (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsOne
  calc
    ‖L (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
        ∑' n : ℕ, ‖LSeries.term
          (fun m : ℕ ↦ ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      hsum.norm.tsum_le_tsum
        (norm_moebius_LSeries_term_safeLine_le hs)
        summable_staticContourSafeZetaDirichletSeries
    _ = staticContourSafeZetaDirichletMass := rfl

/-- The reciprocal zeta value on `Re s = 3/2` is bounded uniformly by the
same Dirichlet mass. -/
theorem norm_inv_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖(riemannZeta s)⁻¹‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsOne
  have hmul : riemannZeta s *
      L (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsOne]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hsOne
  have hinv : (riemannZeta s)⁻¹ =
      L (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
    apply mul_left_cancel₀ hzeta
    rw [mul_inv_cancel₀ hzeta, hmul]
  rw [hinv]
  exact norm_moebius_LSeries_safeLine_le_mass hs

/-- The logarithmic modulus of zeta is uniformly bounded on `Re s = 3/2`. -/
theorem abs_log_norm_riemannZeta_safeLine_le_log_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    |Real.log ‖riemannZeta s‖| ≤
      Real.log staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsOne
  have hnormPos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hzeta
  have hmassPos : 0 < staticContourSafeZetaDirichletMass :=
    one_pos.trans_le one_le_staticContourSafeZetaDirichletMass
  have hupper : Real.log ‖riemannZeta s‖ ≤
      Real.log staticContourSafeZetaDirichletMass :=
    Real.log_le_log hnormPos (norm_riemannZeta_safeLine_le_mass hs)
  have hlowerRaw : Real.log ‖(riemannZeta s)⁻¹‖ ≤
      Real.log staticContourSafeZetaDirichletMass := by
    apply Real.log_le_log
    · exact norm_pos_iff.mpr (inv_ne_zero hzeta)
    · exact norm_inv_riemannZeta_safeLine_le_mass hs
  have hlower : -Real.log staticContourSafeZetaDirichletMass ≤
      Real.log ‖riemannZeta s‖ := by
    rw [norm_inv, Real.log_inv] at hlowerRaw
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The safe zeta endpoint logarithm is `o(T)` on the quantitative contour
sequence. -/
theorem tendsto_log_norm_riemannZeta_safeEndpoint_div_quantitative_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log ‖riemannZeta
            (staticContourSafeEndpoint
              (quantitativeSpectralBoundaryTruncation n))‖ /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let M : ℝ := staticContourSafeZetaDirichletMass
  refine squeeze_zero_norm'
    (a := fun n : ℕ ↦ Real.log M / T n) ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      have hT : 0 < T n :=
        (Nat.cast_nonneg n).trans_lt
          (by simpa [T] using
            (quantitativeSpectralBoundaryTruncation_spec n).1)
      have hbound := abs_log_norm_riemannZeta_safeLine_le_log_mass
        (s := staticContourSafeEndpoint (T n))
        (by simp [staticContourSafeEndpoint])
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hT]
      exact div_le_div_of_nonneg_right (by simpa [M] using hbound) hT.le
  · exact tendsto_const_nhds.div_atTop
      tendsto_quantitativeSpectralBoundaryTruncation_atTop

/-- After the uniform safe-line estimate, the static vertical boundary is
asymptotic solely to the negative critical-line zeta logarithm.  The only
remaining endpoint estimate is therefore at `1/2 + I*T_n`. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_sub_criticalZeta_logNorm_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) -
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            Real.log ‖riemannZeta
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖ : ℝ) : ℂ))
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let S : ℕ → ℝ := fun n ↦
    Real.log ‖riemannZeta (staticContourSafeEndpoint (T n))‖
  let C : ℕ → ℝ := fun n ↦
    Real.log ‖riemannZeta (staticContourCriticalEndpoint (T n))‖
  let V : ℕ → ℂ := fun n ↦
    -Complex.I * xiSpectralBlaschkeSignedVerticalRemainderWindow
      (T n) 0 ((v : ℂ) * Complex.I)
  have hzeta : Tendsto
      (fun n : ℕ ↦ V n + (((4 / T n) * (S n - C n) : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa [T, S, C, V, staticContourZetaEndpointLogDifference] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_zeta_logNorm_main_quantitative_zero
        hv
  have hsafe : Tendsto (fun n : ℕ ↦ S n / T n) atTop (nhds 0) := by
    simpa [T, S] using
      tendsto_log_norm_riemannZeta_safeEndpoint_div_quantitative_zero
  have hsafeComplex : Tendsto
      (fun n : ℕ ↦ (((4 * (S n / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ ↦ 4 * (S n / T n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hsafe
    simpa using hreal.ofReal
  have hdifference : Tendsto
      (fun n : ℕ ↦
        V n + (((4 / T n) * (S n - C n) : ℝ) : ℂ) -
          (((4 * (S n / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    simpa using hzeta.sub hsafeComplex
  apply hdifference.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp [T, S, C, V]
    push_cast
    ring

end

end RiemannGaussian
