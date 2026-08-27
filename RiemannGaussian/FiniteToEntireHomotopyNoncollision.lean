import RiemannGaussian.FiniteToEntireHardyReductio
import RiemannGaussian.GaussianXiDivisorContour

/-!
# Noncolliding roots of the analytic homotopy

At a zero `a` of an analytic function with finite multiplicity `m`, its
logarithmic derivative has the local form

`f'/f = m/(z-a) + h(z)`.

The apparently singular root parameter `i f/f'` therefore has the removable
form

`i (z-a) / (m + (z-a) h(z))`.

This file proves that the latter function is analytic at `a`, has derivative
`i/m`, and is locally invertible.  A small positive real parameter then gives
an upper-half-plane root of `f + i eta f'` at which `f` itself is nonzero.
For spectral xi this strengthens the RH reductio entry point: failure of RH
can always be represented by a noncolliding positive-homotopy root.
-/

open Complex Filter Set Topology
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The removable form of `i f/f'` supplied by a logarithmic-derivative
principal part of multiplicity `m`. -/
def analyticERegularizedRootParameter
    (h : ℂ → ℂ) (m : ℕ) (a z : ℂ) : ℂ :=
  Complex.I * (z - a) /
    ((m : ℂ) + (z - a) * h z)

@[simp] theorem analyticERegularizedRootParameter_at_center
    (h : ℂ → ℂ) (m : ℕ) (a : ℂ) :
    analyticERegularizedRootParameter h m a a = 0 := by
  simp [analyticERegularizedRootParameter]

/-- The regularized root parameter is analytic at the divisor point. -/
theorem analyticERegularizedRootParameter_analyticAt
    {h : ℂ → ℂ} {m : ℕ} {a : ℂ}
    (hh : AnalyticAt ℂ h a) (hm : m ≠ 0) :
    AnalyticAt ℂ (analyticERegularizedRootParameter h m a) a := by
  have hlinear : AnalyticAt ℂ (fun z : ℂ ↦ z - a) a := by
    fun_prop
  have hnum : AnalyticAt ℂ
      (fun z : ℂ ↦ Complex.I * (z - a)) a :=
    analyticAt_const.mul hlinear
  have hden : AnalyticAt ℂ
      (fun z : ℂ ↦ (m : ℂ) + (z - a) * h z) a :=
    analyticAt_const.add (hlinear.mul hh)
  unfold analyticERegularizedRootParameter
  apply hnum.div hden
  simp [hm]

/-- Its derivative at the divisor point is `i/m`, hence nonzero for positive
multiplicity. -/
theorem analyticERegularizedRootParameter_hasDerivAt
    {h : ℂ → ℂ} {m : ℕ} {a : ℂ}
    (hh : AnalyticAt ℂ h a) (hm : m ≠ 0) :
    HasDerivAt (analyticERegularizedRootParameter h m a)
      (Complex.I / (m : ℂ)) a := by
  have hlinear : HasDerivAt (fun z : ℂ ↦ z - a) 1 a :=
    (hasDerivAt_id a).sub_const a
  have hhDeriv : HasDerivAt h (deriv h a) a :=
    hh.differentiableAt.hasDerivAt
  have hnum : HasDerivAt
      (fun z : ℂ ↦ Complex.I * (z - a)) Complex.I a := by
    simpa only [mul_one] using hlinear.const_mul Complex.I
  have hprod : HasDerivAt
      (fun z : ℂ ↦ (z - a) * h z)
      (1 * h a + (a - a) * deriv h a) a := by
    apply (hlinear.mul hhDeriv).congr_of_eventuallyEq
    exact Eventually.of_forall fun _ ↦ rfl
  have hden : HasDerivAt
      (fun z : ℂ ↦ (m : ℂ) + (z - a) * h z)
      (0 + (1 * h a + (a - a) * deriv h a)) a :=
    (hasDerivAt_const a (m : ℂ)).add
      hprod
  have hdenNe : (m : ℂ) + (a - a) * h a ≠ 0 := by
    simp [hm]
  have hquot := hnum.div hden hdenNe
  unfold analyticERegularizedRootParameter
  apply hquot.congr_deriv
  simp only [sub_self, mul_zero, add_zero, zero_mul, one_mul]
  field_simp [show (m : ℂ) ≠ 0 by exact_mod_cast hm]
  ring

/-- The regularized parameter admits a local inverse taking parameter zero
back to the divisor point. -/
theorem exists_analyticERegularizedRootParameter_germ
    {h : ℂ → ℂ} {m : ℕ} {a : ℂ}
    (hh : AnalyticAt ℂ h a) (hm : m ≠ 0) :
    ∃ rootCurve : ℂ → ℂ,
      Tendsto rootCurve (nhds 0) (nhds a) ∧
      ∀ᶠ eta in nhds 0,
        analyticERegularizedRootParameter h m a (rootCurve eta) = eta := by
  let p : ℂ → ℂ := analyticERegularizedRootParameter h m a
  have hpan : AnalyticAt ℂ p a :=
    analyticERegularizedRootParameter_analyticAt hh hm
  have hpderiv : deriv p a = Complex.I / (m : ℂ) :=
    (analyticERegularizedRootParameter_hasDerivAt hh hm).deriv
  have hpderivNe : deriv p a ≠ 0 := by
    rw [hpderiv]
    exact div_ne_zero Complex.I_ne_zero (by exact_mod_cast hm)
  have hpzero : p a = 0 :=
    analyticERegularizedRootParameter_at_center h m a
  let rootCurve : ℂ → ℂ :=
    hpan.hasStrictDerivAt.localInverse p (deriv p a) a hpderivNe
  have hcurve : Tendsto rootCurve (nhds 0) (nhds a) := by
    rw [← hpzero]
    exact HasStrictFDerivAt.localInverse_tendsto
      (hpan.hasStrictDerivAt.hasStrictFDerivAt_equiv hpderivNe)
  have hinverse : ∀ᶠ eta in nhds 0, p (rootCurve eta) = eta := by
    rw [← hpzero]
    exact hpan.hasStrictDerivAt.eventually_right_inverse hpderivNe
  exact ⟨rootCurve, hcurve, hinverse⟩

/-! ## From the regularized parameter to a genuine homotopy root -/

/-- At a punctured point where the logarithmic-derivative principal-part
identity holds, a nonzero real value of the regularized parameter gives an
exact root of `f + i eta f'`. -/
theorem analyticEValue_eq_zero_of_regularizedRootParameter_eq
    {f h : ℂ → ℂ} {m : ℕ} {a z : ℂ} {eta : ℝ}
    (hza : z ≠ a) (hfz : f z ≠ 0)
    (hlog : logDeriv f z = (m : ℂ) / (z - a) + h z)
    (hparam : analyticERegularizedRootParameter h m a z = (eta : ℂ))
    (heta : eta ≠ 0) :
    analyticEValue f eta z = 0 := by
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hden : (m : ℂ) + (z - a) * h z =
      (z - a) * logDeriv f z := by
    rw [hlog, mul_add]
    field_simp [hsub]
  rw [analyticERegularizedRootParameter, hden] at hparam
  have hetaComplex : (eta : ℂ) ≠ 0 := by
    exact_mod_cast heta
  have hlogNe : logDeriv f z ≠ 0 := by
    intro hzero
    apply hetaComplex
    symm
    simpa [hzero] using hparam
  have hdenNe : (z - a) * logDeriv f z ≠ 0 :=
    mul_ne_zero hsub hlogNe
  have hcross : Complex.I * (z - a) =
      (eta : ℂ) * ((z - a) * logDeriv f z) :=
    (div_eq_iff hdenNe).mp hparam
  have hetaLog : (eta : ℂ) * logDeriv f z = Complex.I := by
    apply mul_left_cancel₀ hsub
    calc
      (z - a) * ((eta : ℂ) * logDeriv f z) =
          (eta : ℂ) * ((z - a) * logDeriv f z) := by ring
      _ = Complex.I * (z - a) := hcross.symm
      _ = (z - a) * Complex.I := by ring
  have hetaDeriv : (eta : ℂ) * deriv f z = Complex.I * f z := by
    calc
      (eta : ℂ) * deriv f z =
          ((eta : ℂ) * (deriv f z / f z)) * f z := by
            field_simp [hfz]
      _ = ((eta : ℂ) * logDeriv f z) * f z := by rfl
      _ = Complex.I * f z := by rw [hetaLog]
  unfold analyticEValue
  calc
    f z + Complex.I * (eta : ℂ) * deriv f z =
        f z + Complex.I * ((eta : ℂ) * deriv f z) := by ring
    _ = f z + Complex.I * (Complex.I * f z) := by rw [hetaDeriv]
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

/-- A positive-multiplicity logarithmic-derivative principal part at an
upper point produces a nearby noncolliding root of a positive real analytic
homotopy. -/
theorem exists_positive_analyticEValue_upper_nonzero_root_of_logDeriv_principalPart
    {f h : ℂ → ℂ} {m : ℕ} {a : ℂ}
    (ha : 0 < a.im) (hm : m ≠ 0)
    (hh : AnalyticAt ℂ h a)
    (hlog : logDeriv f =ᶠ[nhdsWithin a ({a}ᶜ)]
      fun z ↦ (m : ℂ) / (z - a) + h z)
    (hfne : ∀ᶠ z in nhdsWithin a ({a}ᶜ), f z ≠ 0) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ,
      0 < z.im ∧ analyticEValue f eta z = 0 ∧ f z ≠ 0 := by
  obtain ⟨rootCurve, hcurve, hinverse⟩ :=
    exists_analyticERegularizedRootParameter_germ hh hm
  have hupper : ∀ᶠ e in nhds (0 : ℂ), 0 < (rootCurve e).im :=
    hcurve.eventually
      (Complex.continuous_im.continuousAt.eventually (lt_mem_nhds ha))
  have hlog' : ∀ᶠ z in nhds a, z ≠ a →
      logDeriv f z = (m : ℂ) / (z - a) + h z := by
    have hlogEvent : ∀ᶠ z in nhdsWithin a ({a}ᶜ),
        logDeriv f z = (m : ℂ) / (z - a) + h z := hlog
    rw [eventually_nhdsWithin_iff] at hlogEvent
    exact hlogEvent
  have hfne' : ∀ᶠ z in nhds a, z ≠ a → f z ≠ 0 := by
    rw [eventually_nhdsWithin_iff] at hfne
    exact hfne
  have hcurveLog : ∀ᶠ e in nhds (0 : ℂ),
      rootCurve e ≠ a →
        logDeriv f (rootCurve e) =
          (m : ℂ) / (rootCurve e - a) + h (rootCurve e) :=
    hcurve.eventually hlog'
  have hcurveFne : ∀ᶠ e in nhds (0 : ℂ),
      rootCurve e ≠ a → f (rootCurve e) ≠ 0 :=
    hcurve.eventually hfne'
  have hgood := hinverse.and
    (hupper.and (hcurveLog.and hcurveFne))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  let eta : ℝ := r / 2
  have heta : 0 < eta := half_pos hr
  have hdist : dist (eta : ℂ) 0 < r := by
    simpa [eta, abs_of_pos hr] using half_lt_self hr
  have hdata := hball hdist
  let z : ℂ := rootCurve (eta : ℂ)
  have hetaNe : eta ≠ 0 := heta.ne'
  have hzNe : z ≠ a := by
    intro hza
    have hpzero := analyticERegularizedRootParameter_at_center h m a
    have hparam := hdata.1
    change analyticERegularizedRootParameter h m a z = (eta : ℂ) at hparam
    rw [hza, hpzero] at hparam
    have hetaComplex : (eta : ℂ) ≠ 0 := by
      exact_mod_cast hetaNe
    exact hetaComplex hparam.symm
  have hzLog : logDeriv f z = (m : ℂ) / (z - a) + h z :=
    hdata.2.2.1 hzNe
  have hfz : f z ≠ 0 := hdata.2.2.2 hzNe
  refine ⟨eta, heta, z, hdata.2.1, ?_, hfz⟩
  apply analyticEValue_eq_zero_of_regularizedRootParameter_eq
    hzNe hfz hzLog
  · exact hdata.1
  · exact hetaNe

/-! ## Spectral-xi specialization -/

/-- Failure of RH supplies a positive real homotopy root in the upper half
plane which is not itself a spectral-xi zero.  This removes the collision
choice made by the earlier simple/multiple-root split. -/
theorem exists_positive_riemannXiSpectral_analyticEValue_upper_nonzero_root_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ,
      0 < z.im ∧ analyticEValue riemannXiSpectral eta z = 0 ∧
        riemannXiSpectral z ≠ 0 := by
  obtain ⟨a, haZero, haUpper⟩ :=
    exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
  obtain ⟨rho, rfl⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero a).mp haZero
  obtain ⟨h, hh, hlog⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic rho
  have hm : analyticZetaZeroMultiplicity rho ≠ 0 :=
    (analyticZetaZeroMultiplicity_positive rho).ne'
  have hfinite : analyticOrderAt riemannXiSpectral
      (zetaSpectralCoordinate rho.1) ≠ ⊤ := by
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hfne : ∀ᶠ z in nhdsWithin
      (zetaSpectralCoordinate rho.1) ({zetaSpectralCoordinate rho.1}ᶜ),
      riemannXiSpectral z ≠ 0 :=
    (analyticAt_riemannXiSpectral
      (zetaSpectralCoordinate rho.1)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        fun hzero ↦ hfinite (analyticOrderAt_eq_top.mpr hzero)
  exact
    exists_positive_analyticEValue_upper_nonzero_root_of_logDeriv_principalPart
      haUpper hm hh hlog hfne

end

end RiemannGaussian
