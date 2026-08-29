import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripXiScalar

/-!
# Xi log-norm gradient form of the selected heat frontier

Let `U(a,y) = log |xi(1 / 2 + a + I*y)|`. Away from the xi divisor,
this module proves that the two coordinate derivatives of `U` are
`Re (xi'/xi)` and `-Im (xi'/xi)`. Combined with the checked heat-kernel
partial derivatives, the explicit real Cauchy--Green source becomes exactly
the Euclidean first-order pairing `grad K dot grad U`.

The selected planar rectangles do cross xi zeros. The integral theorem does
not ignore this: their bounded-height divisor is contained in an explicit
finite zero window, hence is null for planar Lebesgue measure. The pointwise
off-divisor identity is promoted to an almost-everywhere equality, proving
integrability of the gradient expression and equality of the ordinary planar
integrals. The selected vertical sides are genuinely zero-free, so their
boundary terms become the corresponding horizontal derivative of `U`.

Consequently the complete real frontier is exactly a boundary-minus-gradient
functional and retains the unnormalized limit to the nonnegative RH detector.
No integration-by-parts or unconditional vanishing estimate is asserted here;
the divisor-aware Green/Dirichlet rigidity step remains open.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The logarithmic modulus potential
`U(a,y) = log |xi(1 / 2 + a + I*y)|` in shifted coordinates. -/
def shiftedRiemannXiLogNorm (a y : ℝ) : ℝ :=
  Real.log ‖riemannXi (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖

/-- If a complex-valued real curve has derivative `D * g(x)` and is nonzero
at `x`, then the derivative of its logarithmic modulus is `Re D`. -/
theorem hasDerivAt_log_norm_of_hasDerivAt_mul_self
    {g : ℝ → ℂ} {D : ℂ} {x : ℝ}
    (hne : g x ≠ 0) (hg : HasDerivAt g (D * g x) x) :
    HasDerivAt (fun u => Real.log ‖g u‖) D.re x := by
  let q : ℝ → ℝ := fun u => ‖g u‖ ^ 2
  have hinner : inner ℝ (g x) (D * g x) = q x * D.re := by
    rw [Complex.inner]
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hq : HasDerivAt q (2 * q x * D.re) x := by
    have hraw := hg.norm_sq
    simpa [q, hinner, mul_assoc] using hraw
  have hqpos : 0 < q x := by
    dsimp [q]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hlog := hq.log hqpos.ne'
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hhalf' : HasDerivAt
      (fun u => (1 / 2 : ℝ) * Real.log (q u)) D.re x := by
    apply hhalf.congr_deriv
    field_simp [hqpos.ne']
  convert hhalf' using 1
  funext u
  simp [q, Real.log_pow]

/-- Away from a xi zero, the horizontal-coordinate derivative of the shifted
xi log-norm potential is `Re (xi'/xi)`. -/
theorem hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate
    {a y : ℝ}
    (hne : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun u : ℝ => shiftedRiemannXiLogNorm u y)
      (shiftedRiemannXiLogDerivative a y).re a := by
  let s : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun u =>
    riemannXi (((u + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let affine : ℂ → ℂ := fun z => z + 1 / 2 + (y : ℂ) * Complex.I
  have haffine : HasDerivAt affine 1 (a : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (𝕜 := ℂ) (a : ℂ)).add_const (1 / 2)).add_const
        ((y : ℂ) * Complex.I)
  have hs : affine (a : ℂ) = s := by
    dsimp [affine, s]
    push_cast
    ring
  have hcomp : HasDerivAt (riemannXi ∘ affine)
      (deriv riemannXi s) (a : ℂ) := by
    have hxiAffine :=
      (differentiable_riemannXi (affine (a : ℂ))).hasDerivAt
    simpa only [hs, mul_one] using
      hxiAffine.comp (a : ℂ) haffine
  have hreal := hcomp.comp_ofReal
  have hgraw : HasDerivAt g (deriv riemannXi s) a := by
    convert hreal using 1
    · funext u
      dsimp [g, affine]
      push_cast
      ring
  let L : ℂ := shiftedRiemannXiLogDerivative a y
  have hga : g a = riemannXi s := by
    dsimp [g, s]
  have hnes : riemannXi s ≠ 0 := by
    exact hne
  have hderiv : deriv riemannXi s = L * g a := by
    rw [hga]
    dsimp [L, shiftedRiemannXiLogDerivative, s]
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hnes).symm
  have hg : HasDerivAt g (L * g a) a := by
    simpa [hderiv] using hgraw
  have hgne : g a ≠ 0 := by
    rw [hga]
    exact hnes
  have hlog := hasDerivAt_log_norm_of_hasDerivAt_mul_self hgne hg
  simpa [g, L, shiftedRiemannXiLogNorm] using hlog

/-- Away from a xi zero, the vertical-coordinate derivative of the shifted xi
log-norm potential is `-Im (xi'/xi)`. -/
theorem hasDerivAt_shiftedRiemannXiLogNorm_imaginaryCoordinate
    {a y : ℝ}
    (hne : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (shiftedRiemannXiLogNorm a)
      (-(shiftedRiemannXiLogDerivative a y).im) y := by
  let s : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun v =>
    riemannXi (((a + 1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
  let affine : ℂ → ℂ := fun z =>
    (((a + 1 / 2 : ℝ) : ℂ) + z * Complex.I)
  have haffine : HasDerivAt affine Complex.I (y : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (𝕜 := ℂ) (y : ℂ)).mul_const Complex.I).const_add
        (((a + 1 / 2 : ℝ) : ℂ))
  have hxi : HasDerivAt riemannXi (deriv riemannXi s) s :=
    (differentiable_riemannXi s).hasDerivAt
  have hs : affine (y : ℂ) = s := rfl
  have hcomp : HasDerivAt (riemannXi ∘ affine)
      (deriv riemannXi s * Complex.I) (y : ℂ) := by
    rw [← hs]
    exact hxi.comp (y : ℂ) haffine
  have hreal := hcomp.comp_ofReal
  have hgraw : HasDerivAt g (deriv riemannXi s * Complex.I) y := by
    simpa [g, affine] using hreal
  let L : ℂ := shiftedRiemannXiLogDerivative a y
  have hga : g y = riemannXi s := by rfl
  have hnes : riemannXi s ≠ 0 := by
    exact hne
  have hbase : deriv riemannXi s = L * g y := by
    rw [hga]
    dsimp [L, shiftedRiemannXiLogDerivative, s]
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hnes).symm
  have hderiv : deriv riemannXi s * Complex.I =
      (Complex.I * L) * g y := by
    rw [hbase]
    ring
  have hg : HasDerivAt g ((Complex.I * L) * g y) y := by
    simpa [hderiv] using hgraw
  have hgne : g y ≠ 0 := by
    rw [hga]
    exact hnes
  have hlog := hasDerivAt_log_norm_of_hasDerivAt_mul_self hgne hg
  convert hlog using 1
  · rfl
  · simp [L, Complex.mul_re]

/-- The real heat kernel paired with the horizontal derivative of the shifted
xi log-norm potential. -/
def suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand (x tau a y : ℝ) : ℝ :=
  suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y *
    deriv (fun u : ℝ => shiftedRiemannXiLogNorm u y) a

/-- Away from the xi divisor, the explicit xi boundary scalar is the heat
kernel times the horizontal derivative of the xi log-norm potential. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand_eq_logNorm_deriv
    (x tau a y : ℝ)
    (hne : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand
        x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
  rw [(hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate hne).deriv]

/-- On a zero-free vertical segment, the xi boundary scalar integral is
exactly its xi log-norm derivative form. -/
theorem intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalar_eq_logNorm_deriv
    (x tau a b u : ℝ) (hbu : b ≤ u)
    (hdomain : [[a, a]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    (∫ y : ℝ in b..u,
      suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand
        x tau a y) =
      ∫ y : ℝ in b..u,
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau a y := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hbu] at hy
  have hp : ((a : ℂ) + (y : ℂ) * Complex.I) ∈
      [[a, a]] ×ℂ [[b, u]] := by
    rw [mem_reProdIm, uIcc_of_le le_rfl, uIcc_of_le hbu]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, zero_add, add_zero,
      mul_one]
    exact ⟨⟨le_rfl, le_rfl⟩, hy⟩
  have hpdomain := hdomain hp
  have hpzero : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    change 0 < (((a : ℂ) + (y : ℂ) * Complex.I) + 1 / 2).re ∧
      riemannXi (((a : ℂ) + (y : ℂ) * Complex.I) + 1 / 2) ≠ 0 at hpdomain
    have hshift :
        ((a : ℂ) + (y : ℂ) * Complex.I) + 1 / 2 =
          (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hshift] at hpdomain
    exact hpdomain.2
  exact
    suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand_eq_logNorm_deriv
      x tau a y hpzero

/-- The Euclidean first-order pairing of the heat-kernel gradient with the xi
log-norm gradient in shifted coordinates. -/
def suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand (x tau a y : ℝ) : ℝ :=
  deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a *
      deriv (fun u : ℝ => shiftedRiemannXiLogNorm u y) a +
    deriv (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y *
      deriv (shiftedRiemannXiLogNorm a) y

/-- Away from the xi divisor, the explicit real xi bulk integrand is exactly
the heat-gradient--xi-log-norm-gradient pairing. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand_eq_logNorm_gradient
    (x tau a y : ℝ)
    (hne : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
  rw [suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand_eq_kernel_deriv_pair,
    (hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate hne).deriv,
    (hasDerivAt_shiftedRiemannXiLogNorm_imaginaryCoordinate hne).deriv]
  ring

/-- On each selected rectangle, the explicit xi bulk scalar and the log-norm
gradient pairing agree almost everywhere; the finite divisor is null. -/
theorem ae_suzukiChebyshevLaplaceBoundaryHeatXiBulkScalar_eq_logNorm_gradient_selected
    (x tau : ℝ) (n : ℕ) :
    ∀ᵐ p : ℂ ∂volume.restrict
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im =
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau p.re p.im := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  let W : Finset ℂ := suzukiChebyshevLaplaceZeroWindow T
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hbu : -T ≤ T := by linarith
  have hRmeas : MeasurableSet R :=
    (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
  have hWnull : (volume.restrict R) (W : Set ℂ) = 0 :=
    W.measure_zero (volume.restrict R)
  have havoid : ∀ᵐ p : ℂ ∂volume.restrict R, p ∉ (W : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.mp hWnull
  filter_upwards [ae_restrict_mem hRmeas, havoid] with p hpR hpW
  have hpR' : p.re ∈ [[l, r]] ∧ p.im ∈ [[-T, T]] := hpR
  rw [uIcc_of_le hlr, uIcc_of_le hbu] at hpR'
  have him : |p.im| ≤ T := abs_le.mpr hpR'.2
  have hpzero : riemannXi (p + 1 / 2) ≠ 0 := by
    intro hzero
    apply hpW
    exact (mem_suzukiChebyshevLaplaceZeroWindow_iff hT0 p).mpr
      ⟨hzero, him⟩
  have hpcoord :
      (((p.re + 1 / 2 : ℝ) : ℂ) + (p.im : ℂ) * Complex.I) =
        p + 1 / 2 := by
    apply Complex.ext <;> simp
  apply suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand_eq_logNorm_gradient
  rw [hpcoord]
  exact hpzero

/-- The xi log-norm gradient pairing is integrable on every selected rectangle
despite the finite xi divisor. -/
theorem integrableOn_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_selected
    (x tau : ℝ) (n : ℕ) :
    IntegrableOn (fun p : ℂ =>
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau p.re p.im)
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]) volume := by
  let R : Set ℂ :=
    [[selectedLaplaceSeparatedLeftBoundary n,
      selectedLaplaceSeparatedRightBoundary n]] ×ℂ
      [[-quantitativeSpectralBoundaryTruncation n,
        quantitativeSpectralBoundaryTruncation n]]
  have hcomplex :=
    integrableOn_separatedSelectedLaplaceXiLogDerivativeSource x tau n
  have hbulk : IntegrableOn
      (fun p : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im) R volume := by
    have him := hcomplex.im
    apply him.congr
    exact Filter.Eventually.of_forall fun p =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im
        x tau p
  apply hbulk.congr
  change
    ∀ᵐ p : ℂ ∂volume.restrict
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im =
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau p.re p.im
  exact ae_suzukiChebyshevLaplaceBoundaryHeatXiBulkScalar_eq_logNorm_gradient_selected x tau n

/-- The ordinary planar xi bulk scalar integral equals the ordinary integral
of the divisor-aware log-norm gradient pairing on every selected rectangle. -/
theorem integral_suzukiChebyshevLaplaceBoundaryHeatXiBulkScalar_eq_logNorm_gradient_selected
    (x tau : ℝ) (n : ℕ) :
    (∫ p : ℂ in
        ([[selectedLaplaceSeparatedLeftBoundary n,
            selectedLaplaceSeparatedRightBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
        x tau p.re p.im) =
      ∫ p : ℂ in
        ([[selectedLaplaceSeparatedLeftBoundary n,
            selectedLaplaceSeparatedRightBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau p.re p.im := by
  apply MeasureTheory.integral_congr_ae
  exact ae_suzukiChebyshevLaplaceBoundaryHeatXiBulkScalar_eq_logNorm_gradient_selected x tau n

/-- The selected boundary-minus-gradient functional written entirely through
the heat kernel and the shifted xi log-norm potential. -/
def separatedSelectedLaplaceXiLogNormGradientScalarHeat (x tau : ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (selectedLaplaceSeparatedRightBoundary n) y) -
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (selectedLaplaceSeparatedLeftBoundary n) y) -
  ∫ p : ℂ in
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau p.re p.im

/-- At every finite stage, the explicit real xi logarithmic-derivative scalar
is exactly the boundary-minus-log-norm-gradient functional. -/
theorem separatedSelectedLaplaceXiLogDerivativeScalarHeat_eq_logNormGradient
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceXiLogDerivativeScalarHeat x tau n =
      separatedSelectedLaplaceXiLogNormGradientScalarHeat x tau n := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hbu : -T ≤ T := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hright :=
    intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalar_eq_logNorm_deriv
    x tau r (-T) T hbu
      (by simpa [r, T] using
        separatedSelectedLaplaceRightVerticalRectangle_subset_poleClearedDomain n)
  have hleft := intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalar_eq_logNorm_deriv
    x tau l (-T) T hbu
      (by simpa [l, T] using
        separatedSelectedLaplaceLeftVerticalRectangle_subset_poleClearedDomain n)
  have hbulk :=
    integral_suzukiChebyshevLaplaceBoundaryHeatXiBulkScalar_eq_logNorm_gradient_selected
      x tau n
  unfold separatedSelectedLaplaceXiLogDerivativeScalarHeat
    separatedSelectedLaplaceXiLogNormGradientScalarHeat
  rw [hright, hleft, hbulk]

/-- The boundary-minus-xi-log-norm-gradient functional retains the
unnormalized limit to `2 * pi` times the complete nonnegative detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogNormGradientScalarHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceXiLogNormGradientScalarHeat x tau) atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogDerivativeScalarHeat x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n =>
    separatedSelectedLaplaceXiLogDerivativeScalarHeat_eq_logNormGradient
      x tau n

end

end RiemannGaussian
