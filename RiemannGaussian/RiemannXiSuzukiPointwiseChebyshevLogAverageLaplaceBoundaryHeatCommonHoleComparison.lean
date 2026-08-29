import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteBallExcision

/-!
# Common-hole comparison and finite Cauchy--Green identity

The termwise finite-window Cauchy--Green construction used one shrinking
square for each principal part, whereas the geometric construction removes
one finite union of common-radius balls from the actual arithmetic source.
This file proves that the square approximation of every locally integrable
principal-part source converges to its ordinary through-pole planar area.

It then combines the response and source decompositions using the same
analytic remainder and removes all auxiliary puncture parameters.  The
result is an exact finite-window Cauchy--Green identity involving only the
actual outer boundary, the genuinely integrable arithmetic area, and the
complete finite multiplicity-weighted heat-residue sum.  The common-ball
integral is proved to converge to that same value.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology ENNReal

/-! ## Half-open planar rectangles -/

/-- On ordered endpoints, the iterated rectangular area integral of an
integrable function is its planar set integral over the corresponding
half-open coordinate rectangle.  The half-open convention makes subsequent
rectangle unions literally disjoint. -/
theorem rectangularAreaIntegral_eq_setIntegral_Ioc
    {l r b u : ℝ} (hlr : l ≤ r) (hbu : b ≤ u) (g : ℂ → ℂ)
    (hg : IntegrableOn g (Set.Ioc l r ×ℂ Set.Ioc b u) volume) :
    rectangularAreaIntegral l r b u g =
      ∫ z in Set.Ioc l r ×ℂ Set.Ioc b u, g z ∂volume := by
  let A : Set ℝ := Set.Ioc l r
  let B : Set ℝ := Set.Ioc b u
  let R : Set ℂ := A ×ℂ B
  let f : ℝ × ℝ → ℂ := fun p =>
    g (Complex.equivRealProdCLM.symm p)
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' R = A ×ˢ B := by
    rfl
  have hpair : IntegrableOn f (A ×ˢ B) (volume.prod volume) := by
    have h :=
      ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
        (MeasurableEquiv.measurableEmbedding _)).2
        (show IntegrableOn g R volume from hg)
    rw [hpre] at h
    rw [Measure.volume_eq_prod ℝ ℝ] at h
    exact h
  have hprod : Integrable f ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hpair
  have hchange :=
    (Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _) g R
  unfold rectangularAreaIntegral
  rw [intervalIntegral.integral_of_le hlr]
  simp_rw [intervalIntegral.integral_of_le hbu]
  calc
    (∫ a in Set.Ioc l r, ∫ y in Set.Ioc b u,
        g ((a : ℂ) + (y : ℂ) * Complex.I) ∂volume ∂volume) =
        ∫ p, f p ∂((volume.restrict A).prod (volume.restrict B)) := by
      simpa [f, A, B, Complex.equivRealProdCLM_symm_apply] using
        (integral_prod f hprod).symm
    _ = ∫ p in A ×ˢ B, f p ∂(volume.prod volume) := by
      rw [Measure.prod_restrict]
    _ = ∫ z in R, g z ∂volume := by
      rw [hpre] at hchange
      rw [Measure.volume_eq_prod ℝ ℝ] at hchange
      exact hchange
    _ = ∫ z in Set.Ioc l r ×ℂ Set.Ioc b u, g z ∂volume := by
      rfl

/-- A half-open product of real coordinate intervals is a measurable subset
of the complex plane. -/
theorem measurableSet_Ioc_reProdIm (l r b u : ℝ) :
    MeasurableSet (Set.Ioc l r ×ℂ Set.Ioc b u) := by
  change MeasurableSet (Complex.measurableEquivRealProd ⁻¹'
    (Set.Ioc l r ×ˢ Set.Ioc b u))
  exact Complex.measurableEquivRealProd.measurable
    (measurableSet_Ioc.prod measurableSet_Ioc)

/-! ## Shrinking square geometry -/

/-- The half-open axis-parallel square of coordinate radius `q` centered at
`c`.  This endpoint convention agrees with the iterated-integral convention
and assigns every internal edge to exactly one surrounding rectangle. -/
def centeredHalfOpenSquare (c : ℂ) (q : ℝ) : Set ℂ :=
  Set.Ioc (c.re - q) (c.re + q) ×ℂ
  Set.Ioc (c.im - q) (c.im + q)

/-- The exact planar volume of a centered half-open coordinate square. -/
theorem volume_centeredHalfOpenSquare (c : ℂ) (q : ℝ) :
    volume (centeredHalfOpenSquare c q) =
      ENNReal.ofReal (2 * q) ^ 2 := by
  change volume (Complex.measurableEquivRealProd ⁻¹'
    (Set.Ioc (c.re - q) (c.re + q) ×ˢ
      Set.Ioc (c.im - q) (c.im + q))) = _
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ioc.prod measurableSet_Ioc).nullMeasurableSet,
    Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioc]
  ring_nf

/-- The volume of a centered half-open square tends to zero as its positive
coordinate radius tends to zero. -/
theorem tendsto_volume_centeredHalfOpenSquare_zero (c : ℂ) :
    Tendsto (fun q : ℝ => volume (centeredHalfOpenSquare c q))
      (𝓝[>] 0) (𝓝 0) := by
  simp only [volume_centeredHalfOpenSquare]
  have h : Tendsto (fun q : ℝ => ENNReal.ofReal (2 * q) ^ 2)
      (𝓝 0) (𝓝 (ENNReal.ofReal (2 * 0) ^ 2)) := by
    exact ENNReal.Tendsto.pow (ENNReal.tendsto_ofReal
      (tendsto_const_nhds.mul tendsto_id))
  simpa using h.mono_left nhdsWithin_le_nhds

/-- Removing a shrinking centered half-open square does not change the
limiting integral of a function integrable on the ambient measurable set. -/
theorem tendsto_centeredHalfOpenSquareExcisionIntegral
    (R : Set ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hRmeas : MeasurableSet R) (hg : IntegrableOn g R volume) :
    Tendsto
      (fun q : ℝ => ∫ z in R \ centeredHalfOpenSquare c q,
        g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in R, g z ∂volume)) := by
  have hsmall : Tendsto
      (fun q : ℝ => ∫ z in centeredHalfOpenSquare c q,
        R.indicator g z ∂volume)
      (𝓝[>] 0) (𝓝 0) :=
    (hg.integrable_indicator hRmeas).tendsto_setIntegral_nhds_zero
      (tendsto_volume_centeredHalfOpenSquare_zero c)
  have hsmall' : Tendsto
      (fun q : ℝ => ∫ z in R ∩ centeredHalfOpenSquare c q,
        g z ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [setIntegral_indicator hRmeas, inter_comm] using hsmall
  have hlimit :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ∫ z in R, g z ∂volume) (𝓝[>] 0)
      (𝓝 (∫ z in R, g z ∂volume))).sub hsmall'
  have hlimit' : Tendsto
      (fun q : ℝ => (∫ z in R, g z ∂volume) -
        ∫ z in R ∩ centeredHalfOpenSquare c q, g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in R, g z ∂volume)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with q
  have hset : R \ centeredHalfOpenSquare c q =
      R \ (R ∩ centeredHalfOpenSquare c q) := by
    ext z
    simp
  rw [hset]
  exact (setIntegral_sdiff
    (hRmeas.inter (by
      simpa [centeredHalfOpenSquare] using
        measurableSet_Ioc_reProdIm
          (c.re - q) (c.re + q) (c.im - q) (c.im + q)))
    hg inter_subset_left).symm

/-- The four iterated rectangle integrals surrounding a strictly internal
centered square are exactly one planar set integral over the half-open outer
rectangle with that square removed. -/
theorem rectangularAreaIntegralOutsideCenteredSquare_eq_setIntegral
    (l r b u q : ℝ) (c : ℂ) (g : ℂ → ℂ)
    (hgloc : LocallyIntegrable g volume)
    (hq : 0 < q)
    (hl : l < c.re - q) (hr : c.re + q < r)
    (hb : b < c.im - q) (hu : c.im + q < u) :
    rectangularAreaIntegralOutsideCenteredSquare l r b u c q g =
      ∫ z in (Set.Ioc l r ×ℂ Set.Ioc b u) \
        centeredHalfOpenSquare c q, g z ∂volume := by
  let Ls : Set ℂ := Set.Ioc l (c.re - q) ×ℂ Set.Ioc b u
  let Bs : Set ℂ := Set.Ioc (c.re - q) (c.re + q) ×ℂ
    Set.Ioc b (c.im - q)
  let Ts : Set ℂ := Set.Ioc (c.re - q) (c.re + q) ×ℂ
    Set.Ioc (c.im + q) u
  let Ds : Set ℂ := Set.Ioc (c.re + q) r ×ℂ Set.Ioc b u
  let Os : Set ℂ := Set.Ioc l r ×ℂ Set.Ioc b u
  let Cs : Set ℂ := centeredHalfOpenSquare c q
  have hbu : b ≤ u := by linarith
  have hmiddleRe : c.re - q ≤ c.re + q := by linarith
  have hLI : IntegrableOn g Ls volume := by
    apply (hgloc.integrableOn_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc :
        IsCompact (Set.Icc l (c.re - q) ×ℂ Set.Icc b u))).mono_set
    intro z hz
    simpa only [Ls, mem_reProdIm, mem_Ioc, mem_Icc] using
      ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hBI : IntegrableOn g Bs volume := by
    apply (hgloc.integrableOn_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc :
        IsCompact (Set.Icc (c.re - q) (c.re + q) ×ℂ
          Set.Icc b (c.im - q)))).mono_set
    intro z hz
    simpa only [Bs, mem_reProdIm, mem_Ioc, mem_Icc] using
      ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hTI : IntegrableOn g Ts volume := by
    apply (hgloc.integrableOn_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc :
        IsCompact (Set.Icc (c.re - q) (c.re + q) ×ℂ
          Set.Icc (c.im + q) u))).mono_set
    intro z hz
    simpa only [Ts, mem_reProdIm, mem_Ioc, mem_Icc] using
      ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hDI : IntegrableOn g Ds volume := by
    apply (hgloc.integrableOn_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc :
        IsCompact (Set.Icc (c.re + q) r ×ℂ Set.Icc b u))).mono_set
    intro z hz
    simpa only [Ds, mem_reProdIm, mem_Ioc, mem_Icc] using
      ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hLm : MeasurableSet Ls := by
    exact measurableSet_Ioc_reProdIm _ _ _ _
  have hBm : MeasurableSet Bs := by
    exact measurableSet_Ioc_reProdIm _ _ _ _
  have hTm : MeasurableSet Ts := by
    exact measurableSet_Ioc_reProdIm _ _ _ _
  have hDm : MeasurableSet Ds := by
    exact measurableSet_Ioc_reProdIm _ _ _ _
  have hLB : Disjoint Ls Bs := by
    rw [Set.disjoint_left]
    intro z hzL hzB
    simp only [Ls, Bs, mem_reProdIm, mem_Ioc] at hzL hzB
    linarith [hzL.1.2, hzB.1.1]
  have hLBT : Disjoint (Ls ∪ Bs) Ts := by
    rw [Set.disjoint_left]
    intro z hzLB hzT
    rcases hzLB with hzL | hzB
    · simp only [Ls, Ts, mem_reProdIm, mem_Ioc] at hzL hzT
      linarith [hzL.1.2, hzT.1.1]
    · simp only [Bs, Ts, mem_reProdIm, mem_Ioc] at hzB hzT
      linarith [hzB.2.2, hzT.2.1]
  have hLBTD : Disjoint ((Ls ∪ Bs) ∪ Ts) Ds := by
    rw [Set.disjoint_left]
    intro z hzLBT hzD
    rcases hzLBT with (hzL | hzB) | hzT
    · simp only [Ls, Ds, mem_reProdIm, mem_Ioc] at hzL hzD
      linarith [hzL.1.2, hzD.1.1]
    · simp only [Bs, Ds, mem_reProdIm, mem_Ioc] at hzB hzD
      linarith [hzB.1.2, hzD.1.1]
    · simp only [Ts, Ds, mem_reProdIm, mem_Ioc] at hzT hzD
      linarith [hzT.1.2, hzD.1.1]
  have hsets : ((Ls ∪ Bs) ∪ Ts) ∪ Ds = Os \ Cs := by
    ext z
    simp only [mem_union, Set.mem_sdiff, Ls, Bs, Ts, Ds, Os, Cs,
      centeredHalfOpenSquare, mem_reProdIm, mem_Ioc]
    constructor
    · intro hz
      rcases hz with ((hzL | hzB) | hzT) | hzD
      · refine ⟨⟨⟨hzL.1.1, ?_⟩, hzL.2⟩, ?_⟩
        · linarith [hzL.1.2, hr]
        · intro hzC
          linarith [hzL.1.2, hzC.1.1]
      · refine ⟨⟨⟨?_, ?_⟩, ⟨hzB.2.1, ?_⟩⟩, ?_⟩
        · linarith [hl, hzB.1.1]
        · linarith [hzB.1.2, hr]
        · linarith [hzB.2.2, hu]
        · intro hzC
          linarith [hzB.2.2, hzC.2.1]
      · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, hzT.2.2⟩⟩, ?_⟩
        · linarith [hl, hzT.1.1]
        · linarith [hzT.1.2, hr]
        · linarith [hb, hzT.2.1]
        · intro hzC
          linarith [hzT.2.1, hzC.2.2]
      · refine ⟨⟨⟨?_, hzD.1.2⟩, hzD.2⟩, ?_⟩
        · linarith [hl, hzD.1.1]
        · intro hzC
          linarith [hzD.1.1, hzC.1.2]
    · rintro ⟨⟨⟨hzl, hzr⟩, ⟨hzb, hzu⟩⟩, hzC⟩
      by_cases hxL : z.re ≤ c.re - q
      · exact Or.inl (Or.inl (Or.inl ⟨⟨hzl, hxL⟩, ⟨hzb, hzu⟩⟩))
      by_cases hxD : c.re + q < z.re
      · exact Or.inr ⟨⟨hxD, hzr⟩, ⟨hzb, hzu⟩⟩
      have hxLower : c.re - q < z.re := lt_of_not_ge hxL
      have hxUpper : z.re ≤ c.re + q := le_of_not_gt hxD
      by_cases hyB : z.im ≤ c.im - q
      · exact Or.inl (Or.inl (Or.inr
          ⟨⟨hxLower, hxUpper⟩, ⟨hzb, hyB⟩⟩))
      have hyLower : c.im - q < z.im := lt_of_not_ge hyB
      have hyTop : c.im + q < z.im := by
        by_contra h
        exact hzC ⟨⟨hxLower, hxUpper⟩,
          ⟨hyLower, le_of_not_gt h⟩⟩
      exact Or.inl (Or.inr
        ⟨⟨hxLower, hxUpper⟩, ⟨hyTop, hzu⟩⟩)
  have hLarea : rectangularAreaIntegral l (c.re - q) b u g =
      ∫ z in Ls, g z ∂volume := by
    simpa [Ls] using rectangularAreaIntegral_eq_setIntegral_Ioc
      (le_of_lt hl) hbu g hLI
  have hBarea : rectangularAreaIntegral (c.re - q) (c.re + q)
      b (c.im - q) g = ∫ z in Bs, g z ∂volume := by
    simpa [Bs] using rectangularAreaIntegral_eq_setIntegral_Ioc
      hmiddleRe (le_of_lt hb) g hBI
  have hTarea : rectangularAreaIntegral (c.re - q) (c.re + q)
      (c.im + q) u g = ∫ z in Ts, g z ∂volume := by
    simpa [Ts] using rectangularAreaIntegral_eq_setIntegral_Ioc
      hmiddleRe (le_of_lt hu) g hTI
  have hDarea : rectangularAreaIntegral (c.re + q) r b u g =
      ∫ z in Ds, g z ∂volume := by
    simpa [Ds] using rectangularAreaIntegral_eq_setIntegral_Ioc
      (le_of_lt hr) hbu g hDI
  unfold rectangularAreaIntegralOutsideCenteredSquare
  rw [hLarea, hBarea, hTarea, hDarea,
    ← setIntegral_union hLB hBm hLI hBI,
    ← setIntegral_union hLBT hTm (hLI.union hBI) hTI,
    ← setIntegral_union hLBTD hDm ((hLI.union hBI).union hTI) hDI,
    hsets]

/-- For a locally integrable planar function, the four-rectangle square
excision approximation converges to the ordinary through-center rectangular
area integral. -/
theorem tendsto_rectangularAreaIntegralOutsideCenteredSquare_eq_full
    (l r b u : ℝ) (c : ℂ) (g : ℂ → ℂ)
    (hgloc : LocallyIntegrable g volume)
    (hl : l < c.re) (hr : c.re < r)
    (hb : b < c.im) (hu : c.im < u) :
    Tendsto
      (fun q : ℝ =>
        rectangularAreaIntegralOutsideCenteredSquare l r b u c q g)
      (𝓝[>] 0) (𝓝 (rectangularAreaIntegral l r b u g)) := by
  have hlr : l ≤ r := by linarith
  have hbu : b ≤ u := by linarith
  have houter : IntegrableOn g
      (Set.Ioc l r ×ℂ Set.Ioc b u) volume := by
    apply (hgloc.integrableOn_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc :
        IsCompact (Set.Icc l r ×ℂ Set.Icc b u))).mono_set
    intro z hz
    simpa only [mem_reProdIm, mem_Ioc, mem_Icc] using
      ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hgeom := tendsto_centeredHalfOpenSquareExcisionIntegral
    (Set.Ioc l r ×ℂ Set.Ioc b u) c g
    (measurableSet_Ioc_reProdIm l r b u) houter
  rw [← rectangularAreaIntegral_eq_setIntegral_Ioc
    hlr hbu g houter] at hgeom
  have hleftRange : Ioo (0 : ℝ) (c.re - l) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hl)
  have hrightRange : Ioo (0 : ℝ) (r - c.re) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hr)
  have hbottomRange : Ioo (0 : ℝ) (c.im - b) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hb)
  have htopRange : Ioo (0 : ℝ) (u - c.im) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hu)
  apply hgeom.congr'
  filter_upwards [hleftRange, hrightRange, hbottomRange, htopRange]
      with q hql hqr hqb hqu
  symm
  exact rectangularAreaIntegralOutsideCenteredSquare_eq_setIntegral
    l r b u q c g hgloc hql.1
      (by linarith [hql.2]) (by linarith [hqr.2])
      (by linarith [hqb.2]) (by linarith [hqu.2])

/-- The ordinary through-pole planar area of one heat-weighted principal-part
source equals its outer boundary integral minus its exact moving heat
residue.  Local planar integrability turns the earlier improper-square
identity into an equality with no puncture parameter. -/
theorem rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource_eq_boundary_sub_residue
    (x tau l r b u : ℝ) (L c : ℂ)
    (hl : l < c.re) (hr : c.re < r)
    (hb : b < c.im) (hu : c.im < u) :
    rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
          x tau L c) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) -
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c * L) := by
  have hfull :=
    tendsto_rectangularAreaIntegralOutsideCenteredSquare_eq_full
      l r b u c
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau L c)
      (locallyIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau L c) hl hr hb hu
  have hresidue :=
    tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
      x tau l r b u L c hl hr hb hu
  exact tendsto_nhds_unique hfull hresidue

/-- One analytic finite-window remainder simultaneously decomposes both the
heat-weighted arithmetic response and its explicit Cauchy--Green source away
from the complete finite xi divisor. -/
theorem exists_suzukiChebyshevLaplaceBoundaryHeatWeighted_finitePrincipalPartDecompositions
    (x tau : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau z =
          (∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho) z) +
            suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
              x tau F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z =
          (∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho) z) +
            suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
              x tau F z) := by
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplacePoleClearedWindowAnalyticDecomposition hT
  refine ⟨F, hF, ?_, ?_⟩
  · intro z hz
    unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
    rw [hdecomp z hz, mul_add]
    unfold suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
      suzukiChebyshevLaplacePoleClearedPrincipalPart
    rw [Finset.mul_sum]
  · intro z hz
    unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
    rw [hdecomp z hz, mul_add]
    unfold suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
      suzukiChebyshevLaplacePoleClearedPrincipalPart
    rw [Finset.mul_sum]

/-! ## Parameter-free finite Cauchy--Green identity -/

/-- Exact finite-window Cauchy--Green identity for the actual arithmetic
response.  On an ordered rectangle inside the complete slab and strictly
containing every selected zero, the genuinely integrable through-divisor
area is the actual outer boundary minus the complete finite
multiplicity-weighted heat-residue sum.  No square radius, ball radius,
regularization function, or puncture limit occurs in the statement. -/
theorem suzukiChebyshevLaplaceBoundaryHeat_finiteCauchyGreen
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ spectralZetaZeroWindow T,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) :
    rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          ∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ) := by
  let R : Set ℂ := [[l, r]] ×ℂ [[b, u]]
  let W := spectralZetaZeroWindow T
  let P : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  let PS : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  obtain ⟨F, hF, hresponse, hsource⟩ :=
    exists_suzukiChebyshevLaplaceBoundaryHeatWeighted_finitePrincipalPartDecompositions
      x tau hT
  let H : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder x tau F
  let HS : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource x tau F
  let PSum : ℂ → ℂ := fun z => ∑ rho ∈ W, P rho z
  let PSSum : ℂ → ℂ := fun z => ∑ rho ∈ W, PS rho z
  have hcompact : IsCompact R := by
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  have hFRectangle : ∀ z ∈ R, AnalyticAt ℂ F z :=
    fun z hz => hF z (hrectangle hz)
  have hPBoundaryInt : ∀ rho ∈ W,
      rectangularBoundaryIntegrable l r b u (P rho) := by
    intro rho hrho
    have hi := hinside rho (by simpa [W] using hrho)
    simpa [P] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_of_mem
        x tau (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho) l r b u
          hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hPSumBoundaryInt : rectangularBoundaryIntegrable l r b u PSum := by
    simpa [PSum] using
      rectangularBoundaryIntegrable_finsetSum l r b u W P hPBoundaryInt
  have hHBoundaryInt : rectangularBoundaryIntegrable l r b u H := by
    simpa [H, R] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
        x tau l r b u F hFRectangle
  have hnotBottom (a : ℝ) :
      (a : ℂ) + (b : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = b := by
      simpa using congrArg Complex.im heq
    linarith [(hinside rho hrho).2.2.1]
  have hnotTop (a : ℝ) :
      (a : ℂ) + (u : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = u := by
      simpa using congrArg Complex.im heq
    linarith [(hinside rho hrho).2.2.2]
  have hnotRight (y : ℝ) :
      (r : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = r := by
      simpa using congrArg Complex.re heq
    linarith [(hinside rho hrho).2.1]
  have hnotLeft (y : ℝ) :
      (l : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = l := by
      simpa using congrArg Complex.re heq
    linarith [(hinside rho hrho).1]
  have hboundaryCongr : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) := by
    apply rectangularBoundaryIntegral_congr_of_eq_on_sides
    · intro a ha
      simpa [PSum, P, H] using
        hresponse ((a : ℂ) + (b : ℂ) * Complex.I) (hnotBottom a)
    · intro a ha
      simpa [PSum, P, H] using
        hresponse ((a : ℂ) + (u : ℂ) * Complex.I) (hnotTop a)
    · intro y hy
      simpa [PSum, P, H] using
        hresponse ((r : ℂ) + (y : ℂ) * Complex.I) (hnotRight y)
    · intro y hy
      simpa [PSum, P, H] using
        hresponse ((l : ℂ) + (y : ℂ) * Complex.I) (hnotLeft y)
  have hboundaryDecomp : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      (∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho)) +
        rectangularBoundaryIntegral l r b u H := by
    calc
      _ = rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) :=
        hboundaryCongr
      _ = rectangularBoundaryIntegral l r b u PSum +
          rectangularBoundaryIntegral l r b u H :=
        rectangularBoundaryIntegral_add l r b u
          hPSumBoundaryInt hHBoundaryInt
      _ = _ := by
        rw [show rectangularBoundaryIntegral l r b u PSum =
            ∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho) by
          simpa [PSum] using
            rectangularBoundaryIntegral_finsetSum l r b u W P
              hPBoundaryInt]
  have hPSInt : ∀ rho ∈ W, IntegrableOn (PS rho) R volume := by
    intro rho hrho
    exact
      (locallyIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho)).integrableOn_isCompact
        hcompact
  have hPSSumInt : IntegrableOn PSSum R volume := by
    change Integrable PSSum (volume.restrict R)
    simpa [PSSum] using integrable_finsetSum W hPSInt
  have hHSInt : IntegrableOn HS R volume := by
    exact
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
          x tau).continuousOn.mul
        (show AnalyticOnNhd ℂ F R from hFRectangle).continuousOn).integrableOn_compact
        hcompact
  have hactualInt : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      R volume := by
    simpa [R] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
        x tau l r b u hT hrectangle
  have hsourceAE : ∀ᵐ z ∂volume.restrict R,
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z =
        PSSum z + HS z := by
    filter_upwards [ae_restrict_of_ae
      ((suzukiChebyshevLaplaceZeroWindow T).finite_toSet.countable.ae_notMem
        volume)] with z hz
    simpa [PSSum, PS, HS, W] using hsource z hz
  have hsetAreaDecomp :
      (∫ z in R,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z
        ∂volume) =
      (∫ z in R, PSSum z ∂volume) +
        ∫ z in R, HS z ∂volume := by
    rw [integral_congr_ae hsourceAE]
    exact integral_add hPSSumInt hHSInt
  have hHSArea : rectangularAreaIntegral l r b u HS =
      ∫ z in R, HS z ∂volume := by
    simpa [R] using rectangularAreaIntegral_eq_setIntegral
      hlr hbu HS hHSInt
  have hPSAreas :
      (∑ rho ∈ W, rectangularAreaIntegral l r b u (PS rho)) =
        ∑ rho ∈ W, ∫ z in R, PS rho z ∂volume := by
    apply Finset.sum_congr rfl
    intro rho hrho
    simpa [R] using rectangularAreaIntegral_eq_setIntegral
      hlr hbu (PS rho) (hPSInt rho hrho)
  have hPSSumArea :
      (∫ z in R, PSSum z ∂volume) =
        ∑ rho ∈ W, ∫ z in R, PS rho z ∂volume := by
    simpa [PSSum] using integral_finsetSum W hPSInt
  have hareaDecomp : rectangularAreaIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularAreaIntegral l r b u HS +
        ∑ rho ∈ W, rectangularAreaIntegral l r b u (PS rho) := by
    rw [rectangularAreaIntegral_eq_setIntegral hlr hbu _ hactualInt,
      hsetAreaDecomp, hPSSumArea, ← hHSArea, ← hPSAreas]
    ring
  have hHCG : rectangularBoundaryIntegral l r b u H =
      rectangularAreaIntegral l r b u HS := by
    simpa [H, HS, R] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder_rectangularCauchyGreen
        x tau l r b u F hFRectangle
  have hPSIdentity : ∀ rho ∈ W,
      rectangularAreaIntegral l r b u (PS rho) =
        rectangularBoundaryIntegral l r b u (P rho) -
          (2 * Real.pi * Complex.I) *
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ)) := by
    intro rho hrho
    have hi := hinside rho (by simpa [W] using hrho)
    simpa [P, PS] using
      rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource_eq_boundary_sub_residue
        x tau l r b u (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho)
          hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  rw [hareaDecomp, ← hHCG,
    Finset.sum_congr rfl hPSIdentity, Finset.sum_sub_distrib,
    Finset.mul_sum]
  rw [show rectangularBoundaryIntegral l r b u H +
      ((∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho)) -
        ∑ rho ∈ W, (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (suzukiChebyshevLaplaceZeroCoordinate rho) *
            (analyticZetaZeroMultiplicity rho : ℂ))) =
      ((∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho)) +
        rectangularBoundaryIntegral l r b u H) -
        ∑ rho ∈ W, (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (suzukiChebyshevLaplaceZeroCoordinate rho) *
            (analyticZetaZeroMultiplicity rho : ℂ)) by ring,
    ← hboundaryDecomp]

/-- The literal common-ball multiply punctured area converges to the same
boundary-minus-residue value as the termwise shrinking-square construction.
This identifies the two finite regularization geometries without asserting
pointwise equality at positive radius. -/
theorem tendsto_suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral_eq_boundary_sub_residue
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ spectralZetaZeroWindow T,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) :
    Tendsto
      (fun q : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
          x tau T l r b u q)
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          ∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hgeom :=
    tendsto_suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
      x tau l r b u hT hlr hbu hrectangle
  rw [suzukiChebyshevLaplaceBoundaryHeat_finiteCauchyGreen
    x tau l r b u hT hlr hbu hrectangle hinside] at hgeom
  exact hgeom

end

end RiemannGaussian
