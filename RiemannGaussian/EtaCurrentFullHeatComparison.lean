import RiemannGaussian.EtaTiltedHeatComposition

/-!
# Full-line heat comparison of the actual completed eta current

The full-time integral splits into the actual eta support return, the
actual gap return, and the nonpositive-time correction. All three are
genuinely integrable, including at zero tilt. The full-line composition is
evaluated at a common phase, and both signed corrections remain in the
completed-current identity.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The full-line composed mass has a uniform endpoint bound at nonnegative
tilt. Its exact amplification in heat width is displayed. -/
theorem integral_fullTwoHeatEnvelope_le {a h t u : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (∫ w, pairedEtaFullTwoHeatEnvelope a h t u w) ≤
      Real.exp (a ^ 2 * h ^ 2) / (4 * Real.sqrt Real.pi * h) := by
  rw [integral_pairedEtaFullTwoHeatEnvelope hh]
  have he : Real.exp (a ^ 2 * h ^ 2 - a * (t + u)) ≤ Real.exp (a ^ 2 * h ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hk := etaNormalizedHeatKernel_le (show 0 < 2 * h by positivity) (u - t)
  exact (mul_le_mul he hk (etaNormalizedHeatKernel_pos (by positivity) _).le
    (Real.exp_pos _).le).trans_eq (by ring)

/-- An actual integrable current with nonnegative physical endpoints has
an absolutely convergent full-line three-time heat integral. Zero tilt is
allowed because the full Gaussian slice, rather than only its supremum,
controls the intermediate-time integral. -/
theorem integrable_current_fullTwoHeat_prod {μ : Measure (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (f z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi (T z.1) z.1.2 z.2) (μ.prod volume) := by
  have hm := (measurable_pairedEtaFullTwoHeatKernel hphi hpsi a h).comp
    (((hT.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hmeas : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ ↦ (f z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi (T z.1) z.1.2 z.2) (μ.prod volume) :=
    hf.ofReal.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · exact Eventually.of_forall fun p ↦
      (integrable_pairedEtaFullTwoHeatKernel hh a (T p) p.2 hphi hpsi).const_mul (f p : ℂ)
  · have heq : (fun p ↦ ∫ w, ‖(f p : ℂ) * pairedEtaFullTwoHeatKernel a h phi psi (T p) p.2 w‖) =
        (fun p ↦ |f p| * (Real.exp (a ^ 2 * h ^ 2 - a * (T p + p.2)) *
          etaNormalizedHeatKernel (2 * h) (p.2 - T p))) := by
      funext p
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pairedEtaFullTwoHeatKernel hh]
      rw [integral_const_mul, integral_pairedEtaFullTwoHeatEnvelope hh]
    rw [heq]
    apply (hf.abs.mul_const (Real.exp (a ^ 2 * h ^ 2) / (4 * Real.sqrt Real.pi * h))).mono'
    · have hg : Measurable (fun p ↦ Real.exp (a ^ 2 * h ^ 2 - a * (T p + p.2)) *
          etaNormalizedHeatKernel (2 * h) (p.2 - T p)) := by
        unfold etaNormalizedHeatKernel
        fun_prop
      exact hf.abs.aestronglyMeasurable.mul hg.aestronglyMeasurable
    · filter_upwards [hpos] with p hp
      have hb := integral_fullTwoHeatEnvelope_le ha hh hp.1 hp.2
      rw [integral_pairedEtaFullTwoHeatEnvelope hh] at hb
      have hk := etaNormalizedHeatKernel_pos (show 0 < 2 * h by positivity) (p.2 - T p)
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- Full real time is exactly eta support plus eta gap plus nonpositive time. -/
theorem volume_eq_eta_support_add_gap_add_nonpositive :
    (volume : Measure ℝ) = (pairedEtaLogMeasure + pairedEtaLogGapMeasure) + volume.restrict (Iic 0) := by
  rw [← volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure]
  simpa only [compl_Ioi] using (Measure.restrict_add_restrict_compl (μ := volume) measurableSet_Ioi).symm

/-- The same completed current and physical head translation integrated
against an explicitly supplied intermediate-time measure. -/
def pairedEtaLeadingCurrentFullTwoHeatIntegral (rho : NontrivialZetaZero) (N : ℕ)
    (a h : ℝ) (phi psi : ℝ → ℝ) (ν : Measure ℝ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi
        (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2
      ∂(((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod ν)
  else
    ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi z.1.1 z.1.2 z.2
      ∂(((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod ν)

/-- Both actual multiplicity carriers have full-time integrability with
both ordered phases retained, including at zero tilt. -/
theorem integrable_leadingCurrent_fullTwoHeat_prod (rho : NontrivialZetaZero) (N : ℕ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi
        (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2)
      (((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod volume) ∧
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦
      (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi z.1.1 z.1.2 z.2)
      (((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod volume) := by
  constructor
  · apply integrable_current_fullTwoHeat_prod (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _) _ ha hh hphi hpsi
    exact (ae_head_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩
  · apply integrable_current_fullTwoHeat_prod (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst _ ha hh hphi hpsi
    exact (ae_adjacent_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩

/-- Every restriction dominated by real volume inherits genuine
three-time integrability for both completed current branches. -/
theorem integrable_leadingCurrent_fullTwoHeat_prod_of_le_volume
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi)
    {ν : Measure ℝ} (hν : ν ≤ volume) :
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi
        (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2)
      (((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod ν) ∧
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦
      (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
      pairedEtaFullTwoHeatKernel a h phi psi z.1.1 z.1.2 z.2)
      (((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod ν) := by
  obtain ⟨hhead, hadj⟩ := integrable_leadingCurrent_fullTwoHeat_prod rho N ha hh hphi hpsi
  exact ⟨Integrable.mono_measure hhead (Measure.prod_mono le_rfl hν),
    Integrable.mono_measure hadj (Measure.prod_mono le_rfl hν)⟩

/-- An integrable full-time product splits with both signed corrections
explicit: eta gap equals full time minus eta support minus nonpositive time. -/
theorem integral_prod_eta_gap_eq_full_sub_support_sub_nonpositive
    {μ : Measure (ℝ × ℝ)} [SFinite μ] {F : (ℝ × ℝ) × ℝ → ℂ}
    (hF : Integrable F (μ.prod volume)) :
    (∫ z, F z ∂μ.prod pairedEtaLogGapMeasure) = (∫ z, F z ∂μ.prod volume) -
      (∫ z, F z ∂μ.prod pairedEtaLogMeasure) - (∫ z, F z ∂μ.prod (volume.restrict (Iic 0))) := by
  have hm : μ.prod volume = (μ.prod pairedEtaLogMeasure + μ.prod pairedEtaLogGapMeasure) +
      μ.prod (volume.restrict (Iic 0)) := by
    calc
      _ = μ.prod ((pairedEtaLogMeasure + pairedEtaLogGapMeasure) + volume.restrict (Iic 0)) :=
        congrArg (fun ν ↦ μ.prod ν) volume_eq_eta_support_add_gap_add_nonpositive
      _ = _ := by rw [Measure.prod_add, Measure.prod_add]
  have hi := hF
  rw [hm] at hi
  have he : (∫ z, F z ∂μ.prod volume) =
      ((∫ z, F z ∂μ.prod pairedEtaLogMeasure) + (∫ z, F z ∂μ.prod pairedEtaLogGapMeasure)) +
        (∫ z, F z ∂μ.prod (volume.restrict (Iic 0))) := by
    rw [hm, integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
      integral_add_measure hi.left_of_add_measure.left_of_add_measure hi.left_of_add_measure.right_of_add_measure]
  rw [he]
  abel

/-- At nonnegative tilt, the original iterated current-gap pairing is
integrable and equals the unrestricted phase kernel on the actual gap. -/
theorem current_gapReturn_pairing_fullHeat {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun w ↦ ∫ p, (f p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore a h a h phi psi (T p) p.2 w ∂μ) pairedEtaLogGapMeasure ∧
    (∫ w, (∫ p, (f p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore a h a h phi psi (T p) p.2 w ∂μ) ∂pairedEtaLogGapMeasure) =
      ∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) * pairedEtaFullTwoHeatKernel a h phi psi (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure := by
  have hi := Integrable.mono_measure (integrable_current_fullTwoHeat_prod hf hT hpos ha hh hphi hpsi)
    (Measure.prod_mono le_rfl (show pairedEtaLogGapMeasure ≤ volume from Measure.restrict_le_self))
  have heq : (fun w ↦ ∫ p, (f p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore a h a h phi psi (T p) p.2 w ∂μ) =ᵐ[pairedEtaLogGapMeasure]
      (fun w ↦ ∫ p, (f p : ℂ) * pairedEtaFullTwoHeatKernel a h phi psi (T p) p.2 w ∂μ) := by
    filter_upwards [ae_mem_pairedEtaLogGapSupport] with w hw
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ by
      dsimp only
      rw [pairedEtaOrderedGapReturnKernelCore_eq_fullTwoHeat_of_mem_gap a h phi psi (T p) p.2 hw]
  refine ⟨hi.integral_prod_right.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact (integral_prod_symm _ hi).symm

/-- Both literal current branches have an integrable original gap pairing
and its exact unrestricted-kernel representation, including at zero tilt. -/
theorem pairedEtaLeadingCurrentIntegratedGapReturn_fullHeat
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (pairedEtaLeadingCurrentGapReturnPairing rho N a h a h phi psi) pairedEtaLogGapMeasure ∧
    pairedEtaLeadingCurrentIntegratedGapReturn rho N a h a h phi psi =
      pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi psi pairedEtaLogGapMeasure := by
  have hhead := current_gapReturn_pairing_fullHeat (integrable_topPrefixFiniteEnergyHeadKernel rho N)
    (measurable_fst.add_const _) ((ae_head_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩)
    ha hh hphi hpsi
  have hadj := current_gapReturn_pairing_fullHeat (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
    measurable_fst ((ae_adjacent_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩)
    ha hh hphi hpsi
  unfold pairedEtaLeadingCurrentIntegratedGapReturn pairedEtaLeadingCurrentGapReturnPairing
    pairedEtaLeadingCurrentFullTwoHeatIntegral
  split_ifs
  · exact hhead
  · exact hadj

/-- The actual completed gap return is the full-line heat pairing minus
both the support return and the nonpositive-time correction. Both ordered
probe phases, the translated head, and multiplicity are retained. -/
theorem pairedEtaLeadingCurrentIntegratedGapReturn_eq_full_sub_support_sub_nonpositive
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    pairedEtaLeadingCurrentIntegratedGapReturn rho N a h a h phi psi =
      pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi psi volume -
        pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi psi pairedEtaLogMeasure -
        pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi psi (volume.restrict (Iic 0)) := by
  rw [(pairedEtaLeadingCurrentIntegratedGapReturn_fullHeat rho N ha hh hphi hpsi).2]
  obtain ⟨hhead, hadj⟩ := integrable_leadingCurrent_fullTwoHeat_prod rho N ha hh hphi hpsi
  unfold pairedEtaLeadingCurrentFullTwoHeatIntegral
  split_ifs
  · exact integral_prod_eta_gap_eq_full_sub_support_sub_nonpositive hhead
  · exact integral_prod_eta_gap_eq_full_sub_support_sub_nonpositive hadj

/-- Full-line composition commutes with the actual current integral,
retaining the common endpoint phase and exact tilted amplitude. -/
theorem integral_current_fullTwoHeat_same_phase {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) * pairedEtaFullTwoHeatKernel a h phi phi (T z.1) z.1.2 z.2
      ∂μ.prod volume) =
      ∫ p, (f p : ℂ) * ((Real.exp (a ^ 2 * h ^ 2 - a * (T p + p.2)) *
        etaNormalizedHeatKernel (2 * h) (p.2 - T p) : ℝ) * pairedEtaHeatPhaseUnit phi (p.2, T p)) ∂μ := by
  rw [integral_prod _ (integrable_current_fullTwoHeat_prod hf hT hpos ha hh hphi hphi)]
  apply integral_congr_ae
  filter_upwards with p
  rw [integral_const_mul, integral_pairedEtaFullTwoHeatKernel_same_phase hh]

/-- The actual completed current paired with the explicitly composed
broader Gaussian and the common endpoint phase. -/
def pairedEtaLeadingCurrentComposedHeatIntegral (rho : NontrivialZetaZero) (N : ℕ)
    (a h : ℝ) (phi : ℝ → ℝ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      ((Real.exp (a ^ 2 * h ^ 2 - a * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2)) *
        etaNormalizedHeatKernel (2 * h) (p.2 - (p.1 + pairedEtaLogTailCutoff (N + 1))) : ℝ) *
          pairedEtaHeatPhaseUnit phi (p.2, p.1 + pairedEtaLogTailCutoff (N + 1)))
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      ((Real.exp (a ^ 2 * h ^ 2 - a * (p.1 + p.2)) * etaNormalizedHeatKernel (2 * h) (p.2 - p.1) : ℝ) *
        pairedEtaHeatPhaseUnit phi (p.2, p.1))
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- The full-line integral evaluates to the broader Gaussian on both
actual completed current carriers, with the physical head time restored. -/
theorem pairedEtaLeadingCurrentFullTwoHeatIntegral_eq_composed
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi phi volume =
      pairedEtaLeadingCurrentComposedHeatIntegral rho N a h phi := by
  unfold pairedEtaLeadingCurrentFullTwoHeatIntegral pairedEtaLeadingCurrentComposedHeatIntegral
  split_ifs
  · exact integral_current_fullTwoHeat_same_phase (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _) ((ae_head_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩)
      ha hh hphi
  · exact integral_current_fullTwoHeat_same_phase (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst ((ae_adjacent_current_physical_window N).mono fun p hp ↦ ⟨hp.1.1, hp.2.1⟩)
      ha hh hphi

/-- Exact continuous comparison with the broader Gaussian: the actual
completed gap return retains the support and nonpositive-time corrections.
This identity is valid at zero tilt as well as positive tilt. -/
theorem pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    pairedEtaLeadingCurrentIntegratedGapReturn rho N a h a h phi phi =
      pairedEtaLeadingCurrentComposedHeatIntegral rho N a h phi -
        pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi phi pairedEtaLogMeasure -
        pairedEtaLeadingCurrentFullTwoHeatIntegral rho N a h phi phi (volume.restrict (Iic 0)) := by
  rw [pairedEtaLeadingCurrentIntegratedGapReturn_eq_full_sub_support_sub_nonpositive rho N ha hh hphi hphi,
    pairedEtaLeadingCurrentFullTwoHeatIntegral_eq_composed rho N ha hh hphi]

end

end RiemannGaussian
