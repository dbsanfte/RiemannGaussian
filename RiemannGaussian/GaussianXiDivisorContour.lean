import RiemannGaussian.GaussianArchimedeanContour
import Mathlib.Analysis.Meromorphic.LogDeriv

/-!
# The xi zero-divisor contour

This file isolates the last analytic contour in the Gaussian explicit
formula.  The functional equation makes the completed xi function even in
the spectral coordinate, so its Gaussian-weighted negative logarithmic
derivative is odd.  Consequently the upper safe line is exactly the
negative of the lower safe line; a residue computation across the whole
critical strip will therefore evaluate twice the already-integrable lower
line.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Functional equation for the pole-cleared entire xi normalization. -/
theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Differentiating the xi functional equation reverses the sign. -/
theorem deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hder := congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  rw [deriv_comp_const_sub] at hder
  simpa using congrArg Neg.neg hder

/-- The affine map from spectral coordinate to the completed-zeta
coordinate intertwines reflection with `s ↦ 1 - s`. -/
@[simp]
theorem completedSpectralCoordinate_neg (z : ℂ) :
    completedSpectralCoordinate (-z) =
      1 - completedSpectralCoordinate z := by
  unfold completedSpectralCoordinate
  ring

/-- The two spectral-coordinate maps are inverse affine transformations. -/
@[simp]
theorem completedSpectralCoordinate_zetaSpectralCoordinate (s : ℂ) :
    completedSpectralCoordinate (zetaSpectralCoordinate s) = s := by
  unfold completedSpectralCoordinate zetaSpectralCoordinate
  calc
    1 / 2 + Complex.I * (-Complex.I * (s - (1 / 2 : ℝ))) =
        1 / 2 + (s - (1 / 2 : ℝ)) := by
      rw [← mul_assoc]
      simp
    _ = s := by push_cast; ring

/-- The inverse affine identity in the other direction. -/
@[simp]
theorem zetaSpectralCoordinate_completedSpectralCoordinate (z : ℂ) :
    zetaSpectralCoordinate (completedSpectralCoordinate z) = z := by
  unfold completedSpectralCoordinate zetaSpectralCoordinate
  rw [show (1 / 2 : ℂ) + Complex.I * z - (1 / 2 : ℝ) =
      Complex.I * z by
    push_cast
    ring]
  rw [← mul_assoc]
  simp

/-- The even entire Gaussian is even in its complex spectral argument. -/
@[simp]
theorem complexSymmetricGaussian_neg_point (ε t : ℝ) (z : ℂ) :
    complexSymmetricGaussian ε t (-z) =
      complexSymmetricGaussian ε t z := by
  unfold complexSymmetricGaussian
  rw [← complexTranslatedGaussian_neg_center ε t z,
    ← complexTranslatedGaussian_neg_center ε (-t) z]
  simp only [neg_neg, add_comm]

/-- Negative logarithmic derivative of xi in spectral coordinates. -/
def xiSpectralNegativeLogDerivative (z : ℂ) : ℂ :=
  -deriv riemannXi (completedSpectralCoordinate z) /
    riemannXi (completedSpectralCoordinate z)

/-- The xi negative logarithmic derivative is odd in spectral coordinates. -/
@[simp]
theorem xiSpectralNegativeLogDerivative_neg (z : ℂ) :
    xiSpectralNegativeLogDerivative (-z) =
      -xiSpectralNegativeLogDerivative z := by
  unfold xiSpectralNegativeLogDerivative
  rw [completedSpectralCoordinate_neg, deriv_riemannXi_one_sub,
    riemannXi_one_sub]
  ring

/-- Gaussian-weighted xi logarithmic derivative in spectral coordinates. -/
def gaussianXiSpectralIntegrand (ε t : ℝ) (z : ℂ) : ℂ :=
  complexSymmetricGaussian ε t z * xiSpectralNegativeLogDerivative z

/-- The complete spectral integrand is odd. -/
@[simp]
theorem gaussianXiSpectralIntegrand_neg (ε t : ℝ) (z : ℂ) :
    gaussianXiSpectralIntegrand ε t (-z) =
      -gaussianXiSpectralIntegrand ε t z := by
  simp [gaussianXiSpectralIntegrand]

/-! ## Multiplicity-aware local residues -/

/-- Xi viewed as an entire function of the spectral coordinate. -/
def riemannXiSpectral (z : ℂ) : ℂ :=
  riemannXi (completedSpectralCoordinate z)

lemma hasDerivAt_completedSpectralCoordinate (z : ℂ) :
    HasDerivAt completedSpectralCoordinate Complex.I z := by
  unfold completedSpectralCoordinate
  simpa only [mul_one] using
    (hasDerivAt_const_mul (x := z) Complex.I).const_add (1 / 2 : ℂ)

theorem differentiable_riemannXiSpectral :
    Differentiable ℂ riemannXiSpectral := by
  intro z
  unfold riemannXiSpectral
  exact (differentiable_riemannXi
      (completedSpectralCoordinate z)).comp z
    (hasDerivAt_completedSpectralCoordinate z).differentiableAt

theorem analyticAt_riemannXiSpectral (z : ℂ) :
    AnalyticAt ℂ riemannXiSpectral z :=
  differentiable_riemannXiSpectral.analyticAt z

/-- The zeros of spectral xi are precisely the affine images of the
nontrivial zeta zeros. -/
theorem riemannXiSpectral_eq_zero_iff_isNontrivialZetaZero (z : ℂ) :
    riemannXiSpectral z = 0 ↔
      IsNontrivialZetaZero (completedSpectralCoordinate z) := by
  exact riemannXi_eq_zero_iff_isNontrivialZetaZero
    (completedSpectralCoordinate z)

theorem riemannXiSpectral_eq_zero_iff_exists_zetaZero (z : ℂ) :
    riemannXiSpectral z = 0 ↔
      ∃ ρ : NontrivialZetaZero,
        z = zetaSpectralCoordinate ρ.1 := by
  constructor
  · intro hz
    let ρ : NontrivialZetaZero :=
      ⟨completedSpectralCoordinate z,
        (riemannXiSpectral_eq_zero_iff_isNontrivialZetaZero z).mp hz⟩
    exact ⟨ρ, (zetaSpectralCoordinate_completedSpectralCoordinate z).symm⟩
  · rintro ⟨ρ, rfl⟩
    unfold riemannXiSpectral
    rw [completedSpectralCoordinate_zetaSpectralCoordinate]
    exact riemannXi_eq_zero_of_isNontrivialZetaZero ρ.2

/-- Spectral xi zeros and nontrivial zeta zeros are canonically the same
discrete divisor. -/
noncomputable def riemannXiSpectralZeroEquiv :
    {z : ℂ // riemannXiSpectral z = 0} ≃ NontrivialZetaZero where
  toFun z :=
    ⟨completedSpectralCoordinate z.1,
      (riemannXiSpectral_eq_zero_iff_isNontrivialZetaZero z.1).mp z.2⟩
  invFun ρ :=
    ⟨zetaSpectralCoordinate ρ.1,
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr
        ⟨ρ, rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact zetaSpectralCoordinate_completedSpectralCoordinate z.1
  right_inv ρ := by
    apply Subtype.ext
    exact completedSpectralCoordinate_zetaSpectralCoordinate ρ.1

/-! ## Finite spectral windows -/

/-- There are only finitely many distinct zeta zeros whose spectral real
coordinate lies in a bounded interval. -/
theorem spectralZetaZeroWindowSet_finite
    {T : ℝ} (hT : 0 ≤ T) :
    {ρ : NontrivialZetaZero |
      |(zetaSpectralCoordinate ρ.1).re| ≤ T}.Finite := by
  let B : Set ℂ :=
    Metric.closedBall (0 : ℂ) (T + 1) ∩ nontrivialZetaZeroSet
  have hB : B.Finite := by
    exact IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) (T + 1))
  have hpre :
      ((fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⁻¹' B).Finite :=
    hB.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  change (ρ.1 : ℂ) ∈ B
  refine ⟨?_, ρ.2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm := Complex.norm_le_abs_re_add_abs_im ρ.1
  have hre : |ρ.1.re| < 1 := by
    rw [abs_of_pos (NontrivialZetaZero.zero_lt_re ρ)]
    exact NontrivialZetaZero.re_lt_one ρ
  have him : |ρ.1.im| ≤ T := by
    change |(zetaSpectralCoordinate ρ.1).re| ≤ T at hρ
    simpa only [zetaSpectralCoordinate_re] using hρ
  linarith

/-- The finite set of distinct zeta zeros in the symmetric spectral window
`|Re z| ≤ max T 0`. -/
noncomputable def spectralZetaZeroWindow
    (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindowSet_finite
    (T := max T 0) (le_max_right T 0)).toFinset

@[simp]
theorem mem_spectralZetaZeroWindow
    {T : ℝ} (hT : 0 ≤ T) (ρ : NontrivialZetaZero) :
    ρ ∈ spectralZetaZeroWindow T ↔
      |(zetaSpectralCoordinate ρ.1).re| ≤ T := by
  unfold spectralZetaZeroWindow
  rw [Set.Finite.mem_toFinset]
  change |(zetaSpectralCoordinate ρ.1).re| ≤ max T 0 ↔ _
  rw [max_eq_left hT]

/-- The corresponding finite set of points in the spectral plane. -/
noncomputable def spectralXiZeroWindow (T : ℝ) : Finset ℂ :=
  (spectralZetaZeroWindow T).image
    (fun ρ => zetaSpectralCoordinate ρ.1)

theorem mem_spectralXiZeroWindow_iff
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    z ∈ spectralXiZeroWindow T ↔
      riemannXiSpectral z = 0 ∧ |z.re| ≤ T := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
    constructor
    · exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr
        ⟨ρ, rfl⟩
    · exact (mem_spectralZetaZeroWindow hT ρ).mp hρ
  · rintro ⟨hz, hzT⟩
    rcases (riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mp hz with
      ⟨ρ, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨ρ, (mem_spectralZetaZeroWindow hT ρ).mpr hzT, rfl⟩

@[simp]
theorem deriv_riemannXiSpectral (z : ℂ) :
    deriv riemannXiSpectral z =
      Complex.I * deriv riemannXi (completedSpectralCoordinate z) := by
  change deriv (riemannXi ∘ completedSpectralCoordinate) z = _
  simpa only [mul_comm] using
    ((differentiable_riemannXi
      (completedSpectralCoordinate z)).hasDerivAt.comp z
      (hasDerivAt_completedSpectralCoordinate z)).deriv

/-- The spectral negative logarithmic derivative is `I` times the ordinary
logarithmic derivative of spectral xi.  This records the Jacobian that
determines the residue sign. -/
theorem xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv (z : ℂ) :
    xiSpectralNegativeLogDerivative z =
      Complex.I * logDeriv riemannXiSpectral z := by
  unfold xiSpectralNegativeLogDerivative
  change
    -deriv riemannXi (completedSpectralCoordinate z) /
        riemannXi (completedSpectralCoordinate z) =
      Complex.I *
        (deriv riemannXiSpectral z / riemannXiSpectral z)
  rw [deriv_riemannXiSpectral]
  unfold riemannXiSpectral
  rw [div_eq_mul_inv]
  calc
    -deriv riemannXi (completedSpectralCoordinate z) *
          (riemannXi (completedSpectralCoordinate z))⁻¹ =
        Complex.I ^ 2 * deriv riemannXi (completedSpectralCoordinate z) *
          (riemannXi (completedSpectralCoordinate z))⁻¹ := by
      rw [Complex.I_sq]
      ring
    _ = Complex.I *
          (Complex.I * deriv riemannXi (completedSpectralCoordinate z) *
            (riemannXi (completedSpectralCoordinate z))⁻¹) := by ring

/-- General multiplicity form of the logarithmic-residue limit.  It also
covers nonzeros, where the analytic order and the limit are both zero. -/
theorem AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    Tendsto
      (fun z => (z - a) * logDeriv f z)
      (𝓝[≠] a)
      (𝓝 (analyticOrderNatAt f a : ℂ)) := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    hf.analyticOrderAt_ne_top.mp hfinite
  let m : ℕ := analyticOrderNatAt f a
  have hfactor' : f =ᶠ[𝓝 a]
      fun z => (z - a) ^ m * g z := by
    simpa only [m, smul_eq_mul] using hfactor
  have hlogFactor := logDeriv_congr_nhds hfactor'
  have hg_ne : ∀ᶠ z in 𝓝 a, g z ≠ 0 :=
    hg.continuousAt.eventually_ne hg0
  have heq : ∀ᶠ z in 𝓝[≠] a,
      (z - a) * logDeriv f z =
        (m : ℂ) + (z - a) * logDeriv g z := by
    filter_upwards
      [hlogFactor.filter_mono nhdsWithin_le_nhds,
        hg_ne.filter_mono nhdsWithin_le_nhds,
        hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hzlog hgz hzAnalytic (hza : z ≠ a)
    have hza0 : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [hzlog]
    rw [logDeriv_mul (f := fun w : ℂ => (w - a) ^ m) (g := g) z
      (pow_ne_zero m hza0) hgz (by fun_prop) hzAnalytic.differentiableAt]
    rw [logDeriv_fun_pow (f := fun w : ℂ => w - a) (by fun_prop) m]
    have hlinear : logDeriv (fun w : ℂ => w - a) z = 1 / (z - a) := by
      simp [logDeriv_apply, hza0]
    rw [hlinear]
    field_simp [hza0]
  have hloggAnalytic : AnalyticAt ℂ (logDeriv g) a := by
    simpa only [logDeriv] using hg.deriv.div hg hg0
  have hsub : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 0) := by
    have hfull : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 (a - a)) :=
      Filter.tendsto_id.sub tendsto_const_nhds
    simpa only [sub_self] using hfull.mono_left nhdsWithin_le_nhds
  have hlogg : Tendsto (logDeriv g) (𝓝[≠] a)
      (𝓝 (logDeriv g a)) :=
    hloggAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit : Tendsto
      (fun z => (m : ℂ) + (z - a) * logDeriv g z)
      (𝓝[≠] a) (𝓝 (m : ℂ)) := by
    simpa using tendsto_const_nhds.add (hsub.mul hlogg)
  exact hlimit.congr' (by
    filter_upwards [heq] with z hz
    exact hz.symm)

/-- A logarithmic derivative is locally its analytic multiplicity divided
by `z - a`, plus an analytic remainder.  This is the removable-remainder
form needed for a finite residue theorem. -/
theorem AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h a ∧
      logDeriv f =ᶠ[𝓝[≠] a]
        fun z => (analyticOrderNatAt f a : ℂ) / (z - a) + h z := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    hf.analyticOrderAt_ne_top.mp hfinite
  let m : ℕ := analyticOrderNatAt f a
  have hfactor' : f =ᶠ[𝓝 a]
      fun z => (z - a) ^ m * g z := by
    simpa only [m, smul_eq_mul] using hfactor
  have hlogFactor := logDeriv_congr_nhds hfactor'
  have hg_ne : ∀ᶠ z in 𝓝 a, g z ≠ 0 :=
    hg.continuousAt.eventually_ne hg0
  have hloggAnalytic : AnalyticAt ℂ (logDeriv g) a := by
    simpa only [logDeriv] using hg.deriv.div hg hg0
  refine ⟨logDeriv g, hloggAnalytic, ?_⟩
  filter_upwards
    [hlogFactor.filter_mono nhdsWithin_le_nhds,
      hg_ne.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hzlog hgz hzAnalytic (hza : z ≠ a)
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr hza
  rw [hzlog]
  rw [logDeriv_mul (f := fun w : ℂ => (w - a) ^ m) (g := g) z
    (pow_ne_zero m hza0) hgz (by fun_prop) hzAnalytic.differentiableAt]
  rw [logDeriv_fun_pow (f := fun w : ℂ => w - a) (by fun_prop) m]
  have hlinear : logDeriv (fun w : ℂ => w - a) z = 1 / (z - a) := by
    simp [logDeriv_apply]
  rw [hlinear]
  change (m : ℂ) * (1 / (z - a)) + logDeriv g z =
    (m : ℂ) / (z - a) + logDeriv g z
  simp only [div_eq_mul_inv, one_mul]

/-! ## Finite removable patching -/

/-- Updating a function by the value of a local analytic model removes a
singularity whenever the two functions agree in a punctured neighborhood. -/
theorem analyticAt_update_of_eventuallyEq_nhdsNE
    {f h : ℂ → ℂ} {a : ℂ}
    (hh : AnalyticAt ℂ h a) (heq : f =ᶠ[𝓝[≠] a] h) :
    AnalyticAt ℂ (Function.update f a (h a)) a := by
  apply hh.congr
  have heq' : h =ᶠ[𝓝[≠] a] f := heq.symm
  rw [Filter.EventuallyEq] at heq' ⊢
  obtain ⟨s, hs, hsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp heq'
  filter_upwards [hs] with z hz
  by_cases hza : z = a
  · subst z
    simp
  · have hzmem : z ∈ s ∩ {a}ᶜ := by
      exact ⟨hz, by simpa using hza⟩
    simpa [Function.update_of_ne hza] using hsub hzmem

lemma update_eventuallyEq_of_ne
    {f : ℂ → ℂ} {a b v : ℂ} (hba : b ≠ a) :
    Function.update f a v =ᶠ[𝓝 b] f := by
  filter_upwards [isOpen_ne.mem_nhds hba] with z hz
  simp [Function.update_of_ne hz]

/-- Pointwise finite sums of analytic functions are analytic.  This
eta-expanded form avoids coercion ambiguity between function-space and
pointwise sums. -/
theorem analyticAt_finset_sum_apply
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℂ → ℂ) {z : ℂ}
    (hf : ∀ a ∈ S, AnalyticAt ℂ (f a) z) :
    AnalyticAt ℂ (fun w => ∑ a ∈ S, f a w) z := by
  induction S using Finset.induction_on with
  | empty =>
      have hzero : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z := analyticAt_const
      simpa using hzero
  | @insert a S ha ih =>
      rw [show (fun w => ∑ x ∈ insert a S, f x w) =
          fun w => f a w + ∑ x ∈ S, f x w by
        funext w
        rw [Finset.sum_insert ha]]
      exact (hf a (Finset.mem_insert_self a S)).add
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- Finitely many locally removable singularities can be patched
simultaneously without changing the function away from that finite set. -/
theorem exists_analyticAtOn_of_finite_removable
    (U : Set ℂ) (S : Finset ℂ) (f : ℂ → ℂ)
    (hSU : ∀ a ∈ S, a ∈ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hrem : ∀ a ∈ S,
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ f =ᶠ[𝓝[≠] a] h) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ U, AnalyticAt ℂ F z) ∧
      (∀ z ∉ S, F z = f z) := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨f, fun z hz => hoff z hz (by simp), by simp⟩
  | @insert a S ha ih =>
      obtain ⟨h, hh, hfh⟩ := hrem a (by simp)
      let f₁ : ℂ → ℂ := Function.update f a (h a)
      have hf₁a : AnalyticAt ℂ f₁ a := by
        exact analyticAt_update_of_eventuallyEq_nhdsNE hh hfh
      have hf₁off : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f₁ z := by
        intro z hzU hzS
        by_cases hza : z = a
        · simpa [hza] using hf₁a
        · have hzf : AnalyticAt ℂ f z :=
            hoff z hzU (by simpa [hza, hzS])
          exact hzf.congr (update_eventuallyEq_of_ne hza).symm
      have hf₁rem : ∀ b ∈ S,
          ∃ k : ℂ → ℂ, AnalyticAt ℂ k b ∧ f₁ =ᶠ[𝓝[≠] b] k := by
        intro b hb
        obtain ⟨k, hk, hfk⟩ := hrem b (by simp [hb])
        have hba : b ≠ a := by
          intro hba
          subst b
          exact ha hb
        refine ⟨k, hk, ?_⟩
        exact ((update_eventuallyEq_of_ne hba).filter_mono
          nhdsWithin_le_nhds).trans hfk
      obtain ⟨F, hFU, hFoff⟩ := ih f₁
        (fun b hb => hSU b (Finset.mem_insert_of_mem hb)) hf₁off hf₁rem
      refine ⟨F, hFU, ?_⟩
      intro z hz
      have hzparts : z ≠ a ∧ z ∉ S := by
        simpa [Finset.mem_insert] using hz
      have hzS : z ∉ S := hzparts.2
      rw [hFoff z hzS]
      have hza : z ≠ a := hzparts.1
      simp [f₁, Function.update_of_ne hza]

/-- Spectral xi has the same analytic multiplicity at the spectral image of
a zeta zero as xi has at that zero. -/
theorem analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannXiSpectral (zetaSpectralCoordinate ρ.1) =
      analyticOrderAt riemannXi ρ.1 := by
  let zρ := zetaSpectralCoordinate ρ.1
  have hcoord : AnalyticAt ℂ completedSpectralCoordinate zρ := by
    unfold completedSpectralCoordinate
    fun_prop
  have hcoordValue : completedSpectralCoordinate zρ = ρ.1 := by
    exact completedSpectralCoordinate_zetaSpectralCoordinate ρ.1
  have hcoordDeriv : deriv completedSpectralCoordinate zρ ≠ 0 := by
    rw [(hasDerivAt_completedSpectralCoordinate zρ).deriv]
    exact Complex.I_ne_zero
  change analyticOrderAt (riemannXi ∘ completedSpectralCoordinate) zρ =
    analyticOrderAt riemannXi ρ.1
  rw [analyticOrderAt_comp_of_deriv_ne_zero hcoord hcoordDeriv,
    hcoordValue]

theorem analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate
    (ρ : NontrivialZetaZero) :
    analyticOrderNatAt riemannXiSpectral (zetaSpectralCoordinate ρ.1) =
      analyticZetaZeroMultiplicity ρ := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
    analyticOrderAt_riemannXi_eq_riemannZeta]
  rfl

/-- At a nontrivial zero, the local spectral logarithmic residue is exactly
the genuine analytic zeta multiplicity. -/
theorem tendsto_zetaSpectralCoordinate_mul_logDeriv_riemannXiSpectral
    (ρ : NontrivialZetaZero) :
    Tendsto
      (fun z =>
        (z - zetaSpectralCoordinate ρ.1) *
          logDeriv riemannXiSpectral z)
      (𝓝[≠] zetaSpectralCoordinate ρ.1)
      (𝓝 (analyticZetaZeroMultiplicity ρ : ℂ)) := by
  have hfinite :
      analyticOrderAt riemannXiSpectral
          (zetaSpectralCoordinate ρ.1) ≠ ⊤ := by
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
  have hlocal :=
    AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
      (analyticAt_riemannXiSpectral (zetaSpectralCoordinate ρ.1)) hfinite
  simpa only
      [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
    hlocal

/-- Local principal-part decomposition at a spectral xi zero, with the
true zeta multiplicity. -/
theorem exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic
    (ρ : NontrivialZetaZero) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate ρ.1) ∧
      logDeriv riemannXiSpectral =ᶠ[𝓝[≠] zetaSpectralCoordinate ρ.1]
        fun z =>
          (analyticZetaZeroMultiplicity ρ : ℂ) /
              (z - zetaSpectralCoordinate ρ.1) + h z := by
  have hfinite :
      analyticOrderAt riemannXiSpectral
          (zetaSpectralCoordinate ρ.1) ≠ ⊤ := by
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
  have hlocal :=
    AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic
      (analyticAt_riemannXiSpectral (zetaSpectralCoordinate ρ.1)) hfinite
  simpa only
      [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
    hlocal

/-- The residue coefficient of the negative xi logarithmic derivative in
spectral coordinates.  The factor `I` is the affine-coordinate Jacobian. -/
theorem tendsto_zetaSpectralCoordinate_mul_xiSpectralNegativeLogDerivative
    (ρ : NontrivialZetaZero) :
    Tendsto
      (fun z =>
        (z - zetaSpectralCoordinate ρ.1) *
          xiSpectralNegativeLogDerivative z)
      (𝓝[≠] zetaSpectralCoordinate ρ.1)
      (𝓝 (Complex.I * (analyticZetaZeroMultiplicity ρ : ℂ))) := by
  have hlocal :=
    tendsto_zetaSpectralCoordinate_mul_logDeriv_riemannXiSpectral ρ
  have hI : Tendsto (fun _ : ℂ => Complex.I)
      (𝓝[≠] zetaSpectralCoordinate ρ.1) (𝓝 Complex.I) :=
    tendsto_const_nhds
  have hscaled := hI.mul hlocal
  convert hscaled using 1
  · funext z
    rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv]
    ring

theorem differentiable_complexSymmetricGaussian (ε t : ℝ) :
    Differentiable ℂ (complexSymmetricGaussian ε t) := by
  unfold complexSymmetricGaussian complexTranslatedGaussian
  fun_prop

/-- The genuine local residue coefficient of the Gaussian-weighted xi
contour integrand. -/
def gaussianXiSpectralResidue
    (ε t : ℝ) (ρ : NontrivialZetaZero) : ℂ :=
  complexSymmetricGaussian ε t (zetaSpectralCoordinate ρ.1) *
    (Complex.I * (analyticZetaZeroMultiplicity ρ : ℂ))

/-- Constant-numerator principal part attached to one spectral xi zero. -/
def gaussianXiSpectralPrincipalPart
    (ε t : ℝ) (ρ : NontrivialZetaZero) (z : ℂ) : ℂ :=
  gaussianXiSpectralResidue ε t ρ /
    (z - zetaSpectralCoordinate ρ.1)

/-- After subtracting the constant-numerator principal part at one zero,
the Gaussian xi integrand has a local analytic continuation. -/
theorem exists_gaussianXiSpectralIntegrand_eq_principalPart_add_analytic
    (ε t : ℝ) (ρ : NontrivialZetaZero) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate ρ.1) ∧
      gaussianXiSpectralIntegrand ε t =ᶠ[𝓝[≠] zetaSpectralCoordinate ρ.1]
        fun z => gaussianXiSpectralPrincipalPart ε t ρ z + h z := by
  obtain ⟨k, hkAnalytic, hk⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic ρ
  let a : ℂ := zetaSpectralCoordinate ρ.1
  let m : ℂ := (analyticZetaZeroMultiplicity ρ : ℂ)
  let H : ℂ → ℂ := complexSymmetricGaussian ε t
  let h : ℂ → ℂ := fun z =>
    H z * (Complex.I * k z) +
      (Complex.I * m) * dslope H a z
  have hHdiff : DifferentiableOn ℂ H Set.univ := by
    intro z hz
    exact (differentiable_complexSymmetricGaussian ε t z).differentiableWithinAt
  have hSlopeDiff : DifferentiableOn ℂ (dslope H a) Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2 hHdiff
  have hhAnalytic : AnalyticAt ℂ h a := by
    have hHAnalytic : AnalyticAt ℂ H a :=
      (differentiable_complexSymmetricGaussian ε t).analyticAt a
    have hSlopeAnalytic : AnalyticAt ℂ (dslope H a) a :=
      (differentiableOn_univ.mp hSlopeDiff).analyticAt a
    unfold h
    exact (hHAnalytic.mul (analyticAt_const.mul hkAnalytic)).add
      (analyticAt_const.mul hSlopeAnalytic)
  refine ⟨h, hhAnalytic, ?_⟩
  filter_upwards [hk, self_mem_nhdsWithin] with z hlog (hza : z ≠ a)
  unfold gaussianXiSpectralIntegrand
  rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv, hlog]
  change
    H z * (Complex.I * (m / (z - a) + k z)) =
      gaussianXiSpectralPrincipalPart ε t ρ z +
        (H z * (Complex.I * k z) +
          (Complex.I * m) * dslope H a z)
  rw [dslope_of_ne H hza, slope_def_field]
  unfold gaussianXiSpectralPrincipalPart gaussianXiSpectralResidue
  change
    H z * (Complex.I * (m / (z - a) + k z)) =
      H a * (Complex.I * m) / (z - a) +
        (H z * (Complex.I * k z) +
          (Complex.I * m) * ((H z - H a) / (z - a)))
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr hza
  field_simp [hza0]
  ring

/-- Away from its zero set, the spectral logarithmic derivative of xi is
analytic. -/
theorem analyticAt_logDeriv_riemannXiSpectral_of_ne
    {z : ℂ} (hz : riemannXiSpectral z ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannXiSpectral) z := by
  have hxi := analyticAt_riemannXiSpectral z
  simpa only [logDeriv] using hxi.deriv.div hxi hz

theorem analyticAt_xiSpectralNegativeLogDerivative_of_ne
    {z : ℂ} (hz : riemannXiSpectral z ≠ 0) :
    AnalyticAt ℂ xiSpectralNegativeLogDerivative z := by
  have hmodel : AnalyticAt ℂ
      (fun w => Complex.I * logDeriv riemannXiSpectral w) z :=
    analyticAt_const.mul (analyticAt_logDeriv_riemannXiSpectral_of_ne hz)
  exact hmodel.congr (Filter.Eventually.of_forall fun w =>
    (xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv w).symm)

theorem analyticAt_gaussianXiSpectralIntegrand_of_ne
    (ε t : ℝ) {z : ℂ} (hz : riemannXiSpectral z ≠ 0) :
    AnalyticAt ℂ (gaussianXiSpectralIntegrand ε t) z := by
  unfold gaussianXiSpectralIntegrand
  exact ((differentiable_complexSymmetricGaussian ε t).analyticAt z).mul
    (analyticAt_xiSpectralNegativeLogDerivative_of_ne hz)

theorem analyticAt_gaussianXiSpectralPrincipalPart_of_ne
    (ε t : ℝ) (ρ : NontrivialZetaZero) {z : ℂ}
    (hz : z ≠ zetaSpectralCoordinate ρ.1) :
    AnalyticAt ℂ (gaussianXiSpectralPrincipalPart ε t ρ) z := by
  unfold gaussianXiSpectralPrincipalPart
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hz)

/-- Sum of all constant-numerator principal parts in a finite spectral
window. -/
def gaussianXiWindowPrincipalSum
    (ε t T : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ spectralZetaZeroWindow T,
    gaussianXiSpectralPrincipalPart ε t ρ z

theorem analyticAt_gaussianXiWindowPrincipalSum_of_not_mem
    (ε t T : ℝ) {z : ℂ} (hz : z ∉ spectralXiZeroWindow T) :
    AnalyticAt ℂ (gaussianXiWindowPrincipalSum ε t T) z := by
  unfold gaussianXiWindowPrincipalSum
  apply analyticAt_finset_sum_apply
  intro ρ hρ
  apply analyticAt_gaussianXiSpectralPrincipalPart_of_ne
  intro heq
  apply hz
  apply Finset.mem_image.mpr
  exact ⟨ρ, hρ, heq.symm⟩

/-- The unpatched finite-window remainder.  It is analytic away from the
finite zero set and has removable singularities at every point of that set. -/
def gaussianXiWindowRawRemainder
    (ε t T : ℝ) (z : ℂ) : ℂ :=
  gaussianXiSpectralIntegrand ε t z -
    gaussianXiWindowPrincipalSum ε t T z

theorem analyticAt_gaussianXiWindowRawRemainder_of_not_mem
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hzRe : |z.re| ≤ T) (hz : z ∉ spectralXiZeroWindow T) :
    AnalyticAt ℂ (gaussianXiWindowRawRemainder ε t T) z := by
  have hxi : riemannXiSpectral z ≠ 0 := by
    intro hzero
    exact hz ((mem_spectralXiZeroWindow_iff hT z).mpr ⟨hzero, hzRe⟩)
  unfold gaussianXiWindowRawRemainder gaussianXiWindowPrincipalSum
  apply (analyticAt_gaussianXiSpectralIntegrand_of_ne ε t hxi).sub
  have hterm (ρ : NontrivialZetaZero)
      (hρ : ρ ∈ spectralZetaZeroWindow T) :
      AnalyticAt ℂ (gaussianXiSpectralPrincipalPart ε t ρ) z := by
    apply analyticAt_gaussianXiSpectralPrincipalPart_of_ne
    intro hzr
    apply hz
    apply Finset.mem_image.mpr
    exact ⟨ρ, hρ, hzr.symm⟩
  exact analyticAt_finset_sum_apply
    (spectralZetaZeroWindow T)
    (fun ρ => gaussianXiSpectralPrincipalPart ε t ρ) hterm

/-- Closed rectangle used for the safe-line xi contour. -/
def spectralContourRectangle (T : ℝ) : Set ℂ :=
  {z | |z.re| ≤ T ∧ |z.im| ≤ 1}

/-- Spectral xi cannot vanish at a point whose imaginary part is outside
the open critical strip `|Im z| < 1/2`. -/
theorem riemannXiSpectral_ne_zero_of_half_le_abs_im
    {z : ℂ} (hz : (1 / 2 : ℝ) ≤ |z.im|) :
    riemannXiSpectral z ≠ 0 := by
  intro hzero
  rcases (riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mp hzero with
    ⟨ρ, heq⟩
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half ρ
  rw [← heq] at him
  exact (not_lt_of_ge hz) him

/-- A prescribed vertical spectral line is zero-free if its absolute real
coordinate differs from that of every nontrivial zeta zero. -/
theorem riemannXiSpectral_ne_zero_of_abs_re_ne
    {T : ℝ}
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T)
    {z : ℂ} (hz : |z.re| = T) :
    riemannXiSpectral z ≠ 0 := by
  intro hzero
  rcases (riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mp hzero with
    ⟨ρ, heq⟩
  apply hboundary ρ
  rw [← heq]
  exact hz

/-- The two horizontal safe lines do not meet the spectral xi zero set:
all nontrivial zeta zeros lie strictly between them. -/
theorem lower_safeLine_not_mem_spectralXiZeroWindow
    (T x : ℝ) :
    ((x : ℂ) - Complex.I) ∉ spectralXiZeroWindow T := by
  intro hz
  rcases Finset.mem_image.mp hz with ⟨ρ, hρ, heq⟩
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half ρ
  rw [heq] at him
  norm_num at him

theorem upper_safeLine_not_mem_spectralXiZeroWindow
    (T x : ℝ) :
    ((x : ℂ) + Complex.I) ∉ spectralXiZeroWindow T := by
  intro hz
  rcases Finset.mem_image.mp hz with ⟨ρ, hρ, heq⟩
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half ρ
  rw [heq] at him
  norm_num at him

/-- A symmetric vertical boundary is zero-free when its spectral abscissa
does not equal that of any nontrivial zeta zero. -/
theorem right_vertical_not_mem_spectralXiZeroWindow
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T)
    (y : ℝ) :
    ((T : ℂ) + (y : ℂ) * Complex.I) ∉ spectralXiZeroWindow T := by
  intro hz
  rcases Finset.mem_image.mp hz with ⟨ρ, hρ, heq⟩
  apply hboundary ρ
  rw [heq]
  simp [abs_of_nonneg hT]

theorem left_vertical_not_mem_spectralXiZeroWindow
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T)
    (y : ℝ) :
    ((-T : ℂ) + (y : ℂ) * Complex.I) ∉ spectralXiZeroWindow T := by
  intro hz
  rcases Finset.mem_image.mp hz with ⟨ρ, hρ, heq⟩
  apply hboundary ρ
  rw [heq]
  simp [abs_of_nonneg hT]

theorem exists_gaussianXiWindowRawRemainder_eq_analyticAt
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (ρ : NontrivialZetaZero) (hρ : ρ ∈ spectralZetaZeroWindow T) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate ρ.1) ∧
      gaussianXiWindowRawRemainder ε t T =ᶠ[𝓝[≠] zetaSpectralCoordinate ρ.1] h := by
  obtain ⟨k, hk, horiginal⟩ :=
    exists_gaussianXiSpectralIntegrand_eq_principalPart_add_analytic ε t ρ
  let W := spectralZetaZeroWindow T
  let h : ℂ → ℂ := fun z =>
    k z - ∑ σ ∈ W.erase ρ,
      gaussianXiSpectralPrincipalPart ε t σ z
  have hother : AnalyticAt ℂ
      (fun z => ∑ σ ∈ W.erase ρ,
        gaussianXiSpectralPrincipalPart ε t σ z)
      (zetaSpectralCoordinate ρ.1) := by
    have hterm (σ : NontrivialZetaZero) (hσ : σ ∈ W.erase ρ) :
        AnalyticAt ℂ (gaussianXiSpectralPrincipalPart ε t σ)
          (zetaSpectralCoordinate ρ.1) := by
      apply analyticAt_gaussianXiSpectralPrincipalPart_of_ne
      intro heq
      have hval : ρ.1 = σ.1 :=
        zetaSpectralCoordinate_injective heq
      have hrs : ρ = σ := Subtype.ext hval
      exact (Finset.mem_erase.mp hσ).1 hrs.symm
    exact analyticAt_finset_sum_apply (W.erase ρ)
      (fun σ => gaussianXiSpectralPrincipalPart ε t σ) hterm
  have hh : AnalyticAt ℂ h (zetaSpectralCoordinate ρ.1) := by
    unfold h
    exact hk.sub hother
  refine ⟨h, hh, ?_⟩
  filter_upwards [horiginal] with z hz
  unfold gaussianXiWindowRawRemainder gaussianXiWindowPrincipalSum h
  rw [hz]
  have hsum := W.add_sum_erase
    (fun σ => gaussianXiSpectralPrincipalPart ε t σ z) hρ
  rw [← hsum]
  ring

/-- The finite-window xi remainder admits a holomorphic representative on
the whole contour rectangle, equal to the raw remainder away from its
finite zero set. -/
theorem exists_gaussianXiWindowRegularization
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ spectralContourRectangle T, AnalyticAt ℂ F z) ∧
      (∀ z ∉ spectralXiZeroWindow T,
        F z = gaussianXiWindowRawRemainder ε t T z) := by
  apply exists_analyticAtOn_of_finite_removable
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
    constructor
    · exact (mem_spectralZetaZeroWindow hT ρ).mp hρ
    · exact (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half ρ).le.trans
        (by norm_num)
  · intro z hzU hz
    exact analyticAt_gaussianXiWindowRawRemainder_of_not_mem
      ε t hT hzU.1 hz
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
    exact exists_gaussianXiWindowRawRemainder_eq_analyticAt ε t hT ρ hρ

/-- Counterclockwise integral over the rectangle with horizontal safe
lines `Im z = ±1` and vertical sides `Re z = ±T`. -/
def spectralRectangleBoundaryIntegral (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in -T..T, f ((x : ℂ) - Complex.I)) -
    (∫ x : ℝ in -T..T, f ((x : ℂ) + Complex.I)) +
    Complex.I * (∫ y : ℝ in (-1 : ℝ)..1,
      f ((T : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in (-1 : ℝ)..1,
      f ((-T : ℂ) + (y : ℂ) * Complex.I))

/-- Counterclockwise boundary integral of an arbitrary axis-parallel
rectangle `[l,r] × [b,u]`. -/
def rectangularBoundaryIntegral
    (l r b u : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in l..r, f ((x : ℂ) + (b : ℂ) * Complex.I)) -
    (∫ x : ℝ in l..r, f ((x : ℂ) + (u : ℂ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in b..u,
      f ((r : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in b..u,
      f ((l : ℂ) + (y : ℂ) * Complex.I))

theorem rectangularBoundaryIntegral_eq_zero_of_differentiableOn
    (l r b u : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f
      (Complex.Rectangle
        ((l : ℂ) + (b : ℂ) * Complex.I)
        ((r : ℂ) + (u : ℂ) * Complex.I))) :
    rectangularBoundaryIntegral l r b u f = 0 := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((l : ℂ) + (b : ℂ) * Complex.I)
      ((r : ℂ) + (u : ℂ) * Complex.I) hf
  simpa [rectangularBoundaryIntegral, sub_eq_add_neg] using hrect

/-- Subdividing a rectangle by a vertical line adds its two boundary
integrals; the artificial vertical sides cancel. -/
theorem rectangularBoundaryIntegral_split_re
    (l m r b u : ℝ) (f : ℂ → ℂ)
    (hb : Continuous (fun x : ℝ =>
      f ((x : ℂ) + (b : ℂ) * Complex.I)))
    (hu : Continuous (fun x : ℝ =>
      f ((x : ℂ) + (u : ℂ) * Complex.I))) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l m b u f +
        rectangularBoundaryIntegral m r b u f := by
  unfold rectangularBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hb.intervalIntegrable l m) (hb.intervalIntegrable m r),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable l m) (hu.intervalIntegrable m r)]
  ring

/-- Subdividing a rectangle by a horizontal line adds its two boundary
integrals; the artificial horizontal sides cancel. -/
theorem rectangularBoundaryIntegral_split_im
    (l r b m u : ℝ) (f : ℂ → ℂ)
    (hl : Continuous (fun y : ℝ =>
      f ((l : ℂ) + (y : ℂ) * Complex.I)))
    (hr : Continuous (fun y : ℝ =>
      f ((r : ℂ) + (y : ℂ) * Complex.I))) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l r b m f +
        rectangularBoundaryIntegral l r m u f := by
  unfold rectangularBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hr.intervalIntegrable b m) (hr.intervalIntegrable m u),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hl.intervalIntegrable b m) (hl.intervalIntegrable m u)]
  ring

lemma unitPrincipalKernel_horizontal
    (A : ℂ) (x : ℝ) :
    A / ((x : ℂ) - Complex.I) -
        A / ((x : ℂ) + Complex.I) =
      (2 * Complex.I * A) *
        (((1 / (1 + x ^ 2) : ℝ) : ℂ)) := by
  have hminus : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hplus : (x : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hreal : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hrealC : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hreal
  have hdenom : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast hreal
  push_cast
  field_simp [hminus, hplus, hrealC]
  ring_nf
  field_simp [hdenom]
  simp [pow_succ, Complex.I_sq]

lemma unitPrincipalKernel_vertical
    (A : ℂ) (y : ℝ) :
    Complex.I * (A / (1 + (y : ℂ) * Complex.I)) -
        Complex.I * (A / (-1 + (y : ℂ) * Complex.I)) =
      (2 * Complex.I * A) *
        (((1 / (1 + y ^ 2) : ℝ) : ℂ)) := by
  have hright : (1 : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hleft : (-1 : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hreal : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
  have hrealC : (((1 + y ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hreal
  have hdenom : (1 + (y : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast hreal
  have hright' : (1 : ℂ) + Complex.I * (y : ℂ) ≠ 0 := by
    simpa [mul_comm] using hright
  have hleft' : (-1 : ℂ) + Complex.I * (y : ℂ) ≠ 0 := by
    simpa [mul_comm] using hleft
  push_cast
  field_simp [hright, hleft, hright', hleft', hrealC]
  ring_nf
  rw [Complex.I_sq]
  field_simp [hdenom]
  ring

lemma integral_inv_one_add_sq_neg_one_one :
    (∫ x : ℝ in (-1 : ℝ)..1, (1 + x ^ 2)⁻¹) =
      Real.pi / 2 := by
  rw [integral_inv_one_add_sq, Real.arctan_neg, Real.arctan_one]
  ring

/-- Interval integrability of a function on all four parametrized sides of
the spectral rectangle. -/
def spectralRectangleBoundaryIntegrable (T : ℝ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) - Complex.I)) volume (-T) T ∧
    IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + Complex.I)) volume (-T) T ∧
    IntervalIntegrable
      (fun y : ℝ => f ((T : ℂ) + (y : ℂ) * Complex.I)) volume (-1) 1 ∧
    IntervalIntegrable
      (fun y : ℝ => f ((-T : ℂ) + (y : ℂ) * Complex.I)) volume (-1) 1

/-- Linearity of the rectangular boundary integral for a difference of
functions that are integrable on all four sides. -/
theorem spectralRectangleBoundaryIntegral_sub
    (T : ℝ) {f g : ℂ → ℂ}
    (hf : spectralRectangleBoundaryIntegrable T f)
    (hg : spectralRectangleBoundaryIntegrable T g) :
    spectralRectangleBoundaryIntegral T (fun z => f z - g z) =
      spectralRectangleBoundaryIntegral T f -
        spectralRectangleBoundaryIntegral T g := by
  rcases hf with ⟨hfl, hfu, hfr, hfleft⟩
  rcases hg with ⟨hgl, hgu, hgr, hgleft⟩
  unfold spectralRectangleBoundaryIntegral
  rw [intervalIntegral.integral_sub hfl hgl,
    intervalIntegral.integral_sub hfu hgu,
    intervalIntegral.integral_sub hfr hgr,
    intervalIntegral.integral_sub hfleft hgleft]
  ring

lemma continuous_comp_of_forall_analyticAt
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hf : ∀ x, AnalyticAt ℂ f (γ x)) :
    Continuous (fun x => f (γ x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hf x).continuousAt.comp hγ.continuousAt

theorem spectralRectangleBoundaryIntegrable_gaussianXiSpectralIntegrand
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T) :
    spectralRectangleBoundaryIntegrable T
      (gaussianXiSpectralIntegrand ε t) := by
  unfold spectralRectangleBoundaryIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiSpectralIntegrand ε t)
      (fun x : ℝ => (x : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    apply analyticAt_gaussianXiSpectralIntegrand_of_ne
    apply riemannXiSpectral_ne_zero_of_half_le_abs_im
    norm_num
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiSpectralIntegrand ε t)
      (fun x : ℝ => (x : ℂ) + Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    apply analyticAt_gaussianXiSpectralIntegrand_of_ne
    apply riemannXiSpectral_ne_zero_of_half_le_abs_im
    norm_num
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiSpectralIntegrand ε t)
      (fun y : ℝ => (T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    apply analyticAt_gaussianXiSpectralIntegrand_of_ne
    apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
    simp [abs_of_nonneg hT]
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiSpectralIntegrand ε t)
      (fun y : ℝ => (-T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    apply analyticAt_gaussianXiSpectralIntegrand_of_ne
    apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
    simp [abs_of_nonneg hT]

theorem spectralRectangleBoundaryIntegrable_gaussianXiWindowPrincipalSum
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T) :
    spectralRectangleBoundaryIntegrable T
      (gaussianXiWindowPrincipalSum ε t T) := by
  unfold spectralRectangleBoundaryIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiWindowPrincipalSum ε t T)
      (fun x : ℝ => (x : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact analyticAt_gaussianXiWindowPrincipalSum_of_not_mem ε t T
      (lower_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiWindowPrincipalSum ε t T)
      (fun x : ℝ => (x : ℂ) + Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact analyticAt_gaussianXiWindowPrincipalSum_of_not_mem ε t T
      (upper_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiWindowPrincipalSum ε t T)
      (fun y : ℝ => (T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact analyticAt_gaussianXiWindowPrincipalSum_of_not_mem ε t T
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  · apply (continuous_comp_of_forall_analyticAt
      (gaussianXiWindowPrincipalSum ε t T)
      (fun y : ℝ => (-T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact analyticAt_gaussianXiWindowPrincipalSum_of_not_mem ε t T
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)

/-- Finite-rectangle Cauchy identity after removing every spectral xi pole
in the window.  The vertical-boundary hypothesis merely says that the
chosen truncation height does not pass through a zeta zero. -/
theorem gaussianXiWindowRawRemainder_rectangle_identity
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
      (gaussianXiWindowRawRemainder ε t T) = 0 := by
  obtain ⟨F, hFanalytic, hFoff⟩ :=
    exists_gaussianXiWindowRegularization ε t hT
  have hdiff : DifferentiableOn ℂ F
      (Complex.Rectangle ((-T : ℂ) - Complex.I)
        ((T : ℂ) + Complex.I)) := by
    intro z hz
    apply (hFanalytic z ?_).differentiableAt.differentiableWithinAt
    constructor
    · have hre : z.re ∈ Set.uIcc (-T) T := by
        simpa using hz.1
      rw [uIcc_of_le (by linarith)] at hre
      exact (abs_le).2 hre
    · have him : z.im ∈ Set.uIcc (-1) 1 := by
        simpa using hz.2
      rw [uIcc_of_le (by norm_num)] at him
      exact (abs_le).2 him
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F ((-T : ℂ) - Complex.I) ((T : ℂ) + Complex.I) hdiff
  have hrectF : spectralRectangleBoundaryIntegral T F = 0 := by
    simpa [spectralRectangleBoundaryIntegral, sub_eq_add_neg] using hrect
  have hlower (x : ℝ) :
      F ((x : ℂ) - Complex.I) =
        gaussianXiWindowRawRemainder ε t T ((x : ℂ) - Complex.I) :=
    hFoff _ (lower_safeLine_not_mem_spectralXiZeroWindow T x)
  have hupper (x : ℝ) :
      F ((x : ℂ) + Complex.I) =
        gaussianXiWindowRawRemainder ε t T ((x : ℂ) + Complex.I) :=
    hFoff _ (upper_safeLine_not_mem_spectralXiZeroWindow T x)
  have hright (y : ℝ) :
      F ((T : ℂ) + (y : ℂ) * Complex.I) =
        gaussianXiWindowRawRemainder ε t T
          ((T : ℂ) + (y : ℂ) * Complex.I) :=
    hFoff _
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  have hleft (y : ℝ) :
      F ((-T : ℂ) + (y : ℂ) * Complex.I) =
        gaussianXiWindowRawRemainder ε t T
          ((-T : ℂ) + (y : ℂ) * Complex.I) :=
    hFoff _
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  unfold spectralRectangleBoundaryIntegral at hrectF ⊢
  simp_rw [hlower, hupper, hright, hleft] at hrectF
  exact hrectF

/-- The finite xi divisor identity: the contour integral of the original
Gaussian-weighted logarithmic derivative equals that of the sum of its
true multiplicity-weighted principal parts inside the rectangle. -/
theorem gaussianXiSpectralIntegrand_rectangle_eq_windowPrincipalSum
    (ε t : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ ρ : NontrivialZetaZero,
      |(zetaSpectralCoordinate ρ.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
        (gaussianXiSpectralIntegrand ε t) =
      spectralRectangleBoundaryIntegral T
        (gaussianXiWindowPrincipalSum ε t T) := by
  have hraw := gaussianXiWindowRawRemainder_rectangle_identity
    ε t hT hboundary
  have horiginal :=
    spectralRectangleBoundaryIntegrable_gaussianXiSpectralIntegrand
      ε t hT hboundary
  have hprincipal :=
    spectralRectangleBoundaryIntegrable_gaussianXiWindowPrincipalSum
      ε t hT hboundary
  have hsub := spectralRectangleBoundaryIntegral_sub T horiginal hprincipal
  change spectralRectangleBoundaryIntegral T
      (fun z => gaussianXiSpectralIntegrand ε t z -
        gaussianXiWindowPrincipalSum ε t T z) = 0 at hraw
  rw [hsub] at hraw
  exact sub_eq_zero.mp hraw

theorem tendsto_zetaSpectralCoordinate_mul_gaussianXiSpectralIntegrand
    (ε t : ℝ) (ρ : NontrivialZetaZero) :
    Tendsto
      (fun z =>
        (z - zetaSpectralCoordinate ρ.1) *
          gaussianXiSpectralIntegrand ε t z)
      (𝓝[≠] zetaSpectralCoordinate ρ.1)
      (𝓝 (gaussianXiSpectralResidue ε t ρ)) := by
  have hgaussian : Tendsto (complexSymmetricGaussian ε t)
      (𝓝[≠] zetaSpectralCoordinate ρ.1)
      (𝓝 (complexSymmetricGaussian ε t
        (zetaSpectralCoordinate ρ.1))) :=
    (differentiable_complexSymmetricGaussian ε t).continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hresidue :=
    tendsto_zetaSpectralCoordinate_mul_xiSpectralNegativeLogDerivative ρ
  have hproduct := hgaussian.mul hresidue
  convert hproduct using 1
  · funext z
    unfold gaussianXiSpectralIntegrand
    ring
  · rfl

lemma gaussianXiSpectralIntegrand_lower_safeLine
    (ε t x : ℝ) :
    gaussianXiSpectralIntegrand ε t ((x : ℂ) - Complex.I) =
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (x : ℂ))) := by
  unfold gaussianXiSpectralIntegrand xiSpectralNegativeLogDerivative
  rw [completedSpectralCoordinate_safeLine]

theorem integrable_gaussianXiSpectralIntegrand_lower_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ =>
      gaussianXiSpectralIntegrand ε t ((x : ℂ) - Complex.I)) := by
  simpa only [gaussianXiSpectralIntegrand_lower_safeLine] using
    integrable_complexSymmetricGaussian_mul_negLogDeriv_riemannXi_safeLine
      hε t

/-- Pointwise, the upper safe-line integrand is the negative reflection of
the lower safe-line integrand. -/
theorem gaussianXiSpectralIntegrand_upper_eq_neg_lower_neg
    (ε t x : ℝ) :
    gaussianXiSpectralIntegrand ε t ((x : ℂ) + Complex.I) =
      -gaussianXiSpectralIntegrand ε t (((-x : ℝ) : ℂ) - Complex.I) := by
  have hpoint : (x : ℂ) + Complex.I =
      -((((-x : ℝ) : ℂ) - Complex.I)) := by
    push_cast
    ring
  rw [hpoint, gaussianXiSpectralIntegrand_neg]

theorem integrable_gaussianXiSpectralIntegrand_upper_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ =>
      gaussianXiSpectralIntegrand ε t ((x : ℂ) + Complex.I)) := by
  have hlower :=
    (integrable_gaussianXiSpectralIntegrand_lower_safeLine hε t).comp_neg.neg
  exact hlower.congr (Filter.Eventually.of_forall fun x => by
    change
      -gaussianXiSpectralIntegrand ε t
          (((-x : ℝ) : ℂ) - Complex.I) =
        gaussianXiSpectralIntegrand ε t ((x : ℂ) + Complex.I)
    exact
      (gaussianXiSpectralIntegrand_upper_eq_neg_lower_neg ε t x).symm)

/-- The functional equation identifies the full upper safe-line integral
with the negative of the full lower safe-line integral. -/
theorem integral_gaussianXiSpectralIntegrand_upper_eq_neg_lower
    (ε t : ℝ) :
    (∫ x : ℝ,
      gaussianXiSpectralIntegrand ε t ((x : ℂ) + Complex.I)) =
      -(∫ x : ℝ,
        gaussianXiSpectralIntegrand ε t ((x : ℂ) - Complex.I)) := by
  calc
    (∫ x : ℝ,
      gaussianXiSpectralIntegrand ε t ((x : ℂ) + Complex.I)) =
        ∫ x : ℝ,
          -gaussianXiSpectralIntegrand ε t
            (((-x : ℝ) : ℂ) - Complex.I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        gaussianXiSpectralIntegrand_upper_eq_neg_lower_neg ε t x
    _ = -(∫ x : ℝ,
        gaussianXiSpectralIntegrand ε t
          (((-x : ℝ) : ℂ) - Complex.I)) := integral_neg _
    _ = -(∫ x : ℝ,
        gaussianXiSpectralIntegrand ε t ((x : ℂ) - Complex.I)) := by
      rw [integral_neg_eq_self
        (fun x : ℝ =>
          gaussianXiSpectralIntegrand ε t ((x : ℂ) - Complex.I)) volume]

end

end RiemannGaussian
