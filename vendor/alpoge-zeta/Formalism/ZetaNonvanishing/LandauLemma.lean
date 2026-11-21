import Formalism.ZetaRealNonvanish

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

namespace landauIteratedDerivatives

def Good (H : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)

lemma meas_rpow (H : ℝ → ℝ) (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (σ : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ - 1)) (volume.restrict (Ioi 1)) :=
  hH.mul (by fun_prop : Measurable fun x : ℝ => x ^ (-σ - 1)).aestronglyMeasurable

lemma good_mono {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {σ σ' : ℝ} (h : Good H σ) (hle : σ ≤ σ') : Good H σ' := by
  refine Integrable.mono h (meas_rpow H hH σ') ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
    (norm_nonneg _)

lemma logpow_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ n ≤ (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set η : ℝ := ε / ((n : ℝ) + 1) with hη
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hηpos : 0 < η := div_pos hε hn1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0 hηpos
  have h2 : Real.log x ^ n ≤ (x ^ η / η) ^ n := pow_le_pow_left₀ hlog0 h1 n
  have h3 : (x ^ η / η) ^ n = (1 / η) ^ n * x ^ (η * n) := by
    rw [Real.rpow_mul_natCast hx0, div_pow, one_div_pow]; ring
  have h4 : x ^ (η * n) ≤ x ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hn1]
    nlinarith
  have h5 : 1 / η = ((n : ℝ) + 1) / ε := by rw [hη]; field_simp
  calc Real.log x ^ n ≤ (x ^ η / η) ^ n := h2
    _ = (1 / η) ^ n * x ^ (η * n) := h3
    _ ≤ (1 / η) ^ n * x ^ ε := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by rw [h5]

lemma good_logpow {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {τ σ : ℝ} (hτ : Good H τ) (hlt : τ < σ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-σ - 1))) (Ioi 1) := by
  set K : ℝ := (((n : ℝ) + 1) / (σ - τ)) ^ n
  have hK : 0 ≤ K := by
    have : 0 < σ - τ := by linarith
    positivity
  refine Integrable.mono' (hτ.norm.const_mul K) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => Real.log x ^ n).aestronglyMeasurable.mul
      (meas_rpow H hH σ)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hb := logpow_le n (sub_pos.2 hlt) hx1
  rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg hlog0 n),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hsplit : x ^ (-τ - 1) = x ^ (σ - τ) * x ^ (-σ - 1) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit]
  calc Real.log x ^ n * (‖H x‖ * x ^ (-σ - 1))
      ≤ (K * x ^ (σ - τ)) * (‖H x‖ * x ^ (-σ - 1)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = K * (‖H x‖ * (x ^ (σ - τ) * x ^ (-σ - 1))) := by ring

def J (H : ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (((-Real.log x) ^ n * H x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1)

lemma hasDerivAt_J (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) {z : ℂ} (hz : σc < z.re) :
    HasDerivAt (J H n) (J H (n + 1) z) z := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (((-Real.log x) ^ n * H x : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (((by fun_prop : Measurable fun x : ℝ => (-Real.log x) ^ n).aestronglyMeasurable).mul hH)
  have hint : ∀ σ : ℝ, σc < σ → IntegrableOn
      (fun x : ℝ => ‖(((-Real.log x) ^ n * H x : ℝ) : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have := good_logpow hH (hgood ((σc + σ) / 2) (by linarith))
      (show (σc + σ) / 2 < σ by linarith) n
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (hpos x hx)]
    ring
  have := hMD _ σc hmeas hint z hz
  unfold J
  convert this using 2
  funext x
  push_cast
  ring

lemma iteratedDeriv_J (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) :
    ∀ z : ℂ, σc < z.re → iteratedDeriv n (J H 0) z = J H n z := by
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (J H 0) =ᶠ[𝓝 z] J H n := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
      exact ih w hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_J hMD hH hpos hgood n hz).deriv

lemma J_real (H : ℝ → ℝ) (cr : ℝ) (n : ℕ) :
    J H n (cr : ℂ) = ((∫ x in Ioi (1:ℝ), (-Real.log x) ^ n * H x * x ^ (-cr - 1) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold J
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans one_pos hx)
  rw [Complex.ofReal_mul _ (x ^ (-cr - 1)), Complex.ofReal_cpow hx0]
  push_cast
  ring

lemma term_eq (H : ℝ → ℝ) (cr t : ℝ) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • ((-(t : ℂ)) ^ n • J H n (cr : ℂ)) =
      ((∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))) : ℝ) : ℂ) := by
  have hI : (∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1)))) =
      (-t) ^ n / n.factorial * ∫ x in Ioi (1:ℝ), (-Real.log x) ^ n * H x * x ^ (-cr - 1) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    have hp : (-t) ^ n * (-Real.log x) ^ n = t ^ n * Real.log x ^ n := by
      rw [← mul_pow, ← mul_pow, neg_mul_neg]
    have e1 : t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))) =
        (t ^ n * Real.log x ^ n) * (H x * x ^ (-cr - 1)) / n.factorial := by ring
    rw [e1, ← hp]
    ring
  rw [hI, J_real]
  simp only [smul_eq_mul]
  push_cast
  ring

lemma integrable_of_series {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x) {cr t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1))
    (hsum : Summable (fun n : ℕ =>
      ∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))))) :
    Good H (cr - t) := by
  set f : ℕ → ℝ → ℝ := fun n x => t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1)))
    with hf
  have hfi : ∀ n, Integrable (f n) (volume.restrict (Ioi 1)) := fun n => (hint n).const_mul _
  have hf0 : ∀ n, ∀ x ∈ Ioi (1:ℝ), 0 ≤ f n x := by
    intro n x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have := hpos x hx
    have := Real.log_nonneg hx1
    have := Real.rpow_nonneg hx0 (-cr - 1)
    simp only [hf]
    positivity
  have hsumx : ∀ x ∈ Ioi (1:ℝ), HasSum (fun n => f n x) (H x * x ^ (-(cr - t) - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have he := NormedSpace.expSeries_div_hasSum_exp (t * Real.log x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have := he.mul_left (H x * x ^ (-cr - 1))
    have e1 : (fun n => f n x) =
        fun i => H x * x ^ (-cr - 1) * ((t * Real.log x) ^ i / i.factorial) := by
      funext n
      simp only [hf]
      rw [mul_pow]
      ring
    have e2 : H x * x ^ (-(cr - t) - 1) = H x * x ^ (-cr - 1) * Real.exp (t * Real.log x) := by
      rw [show Real.exp (t * Real.log x) = x ^ t by rw [Real.rpow_def_of_pos hx0]; ring_nf,
        mul_assoc, ← Real.rpow_add hx0]
      ring_nf
    rw [e1, e2]
    exact this
  unfold Good IntegrableOn
  rw [← lintegral_ofReal_ne_top_iff_integrable (meas_rpow H hH _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      (hsumx x hx).nonneg (fun n => hf0 n x hx)))]
  have h1 : ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (H x * x ^ (-(cr - t) - 1)) =
      ∫⁻ x in Ioi (1:ℝ), ∑' n, ENNReal.ofReal (f n x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [← (hsumx x hx).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n => hf0 n x hx) (hsumx x hx).summable]
  rw [h1, lintegral_tsum (fun n => (hfi n).aemeasurable.ennreal_ofReal)]
  have h2 : ∀ n, ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (f n x) =
      ENNReal.ofReal (∫ x in Ioi (1:ℝ), f n x) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hfi n)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hf0 n)))).symm
  rw [tsum_congr h2, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => setIntegral_nonneg measurableSet_Ioi (hf0 n)) hsum]
  exact ENNReal.ofReal_ne_top

lemma dist_ofReal' (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma dist_re (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, sub_zero,
    show (0 : ℝ) ^ 2 + z.im ^ 2 = z.im ^ 2 by ring, Real.sqrt_sq_eq_abs]

lemma key (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {b σc : ℝ} (hσcb : σc ≤ b) (hgood : ∀ σ, σc < σ → Good H σ) {Φ : ℂ → ℂ}
    (hΦ1 : ∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s)
    (hΦ2 : ∀ σ : ℝ, σc ≤ σ → σ ≤ b → AnalyticAt ℂ Φ σ)
    (hΦeq : ∀ s : ℂ, b < s.re → Φ s = J H 0 s) : ∃ σ' < σc, Good H σ' := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_Icc.image continuous_ofReal : IsCompact ((fun σ : ℝ => (σ : ℂ)) '' Icc σc b)).exists_thickening_subset_open
      (isOpen_analyticAt ℂ Φ) (by rintro _ ⟨σ, ⟨h1, h2⟩, rfl⟩; exact hΦ2 σ h1 h2)
  have hA : ∀ z : ℂ, (b < z.re ∨ ∃ σ : ℝ, σc ≤ σ ∧ σ ≤ b ∧ dist z σ < δ) → AnalyticAt ℂ Φ z := by
    rintro z (h | ⟨σ, h1, h2, h3⟩)
    · exact hΦ1 z h
    · exact hthick (Metric.mem_thickening_iff.2 ⟨σ, ⟨σ, ⟨h1, h2⟩, rfl⟩, h3⟩)
  set R : Set ℂ := {z : ℂ | σc < z.re} ∩ {z : ℂ | z.im < δ} ∩ {z : ℂ | -δ < z.im} with hR
  have hRopen : IsOpen R :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const)).inter
      (isOpen_lt continuous_const continuous_im)
  have hRconv : Convex ℝ R :=
    ((convex_halfSpace_re_gt σc).inter (convex_halfSpace_im_lt δ)).inter (convex_halfSpace_im_gt (-δ))
  have hΦR : AnalyticOnNhd ℂ Φ R := by
    rintro z ⟨⟨h1, h2⟩, h3⟩
    apply hA
    by_cases hb : b < z.re
    · exact Or.inl hb
    · refine Or.inr ⟨z.re, le_of_lt h1, not_lt.1 hb, ?_⟩
      rw [dist_re]
      exact abs_lt.2 ⟨h3, h2⟩
  have hJan : AnalyticOnNhd ℂ (J H 0) {z : ℂ | σc < z.re} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (hasDerivAt_J hMD hH hpos hgood 0 hz).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
  have hEq : EqOn Φ (J H 0) R := by
    have hz0 : ((b + 1 : ℝ) : ℂ) ∈ R := by
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> linarith
    refine hΦR.eqOn_of_preconnected_of_eventuallyEq (hJan.mono (fun z hz => hz.1.1))
      hRconv.isPreconnected hz0 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show b < (((b + 1 : ℝ) : ℂ)).re by simp)] with w hw
    exact hΦeq w hw
  set cr : ℝ := σc + δ / 4 with hcr
  have hcR : (cr : ℂ) ∈ R := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hcr] <;> linarith
  have hev : Φ =ᶠ[𝓝 (cr : ℂ)] J H 0 := by
    filter_upwards [hRopen.mem_nhds hcR] with w hw
    exact hEq hw
  have hder : ∀ n : ℕ, iteratedDeriv n Φ (cr : ℂ) = J H n (cr : ℂ) := fun n =>
    (hev.iteratedDeriv_eq n).trans
      (iteratedDeriv_J hMD hH hpos hgood n (cr : ℂ) (by simp [hcr]; linarith))
  have hdiff : DifferentiableOn ℂ Φ (Metric.ball (cr : ℂ) (δ / 2)) := by
    intro z hz
    refine (hA z ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball] at hz
    by_cases hb : b < z.re
    · exact Or.inl hb
    · right
      have him : |z.im| < δ / 2 := by
        have := Complex.abs_im_le_norm (z - cr)
        rw [← dist_eq_norm] at this
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
        linarith
      by_cases hs : σc ≤ z.re
      · refine ⟨z.re, hs, not_lt.1 hb, ?_⟩
        rw [dist_re]; linarith
      · refine ⟨σc, le_rfl, hσcb, ?_⟩
        have h1 : dist (cr : ℂ) (σc : ℂ) = δ / 4 := by
          rw [dist_ofReal', hcr, show σc + δ / 4 - σc = δ / 4 by ring,
            abs_of_pos (by linarith)]
        linarith [dist_triangle z (cr : ℂ) (σc : ℂ)]
  set t : ℝ := 3 * δ / 8 with ht
  have hzmem : ((cr - t : ℝ) : ℂ) ∈ Metric.ball (cr : ℂ) (δ / 2) := by
    rw [Metric.mem_ball, dist_ofReal', show cr - t - cr = -t by ring, abs_neg,
      abs_of_pos (by rw [ht]; linarith)]
    rw [ht]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hdiff hzmem
  have hsub : ((cr - t : ℝ) : ℂ) - (cr : ℂ) = -(t : ℂ) := by push_cast; ring
  simp_rw [hsub, hder, term_eq] at hs
  have hsum := Complex.summable_ofReal.1 hs.summable
  have hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1) :=
    fun n => good_logpow hH (hgood (σc + δ / 8) (by linarith)) (by rw [hcr]; linarith) n
  refine ⟨cr - t, by rw [hcr, ht]; linarith, ?_⟩
  exact integrable_of_series hH hpos (by rw [ht]; positivity) hint hsum

end landauIteratedDerivatives

open landauIteratedDerivatives in
theorem landauLemma_of (hMD : MellinDeriv) : LandauLemma := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq σ hσ
  by_contra hbad
  set T : Set ℝ := {τ | a < τ ∧ ¬ Good H τ} with hT
  have hσT : σ ∈ T := ⟨hσ, hbad⟩
  have hbdd : BddAbove T := ⟨b, fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h))⟩
  set σc := sSup T with hσc
  have hσσc : σ ≤ σc := le_csSup hbdd hσT
  have hσcb : σc ≤ b := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h)))
  have hgood : ∀ τ, σc < τ → Good H τ := by
    intro τ hτ
    by_contra h
    have : τ ≤ σc := le_csSup hbdd ⟨by linarith, h⟩
    linarith
  have hJ0 : ∀ s : ℂ, b < s.re → Φ s = J H 0 s := by
    intro s hs
    rw [hΦeq s hs]
    unfold J
    congr 1
    funext x
    simp
  obtain ⟨σ', hσ'lt, hσ'⟩ := key hMD hH hpos hσcb hgood hΦ1
    (fun τ h1 h2 => hΦ2 τ (by linarith) h2) hJ0
  have : σc ≤ σ' := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (good_mono hH hσ' (le_of_lt (lt_of_not_ge h))))
  linarith

end Formalism
