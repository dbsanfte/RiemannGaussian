import RiemannGaussian.FiniteToEntireRadialHeatLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact proper-time convergence

This file upgrades the complete fixed-positive-time polynomial heat limit to
convergence of heat actions on every compact proper-time interval bounded away
from zero.

The key point is intrinsic to the hyperbolic heat kernel.  At positive proper
time it is an integral of `exp (-x * t)` over the interval between the two
squared hyperbolic distances.  Those endpoints are nonnegative and ordered
for two upper-half-plane points, so every one-root heat term, every finite
upper divisor heat, and hence every polynomial upper heat is antitone in
proper time.  Pointwise convergence at the left endpoint of `[a, b]` therefore
gives one stage-independent constant dominating the entire sequence on that
interval.  Lebesgue dominated convergence then identifies the limiting
compact heat action with the interval integral of the complete spectral-xi
heat sum.

Thus a Hardy defect cannot disappear in the interior of proper time.  Any
remaining failure to pass its positive total mass to the spectral limit must
escape through `t -> 0` or `t -> infinity`; controlling those two endpoints is
the next frontier.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## Antitonicity of the positive-time heat kernel -/

/-- A divided difference of two real exponentials is an interval integral.
The positivity of `t` is used only to cancel the antiderivative's factor
`t⁻¹`. -/
theorem expDifferenceDiv_eq_intervalIntegral
    {A B t : ℝ} (ht : 0 < t) :
    t⁻¹ * (Real.exp (-(A * t)) - Real.exp (-(B * t))) =
      ∫ x in A..B, Real.exp (-(x * t)) := by
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ ↦
          -t⁻¹ * (Real.exp ∘ (-(fun u : ℝ ↦ id u * t))) y)
        (Real.exp (-(x * t))) x := by
    have hinner :
        HasDerivAt (-(fun y : ℝ ↦ id y * t)) (-(1 * t)) x :=
      ((hasDerivAt_id x).mul_const t).neg
    have hexp :=
      (Real.hasDerivAt_exp ((-(fun u : ℝ ↦ id u * t)) x)).comp x hinner
    have hscaled := hexp.const_mul (-t⁻¹)
    apply hscaled.congr_deriv
    simp only [Pi.neg_apply, id_eq, one_mul]
    field_simp [ne_of_gt ht]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x)
    ((by fun_prop : Continuous fun x : ℝ ↦
      Real.exp (-(x * t))).intervalIntegrable A B)]
  field_simp
  simp only [Function.comp_apply, Pi.neg_apply, id_eq]
  ring

/-- If `0 ≤ A ≤ B`, the exponential divided difference is antitone in
positive proper time. -/
theorem expDifferenceDiv_le_of_time_le
    {A B s t : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hs : 0 < s) (hst : s ≤ t) :
    t⁻¹ * (Real.exp (-(A * t)) - Real.exp (-(B * t))) ≤
      s⁻¹ * (Real.exp (-(A * s)) - Real.exp (-(B * s))) := by
  have ht : 0 < t := hs.trans_le hst
  rw [expDifferenceDiv_eq_intervalIntegral ht,
    expDifferenceDiv_eq_intervalIntegral hs]
  apply intervalIntegral.integral_mono_on hAB
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.exp (-(x * t))).intervalIntegrable A B
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.exp (-(x * s))).intervalIntegrable A B
  · intro x hx
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ x := hA.trans hx.1
    nlinarith

/-- For positive heights, one real-coordinate hyperbolic heat term is
antitone on positive proper time. -/
theorem pairHyperbolicHeatIntegrand_le_of_time_le
    {d v a s t : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hs : 0 < s) (hst : s ≤ t) :
    pairHyperbolicHeatIntegrand d v a t ≤
      pairHyperbolicHeatIntegrand d v a s := by
  unfold pairHyperbolicHeatIntegrand
  exact expDifferenceDiv_le_of_time_le
    (pairHyperbolicUpperSq_nonneg d v a)
    (pairHyperbolicUpperSq_lt_lowerSq ha hv).le hs hst

/-- For two upper-half-plane points, one complex hyperbolic heat term is
antitone on positive proper time. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_of_time_le
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha t ≤
      upperHalfPlaneHyperbolicHeatIntegrand z alpha s := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand_eq_pair,
    upperHalfPlaneHyperbolicHeatIntegrand_eq_pair]
  exact pairHyperbolicHeatIntegrand_le_of_time_le hz halpha hs hst

/-- Every finite multiplicity-counted upper heat sum is antitone on positive
proper time. -/
theorem finiteUpperHyperbolicHeatSum_le_of_time_le
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    finiteUpperHyperbolicHeatSum z upper t ≤
      finiteUpperHyperbolicHeatSum z upper s := by
  induction upper using Multiset.induction_on with
  | empty => simp [finiteUpperHyperbolicHeatSum]
  | @cons alpha upper ih =>
      rw [finiteUpperHyperbolicHeatSum, Multiset.map_cons,
        Multiset.sum_cons, finiteUpperHyperbolicHeatSum,
        Multiset.map_cons, Multiset.sum_cons]
      apply add_le_add
      · exact upperHalfPlaneHyperbolicHeatIntegrand_le_of_time_le
          hz (halpha alpha (by simp)) hs hst
      · apply ih
        intro beta hbeta
        exact halpha beta (by simp [hbeta])

/-! ## Finite heat continuity and action exchange -/

/-- One hyperbolic heat term is continuous on every positive closed
half-line. -/
theorem continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ici
    (z alpha : ℂ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun tau : ℝ ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
      (Ici a) := by
  unfold upperHalfPlaneHyperbolicHeatIntegrand
  apply ContinuousOn.mul
  · exact continuousOn_id.inv₀ (fun tau htau ↦ by
      simpa only [id_eq] using (ne_of_gt (ha.trans_le htau)))
  · apply ContinuousOn.sub <;> fun_prop

/-- A finite multiplicity-counted upper heat sum is continuous on every
positive closed half-line. -/
theorem continuousOn_finiteUpperHyperbolicHeatSum_Ici
    (z : ℂ) (upper : Multiset ℂ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (finiteUpperHyperbolicHeatSum z upper) (Ici a) := by
  induction upper using Multiset.induction_on with
  | empty =>
      change ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Ici a)
      exact continuousOn_const
  | @cons alpha upper ih =>
      have heq : finiteUpperHyperbolicHeatSum z (alpha ::ₘ upper) =
          fun tau : ℝ ↦
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau +
              finiteUpperHyperbolicHeatSum z upper tau := by
        funext tau
        simp [finiteUpperHyperbolicHeatSum]
      rw [heq]
      exact (continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ici
        z alpha ha).add ih

/-- Finite upper heat sums are interval-integrable on compact positive-time
intervals. -/
theorem intervalIntegrable_finiteUpperHyperbolicHeatSum
    (z : ℂ) (upper : Multiset ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (finiteUpperHyperbolicHeatSum z upper)
      volume a b := by
  apply ((continuousOn_finiteUpperHyperbolicHeatSum_Ici
    z upper ha).mono ?_).intervalIntegrable
  intro tau htau
  rw [uIcc_of_le hab] at htau
  exact htau.1

/-- On a compact positive-time interval, integrating a finite heat sum is
exactly the original multiplicity-counted sum of the individual integrals. -/
theorem upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
    (z : ℂ) (upper : Multiset ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    upperHalfPlaneHyperbolicHeatAction z upper (a, b) =
      ∫ tau in a..b, finiteUpperHyperbolicHeatSum z upper tau := by
  induction upper using Multiset.induction_on with
  | empty => simp [upperHalfPlaneHyperbolicHeatAction,
      finiteUpperHyperbolicHeatSum]
  | @cons alpha upper ih =>
      have hhead : IntervalIntegrable
          (fun tau : ℝ ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
          volume a b := by
        apply ((continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ici
          z alpha ha).mono ?_).intervalIntegrable
        intro tau htau
        rw [uIcc_of_le hab] at htau
        exact htau.1
      have htail : IntervalIntegrable
          (finiteUpperHyperbolicHeatSum z upper) volume a b :=
        intervalIntegrable_finiteUpperHyperbolicHeatSum z upper ha hab
      rw [upperHalfPlaneHyperbolicHeatAction,
        Multiset.map_cons, Multiset.sum_cons,
        show finiteUpperHyperbolicHeatSum z (alpha ::ₘ upper) =
            fun tau ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau +
              finiteUpperHyperbolicHeatSum z upper tau by
          funext tau
          simp [finiteUpperHyperbolicHeatSum],
        intervalIntegral.integral_add hhead htail]
      change
        (∫ tau in a..b,
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau) +
            upperHalfPlaneHyperbolicHeatAction z upper (a, b) =
          (∫ tau in a..b,
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau) +
            ∫ tau in a..b, finiteUpperHyperbolicHeatSum z upper tau
      rw [ih]

/-! ## Dominated convergence on compact proper-time intervals -/

/-- Pointwise convergence of finite upper heat sums on positive time implies
both interval-integrability of the limit and convergence of the associated
heat actions on every compact interval bounded away from zero.

No independent domination hypothesis is needed: antitonicity bounds every
stage on `[a, b]` by its value at `a`, and convergence at `a` makes those
values eventually uniformly bounded. -/
theorem tendsto_finiteUpperHyperbolicHeatAction_on_compact_of_pointwise
    (upper : ℕ → Multiset ℂ) (z : ℂ) (hz : 0 < z.im)
    (halpha : ∀ n alpha, alpha ∈ upper n → 0 < alpha.im)
    (g : ℝ → ℝ)
    (hpointwise : ∀ tau : ℝ, 0 < tau →
      Tendsto (fun n ↦ finiteUpperHyperbolicHeatSum z (upper n) tau)
        atTop (nhds (g tau)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable g volume a b ∧
      Tendsto
        (fun n ↦ upperHalfPlaneHyperbolicHeatAction z (upper n) (a, b))
        atTop (nhds (∫ tau in a..b, g tau)) := by
  let F : ℕ → ℝ → ℝ := fun n tau ↦
    finiteUpperHyperbolicHeatSum z (upper n) tau
  let C : ℝ := g a + 1
  have hAtA : Tendsto (fun n ↦ F n a) atTop (nhds (g a)) := by
    simpa [F] using hpointwise a ha
  have hAtABound : ∀ᶠ n in atTop, F n a < C := by
    exact (tendsto_order.1 hAtA).2 C (by simp [C])
  have hstageBound :
      ∀ᶠ n in atTop, ∀ tau ∈ Ι a b, ‖F n tau‖ ≤ C := by
    filter_upwards [hAtABound] with n hn
    intro tau htau
    rw [uIoc_of_le hab] at htau
    have hat : a ≤ tau := htau.1.le
    have htauPos : 0 < tau := ha.trans_le hat
    have hmono : F n tau ≤ F n a := by
      exact finiteUpperHyperbolicHeatSum_le_of_time_le
        hz (halpha n) ha hat
    have hnonneg : 0 ≤ F n tau := by
      exact finiteUpperHyperbolicHeatSum_nonneg
        hz (halpha n) htauPos
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hmono.trans hn.le
  have hFMeas (n : ℕ) :
      AEStronglyMeasurable (F n) (volume.restrict (Ι a b)) := by
    apply ((continuousOn_finiteUpperHyperbolicHeatSum_Ici
      z (upper n) ha).mono ?_).aestronglyMeasurable measurableSet_uIoc
    intro tau htau
    rw [uIoc_of_le hab] at htau
    exact htau.1.le
  have hlimitAE :
      ∀ᵐ tau ∂volume, tau ∈ Ι a b →
        Tendsto (fun n ↦ F n tau) atTop (nhds (g tau)) := by
    apply Eventually.of_forall
    intro tau htau
    rw [uIoc_of_le hab] at htau
    have htauPos : 0 < tau := ha.trans htau.1
    simpa [F] using hpointwise tau htauPos
  have hlimitRestrict :
      ∀ᵐ tau ∂volume.restrict (Ι a b),
        Tendsto (fun n ↦ F n tau) atTop (nhds (g tau)) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact hlimitAE
  have hgMeas :
      AEStronglyMeasurable g (volume.restrict (Ι a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFMeas hlimitRestrict
  have hgBound : ∀ᵐ tau ∂volume.restrict (Ι a b), ‖g tau‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    apply Eventually.of_forall
    intro tau htau
    rw [uIoc_of_le hab] at htau
    have htauPos : 0 < tau := ha.trans htau.1
    apply le_of_tendsto (tendsto_norm.comp (hpointwise tau htauPos))
    exact hstageBound.mono fun n hn ↦ by
      simpa [F] using hn tau (by rwa [uIoc_of_le hab])
  have hCIntegrable :
      Integrable (fun _ : ℝ ↦ C) (volume.restrict (Ι a b)) := by
    apply intervalIntegrable_iff.mp
    exact intervalIntegrable_const
  have hgIntegrable : IntervalIntegrable g volume a b := by
    apply intervalIntegrable_iff.mpr
    exact hCIntegrable.mono' hgMeas hgBound
  have hDCT :
      Tendsto (fun n ↦ ∫ tau in a..b, F n tau)
        atTop (nhds (∫ tau in a..b, g tau)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ ↦ C)
    · exact Eventually.of_forall hFMeas
    · exact hstageBound.mono fun n hn ↦
        Eventually.of_forall fun tau htau ↦ hn tau htau
    · exact intervalIntegrable_const
    · exact hlimitAE
  refine ⟨hgIntegrable, ?_⟩
  have heq :
      (fun n ↦ upperHalfPlaneHyperbolicHeatAction z (upper n) (a, b)) =
        fun n ↦ ∫ tau in a..b, F n tau := by
    funext n
    simpa [F] using
      upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
        z (upper n) ha hab
  rw [heq]
  exact hDCT

/-- For polynomial upper divisors, the complete fixed-time heat limit is
therefore enough to identify every compact positive proper-time action. -/
theorem tendsto_realPolynomialUpperHeatAction_on_compact_of_pointwise
    (B : ℕ → ℝ[X]) {z : ℂ} (hz : 0 < z.im)
    (hpointwise : ∀ tau : ℝ, 0 < tau →
      Tendsto
        (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) z tau)
        atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (riemannXiUpperHyperbolicHeatSum z) volume a b ∧
      Tendsto
        (fun n ↦ upperHalfPlaneHyperbolicHeatAction z
          (realPolynomialUpperRootMultiset (B n)) (a, b))
        atTop
        (nhds (∫ tau in a..b,
          riemannXiUpperHyperbolicHeatSum z tau)) := by
  apply tendsto_finiteUpperHyperbolicHeatAction_on_compact_of_pointwise
    (fun n ↦ realPolynomialUpperRootMultiset (B n)) z hz
    (fun n ↦ realPolynomialUpperRootMultiset_im_pos (B n))
    (riemannXiUpperHyperbolicHeatSum z)
  · intro tau htau
    simpa [realPolynomialUpperHyperbolicHeatSum] using
      hpointwise tau htau
  · exact ha
  · exact hab

/-! ## The canonical finite Hardy sequence -/

/-- Under failure of RH, one and the same canonical finite Hardy sequence
has all of the following rigorously synchronized properties:

* its full upper-root heat converges at every fixed positive proper time;
* its compact positive-time actions converge to the corresponding integral
  of the complete spectral-xi heat;
* each stage's full improper heat action converges to a logarithmic mass
  bounded below by one fixed positive Hardy defect.

Consequently, the only unclosed passage is uniform control of the two
proper-time endpoints. -/
theorem exists_canonicalFiniteHardyFrontier_compactHeatAction_tendsto_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ n,
          Tendsto
              (upperHalfPlaneHyperbolicHeatAction z
                (realPolynomialUpperRootMultiset (B n)))
              ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
              (nhds (realPolynomialUpperHyperbolicHeatMass (B n) z)) ∧
            -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
              realPolynomialUpperHyperbolicHeatMass (B n) z) ∧
        ∀ (u : ℂ) (a b : ℝ), 0 < u.im → 0 < a → a ≤ b →
          IntervalIntegrable (riemannXiUpperHyperbolicHeatSum u)
              volume a b ∧
            Tendsto
              (fun n ↦ upperHalfPlaneHyperbolicHeatAction u
                (realPolynomialUpperRootMultiset (B n)) (a, b))
              atTop
              (nhds (∫ tau in a..b,
                riemannXiUpperHyperbolicHeatSum u tau)) := by
  obtain ⟨eta, heta, z, hz, B, hlimit, hfrontier, hheat⟩ :=
    exists_canonicalFiniteHardyFrontier_fullHeat_tendsto_of_not_rh hRH
  have hstageZero := realPolynomialUpperHyperbolicHeatAction_frontier
    (hfrontier 0).separable heta hz (hfrontier 0).homotopyRoot
  refine ⟨eta, heta, z, hz, B, hlimit, hfrontier,
    hstageZero.2.1, ?_, ?_⟩
  · intro n
    have hstage := realPolynomialUpperHyperbolicHeatAction_frontier
      (hfrontier n).separable heta hz (hfrontier n).homotopyRoot
    exact ⟨hstage.1, hstage.2.2⟩
  · intro u a b hu ha hab
    apply tendsto_realPolynomialUpperHeatAction_on_compact_of_pointwise
      B hu (fun tau htau ↦ hheat u tau hu htau) ha hab

end

end RiemannGaussian
