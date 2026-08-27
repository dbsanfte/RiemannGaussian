import RiemannGaussian.FiniteToEntireProperTimeCompact

/-!
# Proper-time endpoint escape

Compact positive-time convergence leaves exactly two possible places for a
stage-independent finite Hardy heat defect to go: the intervals approaching
proper time zero and infinity.  This file makes that statement precise
without assuming any endpoint estimate.

For a finite upper divisor, positivity of the heat kernel makes its action
monotone under enlargement of the proper-time interval.  The full logarithmic
mass is the improper limit of those actions, so every compact action is at
most the full mass.  Their difference is therefore a genuine nonnegative
endpoint defect.  If all full masses are bounded below by `c` while the
compact actions converge to `L`, then, up to an arbitrary positive error,
that endpoint defect is eventually at least `c - L`.

The final theorem applies this bookkeeping to the canonical sequence forced
by failure of RH.  It does not claim that the endpoint defect vanishes; it
isolates that vanishing as the exact remaining analytic obligation.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Enlarging a positive proper-time interval can only increase the heat
action of a finite upper divisor. -/
theorem upperHalfPlaneHyperbolicHeatAction_le_of_interval_subset
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {c a b d : ℝ} (hc : 0 < c) (hca : c ≤ a)
    (hab : a ≤ b) (hbd : b ≤ d) :
    upperHalfPlaneHyperbolicHeatAction z upper (a, b) ≤
      upperHalfPlaneHyperbolicHeatAction z upper (c, d) := by
  have ha : 0 < a := hc.trans_le hca
  have hcd : c ≤ d := hca.trans (hab.trans hbd)
  rw [upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
      z upper ha hab,
    upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
      z upper hc hcd]
  apply intervalIntegral.integral_mono_interval hca hab hbd
  · exact (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun tau htau ↦
        finiteUpperHyperbolicHeatSum_nonneg hz halpha
          (hc.trans htau.1))
  · exact intervalIntegrable_finiteUpperHyperbolicHeatSum
      z upper hc hcd

/-- If expanding positive-time actions converge to a full mass, every fixed
compact action is bounded by that mass. -/
theorem upperHalfPlaneHyperbolicHeatAction_le_of_tendsto
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {mass : ℝ}
    (hfull : Tendsto (upperHalfPlaneHyperbolicHeatAction z upper)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) (nhds mass))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    upperHalfPlaneHyperbolicHeatAction z upper (a, b) ≤ mass := by
  have heventually : ∀ᶠ p in
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop),
      upperHalfPlaneHyperbolicHeatAction z upper (a, b) ≤
        upperHalfPlaneHyperbolicHeatAction z upper p := by
    have hleft : ∀ᶠ c in nhdsWithin 0 (Ioi 0),
        0 < c ∧ c < a :=
      (eventually_nhdsWithin_of_forall fun _ h ↦ h).and
        (nhdsWithin_le_nhds (Iio_mem_nhds ha))
    have hpairs : ∀ᶠ p in
        ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop),
        (0 < p.1 ∧ p.1 < a) ∧ b ≤ p.2 :=
      hleft.prod_mk (eventually_ge_atTop b)
    filter_upwards [hpairs] with p hp
    rcases p with ⟨c, d⟩
    exact upperHalfPlaneHyperbolicHeatAction_le_of_interval_subset
      hz halpha hp.1.1 hp.1.2.le hab hp.2
  exact ge_of_tendsto hfull heventually

/-- Every compact positive-time action of a collision-free finite upper
divisor is at most its complete logarithmic heat mass. -/
theorem upperHalfPlaneHyperbolicHeatAction_le_mass
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    upperHalfPlaneHyperbolicHeatAction z upper (a, b) ≤
      finiteUpperHyperbolicHeatMass z upper := by
  apply upperHalfPlaneHyperbolicHeatAction_le_of_tendsto
    hz halpha
  · simpa [finiteUpperHyperbolicHeatMass] using
      tendsto_upperHalfPlaneHyperbolicHeatAction
        hz upper halpha hne
  · exact ha
  · exact hab

/-- The part of a finite polynomial's full logarithmic heat mass not present
in one compact positive-time action. -/
def realPolynomialUpperHyperbolicHeatEndpointDefect
    (A : ℝ[X]) (z : ℂ) (a b : ℝ) : ℝ :=
  realPolynomialUpperHyperbolicHeatMass A z -
    upperHalfPlaneHyperbolicHeatAction z
      (realPolynomialUpperRootMultiset A) (a, b)

/-- At a positive finite-homotopy root, every compact endpoint defect of the
complete polynomial upper divisor is nonnegative. -/
theorem realPolynomialUpperHyperbolicHeatEndpointDefect_nonneg_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ realPolynomialUpperHyperbolicHeatEndpointDefect A z a b := by
  apply sub_nonneg.mpr
  apply upperHalfPlaneHyperbolicHeatAction_le_of_tendsto
    hz (realPolynomialUpperRootMultiset_im_pos A)
  · exact tendsto_realPolynomialUpperHyperbolicHeatAction_of_finiteE_root
      hA heta hz hroot
  · exact ha
  · exact hab

/-- A uniform lower bound on full masses and convergence of compact actions
force the missing endpoint defects to retain the corresponding difference,
up to an arbitrary positive error. -/
theorem eventually_massLowerBound_sub_limit_sub_error_le_endpointDefect
    (mass action : ℕ → ℝ) {lower limit error : ℝ}
    (hmass : ∀ n, lower ≤ mass n)
    (haction : Tendsto action atTop (nhds limit))
    (herror : 0 < error) :
    ∀ᶠ n in atTop,
      lower - limit - error ≤ mass n - action n := by
  have hactionBound : ∀ᶠ n in atTop, action n < limit + error :=
    (tendsto_order.1 haction).2 (limit + error) (by linarith)
  filter_upwards [hactionBound] with n hn
  linarith [hmass n]

/-- Under failure of RH, the same canonical finite Hardy sequence has a
nonnegative endpoint defect outside every compact positive-time interval.
Moreover, this defect eventually contains all of the fixed Hardy mass lower
bound not already present in the limiting compact spectral-xi action, up to
any prescribed positive error. -/
theorem exists_canonicalFiniteHardyFrontier_endpointEscape_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        ∀ (a b : ℝ), 0 < a → a ≤ b →
          IntervalIntegrable (riemannXiUpperHyperbolicHeatSum z)
              volume a b ∧
            Tendsto
              (fun n ↦ upperHalfPlaneHyperbolicHeatAction z
                (realPolynomialUpperRootMultiset (B n)) (a, b))
              atTop
              (nhds (∫ tau in a..b,
                riemannXiUpperHyperbolicHeatSum z tau)) ∧
            (∀ n, 0 ≤
              realPolynomialUpperHyperbolicHeatEndpointDefect
                (B n) z a b) ∧
            ∀ error : ℝ, 0 < error →
              ∀ᶠ n in atTop,
                -2 * Real.log (pairHyperbolicThreshold eta z.im) -
                    (∫ tau in a..b,
                      riemannXiUpperHyperbolicHeatSum z tau) - error ≤
                  realPolynomialUpperHyperbolicHeatEndpointDefect
                    (B n) z a b := by
  obtain ⟨eta, heta, z, hz, B, hlimit, hfrontier, hpositive,
      hstage, hcompact⟩ :=
    exists_canonicalFiniteHardyFrontier_compactHeatAction_tendsto_of_not_rh
      hRH
  refine ⟨eta, heta, z, hz, B, hlimit, hfrontier, hpositive, ?_⟩
  intro a b ha hab
  obtain ⟨hintegrable, haction⟩ := hcompact z a b hz ha hab
  refine ⟨hintegrable, haction, ?_, ?_⟩
  · intro n
    apply sub_nonneg.mpr
    exact upperHalfPlaneHyperbolicHeatAction_le_of_tendsto
      hz (realPolynomialUpperRootMultiset_im_pos (B n))
        (hstage n).1 ha hab
  · intro error herror
    have hmass : ∀ n,
        -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
          realPolynomialUpperHyperbolicHeatMass (B n) z :=
      fun n ↦ (hstage n).2
    simpa [realPolynomialUpperHyperbolicHeatEndpointDefect] using
      eventually_massLowerBound_sub_limit_sub_error_le_endpointDefect
        (fun n ↦ realPolynomialUpperHyperbolicHeatMass (B n) z)
        (fun n ↦ upperHalfPlaneHyperbolicHeatAction z
          (realPolynomialUpperRootMultiset (B n)) (a, b))
        hmass haction herror

end

end RiemannGaussian
