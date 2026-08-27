import RiemannGaussian.FiniteToEntireProperTimeLarge

/-!
# The small proper-time endpoint

The canonical sequence forced by failure of RH is now uniformly tight at
large proper time.  This file combines that fact with compact proper-time
convergence and the fixed positive finite Hardy mass.

The first result records exact additivity of finite heat actions across
adjacent positive-time intervals.  The main abstract estimate then shows
that any mass not present in a limiting compact action must occur before its
lower endpoint: after making the large-time tail and both convergence errors
small, a sufficiently early cutoff captures the remaining mass.

The final theorem applies this estimate to the same noncolliding canonical
sequence used throughout the finite-to-entire passage.  It does not assume a
small-time bound.  Instead, it identifies such a bound as the sole remaining
proper-time obstruction.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A finite upper-divisor heat action is additive across adjacent compact
positive-time intervals. -/
theorem upperHalfPlaneHyperbolicHeatAction_add_adjacent
    (z : ℂ) (upper : Multiset ℂ) {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    upperHalfPlaneHyperbolicHeatAction z upper (a, c) =
      upperHalfPlaneHyperbolicHeatAction z upper (a, b) +
        upperHalfPlaneHyperbolicHeatAction z upper (b, c) := by
  have hb : 0 < b := ha.trans_le hab
  rw [upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
      z upper ha (hab.trans hbc),
    upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
      z upper ha hab,
    upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
      z upper hb hbc]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_finiteUpperHyperbolicHeatSum z upper ha hab)
    (intervalIntegrable_finiteUpperHyperbolicHeatSum z upper hb hbc)).symm

/-- A finite heat action splits exactly into its small, compact, and
large-time pieces. -/
theorem upperHalfPlaneHyperbolicHeatAction_eq_small_add_compact_add_large
    (z : ℂ) (upper : Multiset ℂ) {c a T U : ℝ}
    (hc : 0 < c) (hca : c ≤ a) (haT : a ≤ T) (hTU : T ≤ U) :
    upperHalfPlaneHyperbolicHeatAction z upper (c, U) =
        upperHalfPlaneHyperbolicHeatAction z upper (c, a) +
          upperHalfPlaneHyperbolicHeatAction z upper (a, T) +
            upperHalfPlaneHyperbolicHeatAction z upper (T, U) := by
  rw [upperHalfPlaneHyperbolicHeatAction_add_adjacent
      z upper hc hca (haT.trans hTU),
    upperHalfPlaneHyperbolicHeatAction_add_adjacent
      z upper (hc.trans_le hca) haT hTU]
  ring

/-- Suppose finite heat actions have stage masses bounded below by `lower`,
converge on every compact interval beginning at `a`, and are uniformly tight
at large time.  Then, up to any positive error, the mass missing from a
suitable limiting compact action is eventually captured by an interval
`(c, a)` with `c > 0`.

The cutoff `c` may depend on the stage.  No uniform small-time estimate is
used; producing one is precisely the remaining endpoint problem. -/
theorem exists_compactUpper_eventually_smallTimeHeatAction_gt
    {z : ℂ} (hz : 0 < z.im)
    (upper : ℕ → Multiset ℂ)
    (halpha : ∀ n alpha, alpha ∈ upper n → 0 < alpha.im)
    (mass : ℕ → ℝ) {lower a : ℝ} (ha : 0 < a)
    (hmass : ∀ n, lower ≤ mass n)
    (hfull : ∀ n,
      Tendsto (upperHalfPlaneHyperbolicHeatAction z (upper n))
        ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) (nhds (mass n)))
    (g : ℝ → ℝ)
    (hcompact : ∀ T, a ≤ T →
      Tendsto
        (fun n ↦ upperHalfPlaneHyperbolicHeatAction z (upper n) (a, T))
        atTop (nhds (∫ tau in a..T, g tau)))
    (hlarge : ∀ delta : ℝ, 0 < delta →
      ∃ T : ℝ, 0 < T ∧
        ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
          upperHalfPlaneHyperbolicHeatAction z (upper n) (T, U) < delta)
    {error : ℝ} (herror : 0 < error) :
    ∃ T : ℝ, a ≤ T ∧
      ∀ᶠ n in atTop, ∃ c : ℝ, 0 < c ∧ c < a ∧
        lower - (∫ tau in a..T, g tau) - error <
          upperHalfPlaneHyperbolicHeatAction z (upper n) (c, a) := by
  let delta : ℝ := error / 3
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨T₀, hT₀, hlarge₀⟩ := hlarge delta hdelta
  let T : ℝ := max a T₀
  have haT : a ≤ T := le_max_left _ _
  have hT₀T : T₀ ≤ T := le_max_right _ _
  have hlargeT : ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
      upperHalfPlaneHyperbolicHeatAction z (upper n) (T, U) < delta := by
    filter_upwards [hlarge₀] with n hn
    intro U hTU
    have htailLe :
        upperHalfPlaneHyperbolicHeatAction z (upper n) (T, U) ≤
          upperHalfPlaneHyperbolicHeatAction z (upper n) (T₀, U) :=
      upperHalfPlaneHyperbolicHeatAction_le_of_interval_subset
        hz (halpha n) hT₀ hT₀T hTU le_rfl
    exact htailLe.trans_lt (hn U (hT₀T.trans hTU))
  have hcompactUpper : ∀ᶠ n in atTop,
      upperHalfPlaneHyperbolicHeatAction z (upper n) (a, T) <
        (∫ tau in a..T, g tau) + delta :=
    (tendsto_order.1 (hcompact T haT)).2 _ (by linarith)
  refine ⟨T, haT, ?_⟩
  filter_upwards [hlargeT, hcompactUpper] with n hnLarge hnCompact
  have hnearFull : ∀ᶠ p in
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop),
      mass n - delta <
        upperHalfPlaneHyperbolicHeatAction z (upper n) p :=
    (tendsto_order.1 (hfull n)).1 _ (by linarith)
  have hleft : ∀ᶠ c in nhdsWithin 0 (Ioi 0),
      0 < c ∧ c < a :=
    (eventually_nhdsWithin_of_forall fun _ hc ↦ hc).and
      (nhdsWithin_le_nhds (Iio_mem_nhds ha))
  have hpairs : ∀ᶠ p in
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop),
      (0 < p.1 ∧ p.1 < a) ∧ T ≤ p.2 :=
    hleft.prod_mk (eventually_ge_atTop T)
  obtain ⟨p, hnear, hp⟩ := (hnearFull.and hpairs).exists
  rcases p with ⟨c, U⟩
  rcases hp with ⟨⟨hc, hca⟩, hTU⟩
  refine ⟨c, hc, hca, ?_⟩
  have hsplit :=
    upperHalfPlaneHyperbolicHeatAction_eq_small_add_compact_add_large
      z (upper n) hc hca.le haT hTU
  have htail := hnLarge U hTU
  dsimp [delta] at hnear hnCompact htail ⊢
  linarith [hmass n]

/-- Under failure of RH, the noncolliding canonical sequence has no
large-time escape.  Quantitatively, for every positive lower cutoff `a` and
every error, some compact upper cutoff `T` makes the remaining fixed Hardy
mass appear, stage by stage, in intervals `(c, a)` approaching proper time
zero. -/
theorem exists_canonicalFiniteHardyFrontier_smallTimeEscape_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        (∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) u tau)
            atTop (nhds (riemannXiUpperHyperbolicHeatSum u tau))) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ n,
          -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
            realPolynomialUpperHyperbolicHeatMass (B n) z) ∧
        (∀ (u : ℂ) (a b : ℝ), 0 < u.im → 0 < a → a ≤ b →
          IntervalIntegrable (riemannXiUpperHyperbolicHeatSum u)
              volume a b ∧
            Tendsto
              (fun n ↦ upperHalfPlaneHyperbolicHeatAction u
                (realPolynomialUpperRootMultiset (B n)) (a, b))
              atTop
              (nhds (∫ tau in a..b,
                riemannXiUpperHyperbolicHeatSum u tau))) ∧
        (∀ epsilon : ℝ, 0 < epsilon →
          ∃ T : ℝ, 0 < T ∧
            ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
              upperHalfPlaneHyperbolicHeatAction z
                (realPolynomialUpperRootMultiset (B n)) (T, U) <
                  epsilon) ∧
        ∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop, ∃ c : ℝ, 0 < c ∧ c < a ∧
              -2 * Real.log (pairHyperbolicThreshold eta z.im) -
                    (∫ tau in a..T,
                      riemannXiUpperHyperbolicHeatSum z tau) - error <
                upperHalfPlaneHyperbolicHeatAction z
                  (realPolynomialUpperRootMultiset (B n)) (c, a) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hheat,
      hpositive, hmass, hcompact, hlarge⟩ :=
    exists_canonicalFiniteHardyFrontier_largeTimeTight_of_not_rh hRH
  refine ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hheat,
    hpositive, hmass, hcompact, hlarge, ?_⟩
  intro a error ha herror
  apply exists_compactUpper_eventually_smallTimeHeatAction_gt
    (z := z) hz
    (fun n ↦ realPolynomialUpperRootMultiset (B n))
    (fun n ↦ realPolynomialUpperRootMultiset_im_pos (B n))
    (fun n ↦ realPolynomialUpperHyperbolicHeatMass (B n) z)
    ha hmass
  · intro n
    exact (realPolynomialUpperHyperbolicHeatAction_frontier
      (hfrontier n).separable heta hz
      (hfrontier n).homotopyRoot).1
  · intro T haT
    exact (hcompact z a T hz ha haT).2
  · exact hlarge
  · exact herror

end

end RiemannGaussian
