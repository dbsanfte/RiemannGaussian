import Mathlib.Analysis.Normed.Group.Tannery
import RiemannGaussian.GaussianSpectral

/-!
# Fixed-center Gaussian envelope separation

The explicit detection center in `GaussianSpectral` works when a chosen
packet has maximal envelope at its own ordinate.  A more flexible argument is
to fix any real observation center where one packet uniquely maximizes the
Gaussian envelope, then evaluate along a sequence of widths that puts that
packet at odd-`π` phase.

This file kernel-checks both the finite-family version and the infinite
dominated-convergence upgrade.  For a represented zeta zero sum, finite
dimensional absolute summability supplies the required baseline majorant
without a separate zero-counting estimate.
-/

namespace RiemannGaussian

noncomputable section

open Filter Topology

/-- Envelope exponent of the packet `γ ± ia` at a fixed real observation
center `t`. -/
def offAxisEnvelopeExponent (t γ a : ℝ) : ℝ :=
  a ^ 2 - (γ - t) ^ 2

/-- Target envelope minus competing envelope at the same fixed center. -/
def fixedCenterPacketGap (t γ a η b : ℝ) : ℝ :=
  offAxisEnvelopeExponent t γ a - offAxisEnvelopeExponent t η b

/-- Widths that put the target packet at phase `(2n+1)π`.  We orient the
packet so that `2a(γ-t)>0`; changing `a` to `-a` does not change its packet
contribution. -/
def offAxisOddPiWidth (t γ a : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * (2 * Real.pi) + Real.pi) / (2 * a * (γ - t))

theorem offAxisOddPiWidth_pos
    (t γ a : ℝ) (hslope : 0 < 2 * a * (γ - t)) (n : ℕ) :
    0 < offAxisOddPiWidth t γ a n := by
  unfold offAxisOddPiWidth
  exact div_pos (add_pos_of_nonneg_of_pos
    (mul_nonneg (Nat.cast_nonneg _) (mul_pos two_pos Real.pi_pos).le)
    Real.pi_pos) hslope

theorem offAxisOddPiWidth_phase
    (t γ a : ℝ) (hslope : 0 < 2 * a * (γ - t)) (n : ℕ) :
    2 * offAxisOddPiWidth t γ a n * a * (γ - t) =
      (n : ℝ) * (2 * Real.pi) + Real.pi := by
  unfold offAxisOddPiWidth
  have hfactor : a * (γ - t) ≠ 0 := by
    nlinarith
  have hfactor' : a * γ - a * t ≠ 0 := by
    simpa [mul_sub] using hfactor
  field_simp [hfactor, hfactor']
  exact div_self hfactor

theorem offAxisOddPiWidth_tendsto_atTop
    (t γ a : ℝ) (hslope : 0 < 2 * a * (γ - t)) :
    Tendsto (offAxisOddPiWidth t γ a) atTop atTop := by
  have hcoefficient : 0 < (2 * Real.pi) / (2 * a * (γ - t)) :=
    div_pos (mul_pos two_pos Real.pi_pos) hslope
  have hmul := tendsto_natCast_atTop_atTop.const_mul_atTop hcoefficient
  have hadd := tendsto_atTop_add_const_right atTop
    (Real.pi / (2 * a * (γ - t))) hmul
  convert hadd using 1
  funext n
  unfold offAxisOddPiWidth
  ring

/-- Every positive fixed-center envelope gap decays exponentially along the
odd-`π` width sequence. -/
theorem tendsto_fixedCenter_relativeEnvelope
    (t γ a η b : ℝ) (hslope : 0 < 2 * a * (γ - t))
    (hgap : 0 < fixedCenterPacketGap t γ a η b) :
    Tendsto
      (fun n : ℕ => Real.exp
        (-offAxisOddPiWidth t γ a n *
          fixedCenterPacketGap t γ a η b))
      atTop (𝓝 0) := by
  have hlinear :
      Tendsto
        (fun n : ℕ => offAxisOddPiWidth t γ a n *
          (-fixedCenterPacketGap t γ a η b))
        atTop atBot :=
    (offAxisOddPiWidth_tendsto_atTop t γ a hslope).atTop_mul_const_of_neg
      (neg_lt_zero.mpr hgap)
  refine (Real.tendsto_exp_atBot.comp hlinear).congr' ?_
  exact Eventually.of_forall fun n => by
    simp only [Function.comp_apply]
    congr 1
    ring

/-- Dominated-convergence upgrade from one competing packet to an arbitrary
indexing type.  Summability at one baseline width controls the complete
relative-envelope tail at all later odd-`π` widths. -/
theorem tendsto_tsum_fixedCenter_relativeEnvelope
    {ι : Type*}
    (t γ a : ℝ) (η b : ι → ℝ)
    (hslope : 0 < 2 * a * (γ - t))
    (hgap : ∀ i, 0 < fixedCenterPacketGap t γ a (η i) (b i))
    (ε₀ : ℝ)
    (hsummable : Summable fun i => Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i))) :
    Tendsto
      (fun n : ℕ => ∑' i, Real.exp
        (-offAxisOddPiWidth t γ a n *
          fixedCenterPacketGap t γ a (η i) (b i)))
      atTop (𝓝 0) := by
  have hdominated := tendsto_tsum_of_dominated_convergence
    (f := fun n i => Real.exp
      (-offAxisOddPiWidth t γ a n *
        fixedCenterPacketGap t γ a (η i) (b i)))
    (g := fun _ : ι => (0 : ℝ))
    (bound := fun i => Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i)))
    hsummable
    (fun i => tendsto_fixedCenter_relativeEnvelope
      t γ a (η i) (b i) hslope (hgap i))
    (by
      filter_upwards [
        (offAxisOddPiWidth_tendsto_atTop t γ a hslope).eventually_ge_atTop ε₀
      ] with n hn
      intro i
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by
        nlinarith [hgap i]))
  simpa using hdominated

/-- The target packet is exactly negative on every odd-`π` width. -/
theorem offAxisPacketContribution_at_oddPiWidth
    (t γ a : ℝ) (hslope : 0 < 2 * a * (γ - t)) (n : ℕ) :
    offAxisPacketContribution (offAxisOddPiWidth t γ a n) t γ a =
      -2 * Real.exp
        (offAxisOddPiWidth t γ a n * offAxisEnvelopeExponent t γ a) := by
  unfold offAxisPacketContribution offAxisEnvelopeExponent
  rw [offAxisOddPiWidth_phase t γ a hslope n,
    Real.cos_nat_mul_two_pi_add_pi]
  rw [show offAxisOddPiWidth t γ a n * a ^ 2 -
      offAxisOddPiWidth t γ a n * (γ - t) ^ 2 =
      offAxisOddPiWidth t γ a n * (a ^ 2 - (γ - t) ^ 2) by ring]
  ring

/-- Finite upper-envelope separation at a fixed observation center.

If the target packet has strictly larger envelope than every member of a
finite competing family, then along all sufficiently late odd-`π` widths the
complete finite packet sum is negative.  Unlike the detection-center theorem,
the target need not have maximal off-axis height at its own ordinate. -/
theorem eventually_offAxisPacketContribution_add_finiteFamily_negative_at_fixedCenter
    {ι : Type*} [Fintype ι]
    (t γ a : ℝ) (η b : ι → ℝ)
    (hslope : 0 < 2 * a * (γ - t))
    (hgap : ∀ i, 0 < fixedCenterPacketGap t γ a (η i) (b i)) :
    ∀ᶠ n : ℕ in atTop,
      0 < offAxisOddPiWidth t γ a n ∧
        offAxisPacketContribution (offAxisOddPiWidth t γ a n) t γ a +
          ∑ i, offAxisPacketContribution
            (offAxisOddPiWidth t γ a n) t (η i) (b i) < 0 := by
  have hrelative :
      Tendsto
        (fun n : ℕ =>
          ∑ i, Real.exp
            (-offAxisOddPiWidth t γ a n *
              fixedCenterPacketGap t γ a (η i) (b i)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_finsetSum Finset.univ fun i _ =>
        tendsto_fixedCenter_relativeEnvelope t γ a (η i) (b i)
          hslope (hgap i))
  have hsmall := hrelative.eventually_lt_const zero_lt_one
  filter_upwards [hsmall] with n hsmalln
  let ε := offAxisOddPiWidth t γ a n
  let targetExponent := ε * offAxisEnvelopeExponent t γ a
  let otherExponent : ι → ℝ := fun i =>
    ε * offAxisEnvelopeExponent t (η i) (b i)
  let relativeEnvelope : ι → ℝ := fun i =>
    Real.exp (-ε * fixedCenterPacketGap t γ a (η i) (b i))
  have hother :
      ∑ i, offAxisPacketContribution ε t (η i) (b i) ≤
        ∑ i, 2 * Real.exp (otherExponent i) := by
    exact Finset.sum_le_sum fun i _ => by
      simpa only [otherExponent, offAxisEnvelopeExponent, mul_sub] using
        offAxisPacketContribution_le_envelope ε t (η i) (b i)
  have hexponent (i : ι) :
      otherExponent i = targetExponent -
        ε * fixedCenterPacketGap t γ a (η i) (b i) := by
    unfold otherExponent targetExponent fixedCenterPacketGap
    ring
  have henvelope (i : ι) :
      2 * Real.exp (otherExponent i) =
        (2 * Real.exp targetExponent) * relativeEnvelope i := by
    unfold relativeEnvelope
    rw [hexponent i, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have henvelopeSum :
      ∑ i, 2 * Real.exp (otherExponent i) =
        (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i := by
    calc
      ∑ i, 2 * Real.exp (otherExponent i) =
          ∑ i, (2 * Real.exp targetExponent) * relativeEnvelope i := by
        exact Finset.sum_congr rfl fun i _ => henvelope i
      _ = (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i := by
        rw [Finset.mul_sum]
  have hsmall' : ∑ i, relativeEnvelope i < 1 := hsmalln
  have hfamily :
      ∑ i, offAxisPacketContribution ε t (η i) (b i) <
        2 * Real.exp targetExponent := by
    calc
      ∑ i, offAxisPacketContribution ε t (η i) (b i) ≤
          ∑ i, 2 * Real.exp (otherExponent i) := hother
      _ = (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i :=
        henvelopeSum
      _ < (2 * Real.exp targetExponent) * 1 :=
        mul_lt_mul_of_pos_left hsmall' (by positivity)
      _ = 2 * Real.exp targetExponent := by ring
  refine ⟨offAxisOddPiWidth_pos t γ a hslope n, ?_⟩
  change offAxisPacketContribution ε t γ a +
    ∑ i, offAxisPacketContribution ε t (η i) (b i) < 0
  rw [offAxisPacketContribution_at_oddPiWidth t γ a hslope n]
  linarith

/-- Infinite-family upper-envelope separation under one summable dominating
Gaussian tail.

This is the analytic core needed for a scalar zero-divisor converse.  The
zeta-specific packet organization, unique-maximizer selection, and baseline
summability are completed in `GaussianZetaGeometry`. -/
theorem eventually_offAxisPacketContribution_add_tsum_negative_at_fixedCenter
    {ι : Type*}
    (t γ a : ℝ) (η b : ι → ℝ)
    (hslope : 0 < 2 * a * (γ - t))
    (hgap : ∀ i, 0 < fixedCenterPacketGap t γ a (η i) (b i))
    (ε₀ : ℝ)
    (hsummable : Summable fun i => Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i))) :
    ∀ᶠ n : ℕ in atTop,
      0 < offAxisOddPiWidth t γ a n ∧
        offAxisPacketContribution (offAxisOddPiWidth t γ a n) t γ a +
          ∑' i, offAxisPacketContribution
            (offAxisOddPiWidth t γ a n) t (η i) (b i) < 0 := by
  have hrelative := tendsto_tsum_fixedCenter_relativeEnvelope
    t γ a η b hslope hgap ε₀ hsummable
  have hsmall := hrelative.eventually_lt_const zero_lt_one
  have hbaseline :=
    (offAxisOddPiWidth_tendsto_atTop t γ a hslope).eventually_ge_atTop ε₀
  filter_upwards [hsmall, hbaseline] with n hsmalln hbaselineN
  let ε := offAxisOddPiWidth t γ a n
  let targetExponent := ε * offAxisEnvelopeExponent t γ a
  let otherExponent : ι → ℝ := fun i =>
    ε * offAxisEnvelopeExponent t (η i) (b i)
  let relativeEnvelope : ι → ℝ := fun i =>
    Real.exp (-ε * fixedCenterPacketGap t γ a (η i) (b i))
  let envelope : ι → ℝ := fun i => 2 * Real.exp (otherExponent i)
  have hrelative_le (i : ι) :
      relativeEnvelope i ≤
        Real.exp (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i)) := by
    unfold relativeEnvelope ε
    exact Real.exp_le_exp.mpr (by nlinarith [hgap i])
  have hrelativeSummable : Summable relativeEnvelope :=
    hsummable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) hrelative_le
  have hexponent (i : ι) :
      otherExponent i = targetExponent -
        ε * fixedCenterPacketGap t γ a (η i) (b i) := by
    unfold otherExponent targetExponent fixedCenterPacketGap
    ring
  have henvelope (i : ι) :
      envelope i = (2 * Real.exp targetExponent) * relativeEnvelope i := by
    unfold envelope relativeEnvelope
    rw [hexponent i, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have henvelopeSummable : Summable envelope := by
    exact (hrelativeSummable.mul_left (2 * Real.exp targetExponent)).congr
      (fun i => (henvelope i).symm)
  have hpacketSummable :
      Summable fun i => offAxisPacketContribution ε t (η i) (b i) := by
    apply henvelopeSummable.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs]
    simpa only [envelope, otherExponent, offAxisEnvelopeExponent, mul_sub] using
      abs_offAxisPacketContribution_le_envelope ε t (η i) (b i)
  have hpacket_le (i : ι) :
      offAxisPacketContribution ε t (η i) (b i) ≤ envelope i := by
    simpa only [envelope, otherExponent, offAxisEnvelopeExponent, mul_sub] using
      offAxisPacketContribution_le_envelope ε t (η i) (b i)
  have henvelopeTsum :
      ∑' i, envelope i =
        (2 * Real.exp targetExponent) * ∑' i, relativeEnvelope i := by
    calc
      ∑' i, envelope i =
          ∑' i, (2 * Real.exp targetExponent) * relativeEnvelope i :=
        tsum_congr henvelope
      _ = (2 * Real.exp targetExponent) * ∑' i, relativeEnvelope i :=
        hrelativeSummable.tsum_mul_left _
  have hsmall' : ∑' i, relativeEnvelope i < 1 := hsmalln
  have hfamily :
      ∑' i, offAxisPacketContribution ε t (η i) (b i) <
        2 * Real.exp targetExponent := by
    calc
      ∑' i, offAxisPacketContribution ε t (η i) (b i) ≤
          ∑' i, envelope i :=
        hpacketSummable.tsum_le_tsum hpacket_le henvelopeSummable
      _ = (2 * Real.exp targetExponent) * ∑' i, relativeEnvelope i :=
        henvelopeTsum
      _ < (2 * Real.exp targetExponent) * 1 :=
        mul_lt_mul_of_pos_left hsmall' (by positivity)
      _ = 2 * Real.exp targetExponent := by ring
  refine ⟨offAxisOddPiWidth_pos t γ a hslope n, ?_⟩
  change offAxisPacketContribution ε t γ a +
    ∑' i, offAxisPacketContribution ε t (η i) (b i) < 0
  rw [offAxisPacketContribution_at_oddPiWidth t γ a hslope n]
  linarith

/-! ## Weighted individual spectral points -/

/-- Dominated convergence for individually indexed spectral points with
nonnegative weights.  This is the form used after analytic multiplicities
are grouped over the distinct zeta zeros. -/
theorem tendsto_tsum_weighted_fixedCenter_relativeEnvelope
    {ι : Type*}
    (t γ a : ℝ) (η b weight : ι → ℝ)
    (hslope : 0 < 2 * a * (γ - t))
    (hweight : ∀ i, 0 ≤ weight i)
    (hgap : ∀ i, 0 < fixedCenterPacketGap t γ a (η i) (b i))
    (ε₀ : ℝ)
    (hsummable : Summable fun i => weight i * Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i))) :
    Tendsto
      (fun n : ℕ => ∑' i, weight i * Real.exp
        (-offAxisOddPiWidth t γ a n *
          fixedCenterPacketGap t γ a (η i) (b i)))
      atTop (𝓝 0) := by
  have hdominated := tendsto_tsum_of_dominated_convergence
    (f := fun n i => weight i * Real.exp
      (-offAxisOddPiWidth t γ a n *
        fixedCenterPacketGap t γ a (η i) (b i)))
    (g := fun _ : ι => (0 : ℝ))
    (bound := fun i => weight i * Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i)))
    hsummable
    (fun i => by
      simpa using Filter.Tendsto.const_mul (weight i)
        (tendsto_fixedCenter_relativeEnvelope
          t γ a (η i) (b i) hslope (hgap i)))
    (by
      filter_upwards [
        (offAxisOddPiWidth_tendsto_atTop t γ a hslope).eventually_ge_atTop ε₀
      ] with n hn
      intro i
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweight i),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [hgap i])) (hweight i))
  simpa using hdominated

/-- Infinite fixed-center separation for one target conjugate packet against
an arbitrary family of individually indexed spectral points with
nonnegative weights.  The target packet supplies `-2` times its envelope;
the competing individual points cost at most one envelope each. -/
theorem eventually_offAxisPacketContribution_add_tsum_weightedSingle_negative_at_fixedCenter
    {ι : Type*}
    (t γ a : ℝ) (η b weight : ι → ℝ)
    (hslope : 0 < 2 * a * (γ - t))
    (hweight : ∀ i, 0 ≤ weight i)
    (hgap : ∀ i, 0 < fixedCenterPacketGap t γ a (η i) (b i))
    (ε₀ : ℝ)
    (hsummable : Summable fun i => weight i * Real.exp
      (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i))) :
    ∀ᶠ n : ℕ in atTop,
      0 < offAxisOddPiWidth t γ a n ∧
        offAxisPacketContribution (offAxisOddPiWidth t γ a n) t γ a +
          ∑' i, weight i * offAxisSingleContribution
            (offAxisOddPiWidth t γ a n) t (η i) (b i) < 0 := by
  have hrelative := tendsto_tsum_weighted_fixedCenter_relativeEnvelope
    t γ a η b weight hslope hweight hgap ε₀ hsummable
  have hsmall := hrelative.eventually_lt_const zero_lt_one
  have hbaseline :=
    (offAxisOddPiWidth_tendsto_atTop t γ a hslope).eventually_ge_atTop ε₀
  filter_upwards [hsmall, hbaseline] with n hsmalln hbaselineN
  let ε := offAxisOddPiWidth t γ a n
  let targetExponent := ε * offAxisEnvelopeExponent t γ a
  let otherExponent : ι → ℝ := fun i =>
    ε * offAxisEnvelopeExponent t (η i) (b i)
  let relativeEnvelope : ι → ℝ := fun i =>
    weight i * Real.exp
      (-ε * fixedCenterPacketGap t γ a (η i) (b i))
  let envelope : ι → ℝ := fun i =>
    weight i * Real.exp (otherExponent i)
  have hrelative_le (i : ι) :
      relativeEnvelope i ≤
        weight i * Real.exp
          (-ε₀ * fixedCenterPacketGap t γ a (η i) (b i)) := by
    unfold relativeEnvelope ε
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hgap i])) (hweight i)
  have hrelativeSummable : Summable relativeEnvelope :=
    hsummable.of_nonneg_of_le
      (fun i => mul_nonneg (hweight i) (Real.exp_pos _).le)
      hrelative_le
  have hexponent (i : ι) :
      otherExponent i = targetExponent -
        ε * fixedCenterPacketGap t γ a (η i) (b i) := by
    unfold otherExponent targetExponent fixedCenterPacketGap
    ring
  have henvelope (i : ι) :
      envelope i = Real.exp targetExponent * relativeEnvelope i := by
    unfold envelope relativeEnvelope
    rw [hexponent i,
      show targetExponent -
          ε * fixedCenterPacketGap t γ a (η i) (b i) =
        targetExponent +
          (-ε * fixedCenterPacketGap t γ a (η i) (b i)) by ring,
      Real.exp_add]
    ring
  have henvelopeSummable : Summable envelope := by
    exact (hrelativeSummable.mul_left (Real.exp targetExponent)).congr
      (fun i => (henvelope i).symm)
  have hsingleSummable :
      Summable fun i => weight i *
        offAxisSingleContribution ε t (η i) (b i) := by
    apply henvelopeSummable.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweight i)]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [envelope, otherExponent, offAxisEnvelopeExponent,
          mul_sub] using
            abs_offAxisSingleContribution_le_envelope
              ε t (η i) (b i))
      (hweight i)
  have hsingle_le (i : ι) :
      weight i * offAxisSingleContribution ε t (η i) (b i) ≤
        envelope i := by
    unfold envelope otherExponent offAxisEnvelopeExponent
    apply mul_le_mul_of_nonneg_left _ (hweight i)
    simpa only [mul_sub] using
      offAxisSingleContribution_le_envelope ε t (η i) (b i)
  have henvelopeTsum :
      ∑' i, envelope i =
        Real.exp targetExponent * ∑' i, relativeEnvelope i := by
    calc
      ∑' i, envelope i =
          ∑' i, Real.exp targetExponent * relativeEnvelope i :=
        tsum_congr henvelope
      _ = Real.exp targetExponent * ∑' i, relativeEnvelope i :=
        hrelativeSummable.tsum_mul_left _
  have hsmall' : ∑' i, relativeEnvelope i < 1 := hsmalln
  have hfamily :
      ∑' i, weight i * offAxisSingleContribution ε t (η i) (b i) <
        Real.exp targetExponent := by
    calc
      ∑' i, weight i * offAxisSingleContribution ε t (η i) (b i) ≤
          ∑' i, envelope i :=
        hsingleSummable.tsum_le_tsum hsingle_le henvelopeSummable
      _ = Real.exp targetExponent * ∑' i, relativeEnvelope i :=
        henvelopeTsum
      _ < Real.exp targetExponent * 1 :=
        mul_lt_mul_of_pos_left hsmall' (Real.exp_pos _)
      _ = Real.exp targetExponent := by ring
  refine ⟨offAxisOddPiWidth_pos t γ a hslope n, ?_⟩
  change offAxisPacketContribution ε t γ a +
    ∑' i, weight i * offAxisSingleContribution ε t (η i) (b i) < 0
  rw [offAxisPacketContribution_at_oddPiWidth t γ a hslope n]
  nlinarith [Real.exp_pos targetExponent]

end

end RiemannGaussian
