import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatPuncture
import RiemannGaussian.RiemannXiSuzukiSpectralUpperContourProjection

/-!
# Rectangular excision for arithmetic boundary heat

This file builds the rectangular base case needed to pass the verified
zero-free Cauchy--Green identity across xi-zero punctures.  It first records
local gluing laws for arbitrary rectangular boundary integrals.  It then
proves that a simple-pole limit controls shrinking *square* boundaries, using
the project's elementary rectangle residue theorem rather than a holomorphic
assumption on the weighted response.

The final theorem applies these ingredients to one isolated shifted xi zero.
The sum of the four Cauchy--Green area integrals outside a shrinking centered
square has a forced limit: the outer boundary integral minus `2*pi*i` times
the exact heat-weighted xi residue.  Thus the improper punctured-area limit is
proved from finite zero-free rectangles; it is not inserted as a hypothesis.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Topology

/-! ## Generic rectangular gluing -/

/-- Boundary integrability glues across a vertical subdivision. -/
theorem rectangularBoundaryIntegrable_glue_re
    {l m r b u : ℝ} {f : ℂ → ℂ}
    (hleft : rectangularBoundaryIntegrable l m b u f)
    (hright : rectangularBoundaryIntegrable m r b u f) :
    rectangularBoundaryIntegrable l r b u f := by
  exact ⟨hleft.1.trans hright.1,
    hleft.2.1.trans hright.2.1,
    hright.2.2.1, hleft.2.2.2⟩

/-- Boundary integrability glues across a horizontal subdivision. -/
theorem rectangularBoundaryIntegrable_glue_im
    {l r b m u : ℝ} {f : ℂ → ℂ}
    (hbottom : rectangularBoundaryIntegrable l r b m f)
    (htop : rectangularBoundaryIntegrable l r m u f) :
    rectangularBoundaryIntegrable l r b u f := by
  exact ⟨hbottom.1, htop.2.1,
    hbottom.2.2.1.trans htop.2.2.1,
    hbottom.2.2.2.trans htop.2.2.2⟩

/-- A vertical subdivision adds boundary integrals under the exact local
integrability assumptions needed for the cancellation. -/
theorem rectangularBoundaryIntegral_split_re_of_boundaryIntegrable
    (l m r b u : ℝ) (f : ℂ → ℂ)
    (hleft : rectangularBoundaryIntegrable l m b u f)
    (hright : rectangularBoundaryIntegrable m r b u f) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l m b u f +
        rectangularBoundaryIntegral m r b u f := by
  unfold rectangularBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      hleft.1 hright.1,
    ← intervalIntegral.integral_add_adjacent_intervals
      hleft.2.1 hright.2.1]
  ring

/-- A horizontal subdivision adds boundary integrals under the exact local
integrability assumptions needed for the cancellation. -/
theorem rectangularBoundaryIntegral_split_im_of_boundaryIntegrable
    (l r b m u : ℝ) (f : ℂ → ℂ)
    (hbottom : rectangularBoundaryIntegrable l r b m f)
    (htop : rectangularBoundaryIntegrable l r m u f) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l r b m f +
        rectangularBoundaryIntegral l r m u f := by
  unfold rectangularBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      hbottom.2.2.1 htop.2.2.1,
    ← intervalIntegral.integral_add_adjacent_intervals
      hbottom.2.2.2 htop.2.2.2]
  ring

/-- The counterclockwise outer boundary is the sum of the four rectangular
pieces surrounding a centered square and the counterclockwise boundary of
that square. -/
theorem rectangularBoundaryIntegral_eq_fourPieces_add_centeredSquare
    (l r b u : ℝ) (c : ℂ) (q : ℝ) (f : ℂ → ℂ)
    (hleft : rectangularBoundaryIntegrable
      l (c.re - q) b u f)
    (hbottom : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) b (c.im - q) f)
    (hsquare : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q) f)
    (htop : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im + q) u f)
    (hright : rectangularBoundaryIntegrable
      (c.re + q) r b u f) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l (c.re - q) b u f +
      rectangularBoundaryIntegral (c.re - q) (c.re + q)
          b (c.im - q) f +
      rectangularBoundaryIntegral (c.re - q) (c.re + q)
          (c.im - q) (c.im + q) f +
      rectangularBoundaryIntegral (c.re - q) (c.re + q)
          (c.im + q) u f +
      rectangularBoundaryIntegral (c.re + q) r b u f := by
  have hbottomSquare :=
    rectangularBoundaryIntegrable_glue_im hbottom hsquare
  have hmiddle :=
    rectangularBoundaryIntegrable_glue_im hbottomSquare htop
  have hmiddleRight :=
    rectangularBoundaryIntegrable_glue_re hmiddle hright
  rw [rectangularBoundaryIntegral_split_re_of_boundaryIntegrable
      l (c.re - q) r b u f hleft hmiddleRight,
    rectangularBoundaryIntegral_split_re_of_boundaryIntegrable
      (c.re - q) (c.re + q) r b u f hmiddle hright,
    rectangularBoundaryIntegral_split_im_of_boundaryIntegrable
      (c.re - q) (c.re + q) b (c.im + q) u f
      hbottomSquare htop,
    rectangularBoundaryIntegral_split_im_of_boundaryIntegrable
      (c.re - q) (c.re + q) b (c.im - q) (c.im + q) f
      hbottom hsquare]
  ring

/-! ## Shrinking square residues -/

/-- A simple pole is integrable on the four sides of every positive-radius
square centered at its pole. -/
theorem rectangularBoundaryIntegrable_simplePoleKernel_centeredSquare
    (L c : ℂ) {q : ℝ} (hq : 0 < q) :
    rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q)
      (simplePoleKernel L c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuous_simplePoleKernel_horizontal L c
      (by linarith : c.im - q ≠ c.im)).intervalIntegrable _ _
  · exact (continuous_simplePoleKernel_horizontal L c
      (by linarith : c.im + q ≠ c.im)).intervalIntegrable _ _
  · exact (continuous_simplePoleKernel_vertical L c
      (by linarith : c.re + q ≠ c.re)).intervalIntegrable _ _
  · exact (continuous_simplePoleKernel_vertical L c
      (by linarith : c.re - q ≠ c.re)).intervalIntegrable _ _

/-- A uniform norm bound on the four sides bounds the complete rectangular
boundary integral by the sum of the four side lengths. -/
theorem norm_rectangularBoundaryIntegral_le_of_norm_le_const
    {l r b u C : ℝ} {f : ℂ → ℂ}
    (hbottom : ∀ x ∈ Ι l r,
      ‖f ((x : ℂ) + (b : ℂ) * Complex.I)‖ ≤ C)
    (htop : ∀ x ∈ Ι l r,
      ‖f ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C)
    (hright : ∀ y ∈ Ι b u,
      ‖f ((r : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C)
    (hleft : ∀ y ∈ Ι b u,
      ‖f ((l : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C) :
    ‖rectangularBoundaryIntegral l r b u f‖ ≤
      C * |r - l| + C * |r - l| +
        C * |u - b| + C * |u - b| := by
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const hbottom
  have htnd := intervalIntegral.norm_integral_le_of_norm_le_const htop
  have hrnd := intervalIntegral.norm_integral_le_of_norm_le_const hright
  have hlnd := intervalIntegral.norm_integral_le_of_norm_le_const hleft
  unfold rectangularBoundaryIntegral
  calc
    ‖(∫ x : ℝ in l..r,
          f ((x : ℂ) + (b : ℂ) * Complex.I)) -
        (∫ x : ℝ in l..r,
          f ((x : ℂ) + (u : ℂ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in b..u,
          f ((r : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ in b..u,
          f ((l : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖∫ x : ℝ in l..r,
          f ((x : ℂ) + (b : ℂ) * Complex.I)‖ +
        ‖∫ x : ℝ in l..r,
          f ((x : ℂ) + (u : ℂ) * Complex.I)‖ +
        ‖∫ y : ℝ in b..u,
          f ((r : ℂ) + (y : ℂ) * Complex.I)‖ +
        ‖∫ y : ℝ in b..u,
          f ((l : ℂ) + (y : ℂ) * Complex.I)‖ := by
      calc
        _ ≤ ‖(∫ x : ℝ in l..r,
              f ((x : ℂ) + (b : ℂ) * Complex.I)) -
            (∫ x : ℝ in l..r,
              f ((x : ℂ) + (u : ℂ) * Complex.I)) +
            Complex.I * (∫ y : ℝ in b..u,
              f ((r : ℂ) + (y : ℂ) * Complex.I))‖ +
            ‖Complex.I * (∫ y : ℝ in b..u,
              f ((l : ℂ) + (y : ℂ) * Complex.I))‖ := norm_sub_le _ _
        _ ≤ (‖(∫ x : ℝ in l..r,
              f ((x : ℂ) + (b : ℂ) * Complex.I)) -
            (∫ x : ℝ in l..r,
              f ((x : ℂ) + (u : ℂ) * Complex.I))‖ +
            ‖Complex.I * (∫ y : ℝ in b..u,
              f ((r : ℂ) + (y : ℂ) * Complex.I))‖) +
            ‖Complex.I * (∫ y : ℝ in b..u,
              f ((l : ℂ) + (y : ℂ) * Complex.I))‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖∫ x : ℝ in l..r,
              f ((x : ℂ) + (b : ℂ) * Complex.I)‖ +
            ‖∫ x : ℝ in l..r,
              f ((x : ℂ) + (u : ℂ) * Complex.I)‖) +
            ‖Complex.I * (∫ y : ℝ in b..u,
              f ((r : ℂ) + (y : ℂ) * Complex.I))‖) +
            ‖Complex.I * (∫ y : ℝ in b..u,
              f ((l : ℂ) + (y : ℂ) * Complex.I))‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by simp [add_assoc]
    _ ≤ C * |r - l| + C * |r - l| +
          C * |u - b| + C * |u - b| := by
      simpa only [Complex.norm_I, one_mul] using
        add_le_add (add_le_add (add_le_add hbnd htnd) hrnd) hlnd

/-- A simple-pole limit controls shrinking centered-square boundaries.  The
function itself need not be holomorphic. -/
theorem tendsto_rectangularBoundaryIntegral_centeredSquare_nhdsGT_zero_of_tendsto_sub_mul
    {f : ℂ → ℂ} {c L : ℂ}
    (hintegrable : ∀ᶠ q : ℝ in 𝓝[>] 0,
      rectangularBoundaryIntegrable
        (c.re - q) (c.re + q) (c.im - q) (c.im + q) f)
    (hresidue : Tendsto (fun z : ℂ => (z - c) * f z)
      (𝓝[≠] c) (𝓝 L)) :
    Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral
        (c.re - q) (c.re + q) (c.im - q) (c.im + q) f)
      (𝓝[>] 0) (𝓝 ((2 * Real.pi * Complex.I) * L)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 16
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hclose : ∀ᶠ z in 𝓝[≠] c,
      dist ((z - c) * f z) L < eta :=
    (Metric.tendsto_nhds.mp hresidue) eta heta
  rw [eventually_nhdsWithin_iff] at hclose
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hclose
  have hrange : Ioo (0 : ℝ) (delta / 2) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hintegrable, hrange] with q hfint hq
  have hq0 : 0 < q := hq.1
  have hqdelta : 2 * q < delta := by linarith [hq.2]
  have hprincipalInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q)
      (simplePoleKernel L c) :=
    rectangularBoundaryIntegrable_simplePoleKernel_centeredSquare L c hq0
  have hprincipal : rectangularBoundaryIntegral
      (c.re - q) (c.re + q) (c.im - q) (c.im + q)
      (simplePoleKernel L c) = (2 * Real.pi * Complex.I) * L := by
    simpa [mul_assoc] using
      rectangularBoundaryIntegral_simplePoleKernel_of_mem L c
        (show c.re - q < c.re by linarith)
        (show c.re < c.re + q by linarith)
        (show c.im - q < c.im by linarith)
        (show c.im < c.im + q by linarith)
  have herror (z : ℂ) (hlower : q ≤ ‖z - c‖)
      (hupper : ‖z - c‖ < delta) :
      ‖f z - simplePoleKernel L c z‖ ≤ eta / q := by
    have hzc : z - c ≠ 0 := by
      apply norm_ne_zero_iff.mp
      exact ne_of_gt (hq0.trans_le hlower)
    have hzball : z ∈ ball c delta := by
      simpa [mem_ball, dist_eq_norm] using hupper
    have hzNe : z ∈ ({c} : Set ℂ)ᶜ := by
      simpa [sub_ne_zero] using hzc
    have hgap : ‖(z - c) * f z - L‖ ≤ eta := by
      have := (hball hzball hzNe).le
      simpa [dist_eq_norm] using this
    have heq :
        f z - simplePoleKernel L c z =
          (z - c)⁻¹ * ((z - c) * f z - L) := by
      unfold simplePoleKernel
      field_simp [hzc]
    have hinv : ‖z - c‖⁻¹ ≤ q⁻¹ :=
      (inv_le_inv₀ (norm_pos_iff.mpr hzc) hq0).2 hlower
    rw [heq, norm_mul, norm_inv]
    calc
      ‖z - c‖⁻¹ * ‖(z - c) * f z - L‖ ≤ q⁻¹ * eta :=
        mul_le_mul hinv hgap (norm_nonneg _) (inv_nonneg.mpr hq0.le)
      _ = eta / q := by rw [div_eq_mul_inv, mul_comm]
  have hside (z : ℂ)
      (hre : |(z - c).re| ≤ q) (him : |(z - c).im| ≤ q)
      (hlower : q ≤ ‖z - c‖) :
      ‖f z - simplePoleKernel L c z‖ ≤ eta / q := by
    apply herror z hlower
    calc
      ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ q + q := add_le_add hre him
      _ < delta := by linarith
  have hbottom : ∀ t ∈ Ι (c.re - q) (c.re + q),
      ‖f ((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I) -
        simplePoleKernel L c
          ((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I)‖ ≤ eta / q := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have hre : |t - c.re| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hside
    · simpa using hre
    · simp [abs_of_pos hq0]
    · calc
        q = |(((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I) - c).im| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I) - c‖ :=
          Complex.abs_im_le_norm _
  have htop : ∀ t ∈ Ι (c.re - q) (c.re + q),
      ‖f ((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I) -
        simplePoleKernel L c
          ((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I)‖ ≤ eta / q := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have hre : |t - c.re| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hside
    · simpa using hre
    · simp [abs_of_pos hq0]
    · calc
        q = |(((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I) - c).im| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I) - c‖ :=
          Complex.abs_im_le_norm _
  have hright : ∀ t ∈ Ι (c.im - q) (c.im + q),
      ‖f (((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I) -
        simplePoleKernel L c
          (((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ eta / q := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have him : |t - c.im| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hside
    · simp [abs_of_pos hq0]
    · simpa using him
    · calc
        q = |((((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c).re| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖(((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c‖ :=
          Complex.abs_re_le_norm _
  have hleft : ∀ t ∈ Ι (c.im - q) (c.im + q),
      ‖f (((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I) -
        simplePoleKernel L c
          (((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ eta / q := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    have him : |t - c.im| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hside
    · simp [abs_of_pos hq0]
    · simpa using him
    · calc
        q = |((((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c).re| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖(((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c‖ :=
          Complex.abs_re_le_norm _
  have hsub := rectangularBoundaryIntegral_sub
    (c.re - q) (c.re + q) (c.im - q) (c.im + q)
    hfint hprincipalInt
  rw [← hprincipal, dist_eq_norm, ← hsub]
  calc
    ‖rectangularBoundaryIntegral
        (c.re - q) (c.re + q) (c.im - q) (c.im + q)
        (fun z => f z - simplePoleKernel L c z)‖ ≤
        (eta / q) * |(c.re + q) - (c.re - q)| +
          (eta / q) * |(c.re + q) - (c.re - q)| +
          (eta / q) * |(c.im + q) - (c.im - q)| +
          (eta / q) * |(c.im + q) - (c.im - q)| :=
      norm_rectangularBoundaryIntegral_le_of_norm_le_const
        hbottom htop hright hleft
    _ = 8 * eta := by
      rw [show |(c.re + q) - (c.re - q)| = 2 * q by
          rw [abs_of_pos (by linarith)]; ring,
        show |(c.im + q) - (c.im - q)| = 2 * q by
          rw [abs_of_pos (by linarith)]; ring]
      field_simp [hq0.ne']
      ring
    _ < epsilon := by
      dsimp [eta]
      linarith

/-! ## The arithmetic response on rectangles -/

/-- Iterated area integral over an axis-parallel rectangle, in the
normalization used by mathlib's rectangular Cauchy--Green theorem. -/
def rectangularAreaIntegral
    (l r b u : ℝ) (g : ℂ → ℂ) : ℂ :=
  ∫ a : ℝ in l..r, ∫ y : ℝ in b..u,
    g ((a : ℂ) + (y : ℂ) * Complex.I)

/-- The four rectangular area pieces left after deleting an open centered
square from an outer rectangle. -/
def rectangularAreaIntegralOutsideCenteredSquare
    (l r b u : ℝ) (c : ℂ) (q : ℝ) (g : ℂ → ℂ) : ℂ :=
  rectangularAreaIntegral l (c.re - q) b u g +
    rectangularAreaIntegral (c.re - q) (c.re + q)
      b (c.im - q) g +
    rectangularAreaIntegral (c.re - q) (c.re + q)
      (c.im + q) u g +
    rectangularAreaIntegral (c.re + q) r b u g

/-- The heat-weighted arithmetic response is continuous throughout its
zero-free pole-cleared domain. -/
theorem continuousOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) :
    ContinuousOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  exact
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
        x tau).continuous.continuousOn.mul
      analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation.continuousOn

/-- A zero-free rectangle has an integrable heat-weighted response on all
four parametrized sides. -/
theorem rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau l r b u : ℝ)
    (hdomain :
      [[l, r]] ×ℂ [[b, u]] ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    rectangularBoundaryIntegrable l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) := by
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
  have hF : ContinuousOn F ([[l, r]] ×ℂ [[b, u]]) :=
    (continuousOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau).mono hdomain
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    simpa [F, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun a : ℝ => (a : ℂ) + (b : ℂ) * Complex.I) [[l, r]])
      (fun a ha => ⟨by simpa using ha,
        by simp⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [F, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun a : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) [[l, r]])
      (fun a ha => ⟨by simpa using ha,
        by simp⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [F, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) [[b, u]])
      (fun y hy => ⟨by simp,
        by simpa using hy⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [F, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun y : ℝ => (l : ℂ) + (y : ℂ) * Complex.I) [[b, u]])
      (fun y hy => ⟨by simp,
        by simpa using hy⟩)

/-- The existing zero-free Cauchy--Green theorem in the reusable
`rectangularBoundaryIntegral = rectangularAreaIntegral` notation. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_rectangularCauchyGreen
    (x tau l r b u : ℝ)
    (hdomain :
      [[l, r]] ×ℂ [[b, u]] ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    rectangularBoundaryIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      rectangularAreaIntegral l r b u (fun p =>
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
          suzukiChebyshevLogAverageLaplacePoleClearedContinuation p) := by
  simpa [rectangularBoundaryIntegral, rectangularAreaIntegral,
    sub_eq_add_neg] using
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_cauchyGreenRectangle
      x tau ((l : ℂ) + (b : ℂ) * Complex.I)
        ((r : ℂ) + (u : ℂ) * Complex.I) (by simpa using hdomain)

/-- The actual weighted response is integrable on every sufficiently small
centered-square boundary around a shifted xi zero. -/
theorem eventually_rectangularBoundaryIntegrable_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    ∀ᶠ q : ℝ in 𝓝[>] 0,
      rectangularBoundaryIntegrable
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re + q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im + q)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) := by
  let c := suzukiChebyshevLaplaceZeroCoordinate rho
  obtain ⟨R, hR, hlocal⟩ :=
    exists_ball_punctured_subset_suzukiChebyshevLogAverageLaplacePoleClearedDomain
      rho
  have hrange : Ioo (0 : ℝ) (R / 2) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hrange] with q hq
  have hq0 : 0 < q := hq.1
  have hqR : 2 * q < R := by linarith [hq.2]
  have hpoint (z : ℂ)
      (hre : |(z - c).re| ≤ q) (him : |(z - c).im| ≤ q)
      (hlower : q ≤ ‖z - c‖) :
      z ∈ suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    have hupper : ‖z - c‖ < R := by
      calc
        ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ q + q := add_le_add hre him
        _ < R := by linarith
    have hne : z ≠ c := by
      intro hzc
      subst z
      simp at hlower
      linarith
    apply hlocal
    constructor
    · simpa [mem_ball, dist_eq_norm] using hupper
    · simpa using hne
  have hbottomMap : MapsTo
      (fun t : ℝ => (t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I)
      [[c.re - q, c.re + q]]
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hre : |t - c.re| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hpoint
    · simpa using hre
    · simp [abs_of_pos hq0]
    · calc
        q = |(((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I) - c).im| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖((t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I) - c‖ :=
          Complex.abs_im_le_norm _
  have htopMap : MapsTo
      (fun t : ℝ => (t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I)
      [[c.re - q, c.re + q]]
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hre : |t - c.re| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hpoint
    · simpa using hre
    · simp [abs_of_pos hq0]
    · calc
        q = |(((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I) - c).im| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖((t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I) - c‖ :=
          Complex.abs_im_le_norm _
  have hrightMap : MapsTo
      (fun t : ℝ => ((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      [[c.im - q, c.im + q]]
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have him : |t - c.im| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hpoint
    · simp [abs_of_pos hq0]
    · simpa using him
    · calc
        q = |((((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c).re| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖(((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c‖ :=
          Complex.abs_re_le_norm _
  have hleftMap : MapsTo
      (fun t : ℝ => ((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      [[c.im - q, c.im + q]]
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have him : |t - c.im| ≤ q := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    apply hpoint
    · simp [abs_of_pos hq0]
    · simpa using him
    · calc
        q = |((((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c).re| := by
          simp [abs_of_pos hq0]
        _ ≤ ‖(((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c‖ :=
          Complex.abs_re_le_norm _
  have hF :=
    continuousOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    simpa [c, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun t : ℝ => (t : ℂ) + ((c.im - q : ℝ) : ℂ) * Complex.I)
        [[c.re - q, c.re + q]]) hbottomMap
  · apply ContinuousOn.intervalIntegrable
    simpa [c, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun t : ℝ => (t : ℂ) + ((c.im + q : ℝ) : ℂ) * Complex.I)
        [[c.re - q, c.re + q]]) htopMap
  · apply ContinuousOn.intervalIntegrable
    simpa [c, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun t : ℝ => ((c.re + q : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        [[c.im - q, c.im + q]]) hrightMap
  · apply ContinuousOn.intervalIntegrable
    simpa [c, Function.comp_def] using hF.comp
      (by fun_prop : ContinuousOn
        (fun t : ℝ => ((c.re - q : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        [[c.im - q, c.im + q]]) hleftMap

/-- Shrinking square boundaries of the actual non-holomorphic weighted
response recover the exact moving heat-weighted residue. -/
theorem tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re + q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im + q)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau))
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  exact
    tendsto_rectangularBoundaryIntegral_centeredSquare_nhdsGT_zero_of_tendsto_sub_mul
      (eventually_rectangularBoundaryIntegrable_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
        x tau rho)
      (tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
        x tau rho)

/-- At a selected shifted zero, the shrinking-square contribution is the
exact boundary-heat residue already used by the complete summable detector. -/
theorem tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
    (x tau : ℝ) (rho : NontrivialZetaZero)
    (hrho : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).re + q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im - q)
        ((suzukiChebyshevLaplaceZeroCoordinate rho).im + q)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau))
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  simpa [suzukiChebyshevLaplaceBoundaryHeatResidue, hrho] using
    tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho

/-! ## One-puncture rectangular excision -/

/-- The four closed rectangles outside a strictly interior centered square
lie in any domain containing the outer rectangle minus its center. -/
theorem fourRectanglesOutsideCenteredSquare_subset_of_rectangle_diff_singleton_subset
    {D : Set ℂ} (l r b u : ℝ) (c : ℂ) (q : ℝ)
    (hq : 0 < q)
    (hl : l < c.re - q) (hr : c.re + q < r)
    (hb : b < c.im - q) (hu : c.im + q < u)
    (hdomain : ([[l, r]] ×ℂ [[b, u]]) \ {c} ⊆ D) :
    ([[l, c.re - q]] ×ℂ [[b, u]] ⊆ D) ∧
    ([[c.re - q, c.re + q]] ×ℂ [[b, c.im - q]] ⊆ D) ∧
    ([[c.re - q, c.re + q]] ×ℂ [[c.im + q, u]] ⊆ D) ∧
    ([[c.re + q, r]] ×ℂ [[b, u]] ⊆ D) := by
  have hlr : l ≤ r := (hl.trans (by linarith : c.re - q < r)).le
  have hbu : b ≤ u := (hb.trans (by linarith : c.im - q < u)).le
  have hmemOuter (z : ℂ)
      (hzl : l ≤ z.re) (hzr : z.re ≤ r)
      (hzb : b ≤ z.im) (hzu : z.im ≤ u) :
      z ∈ [[l, r]] ×ℂ [[b, u]] := by
    constructor
    · simpa [uIcc_of_le hlr] using And.intro hzl hzr
    · simpa [uIcc_of_le hbu] using And.intro hzb hzu
  constructor
  · intro z hz
    have hzre : l ≤ z.re ∧ z.re ≤ c.re - q := by
      simpa [uIcc_of_le hl.le] using hz.1
    have hzim : b ≤ z.im ∧ z.im ≤ u := by
      simpa [uIcc_of_le hbu] using hz.2
    apply hdomain
    constructor
    · exact hmemOuter z hzre.1 (hzre.2.trans (by linarith)) hzim.1 hzim.2
    · have hne : z ≠ c := by
        intro hzc
        have hre := congrArg Complex.re hzc
        linarith [hzre.2]
      simpa using hne
  constructor
  · intro z hz
    have hzre : c.re - q ≤ z.re ∧ z.re ≤ c.re + q := by
      simpa [uIcc_of_le (by linarith : c.re - q ≤ c.re + q)] using hz.1
    have hzim : b ≤ z.im ∧ z.im ≤ c.im - q := by
      simpa [uIcc_of_le hb.le] using hz.2
    apply hdomain
    constructor
    · exact hmemOuter z (hl.le.trans hzre.1) (hzre.2.trans hr.le)
        hzim.1 (hzim.2.trans (by linarith))
    · have hne : z ≠ c := by
        intro hzc
        have him := congrArg Complex.im hzc
        linarith [hzim.2]
      simpa using hne
  constructor
  · intro z hz
    have hzre : c.re - q ≤ z.re ∧ z.re ≤ c.re + q := by
      simpa [uIcc_of_le (by linarith : c.re - q ≤ c.re + q)] using hz.1
    have hzim : c.im + q ≤ z.im ∧ z.im ≤ u := by
      simpa [uIcc_of_le hu.le] using hz.2
    apply hdomain
    constructor
    · exact hmemOuter z (hl.le.trans hzre.1) (hzre.2.trans hr.le)
        ((by linarith : b ≤ c.im + q).trans hzim.1) hzim.2
    · have hne : z ≠ c := by
        intro hzc
        have him := congrArg Complex.im hzc
        linarith [hzim.1]
      simpa using hne
  · intro z hz
    have hzre : c.re + q ≤ z.re ∧ z.re ≤ r := by
      simpa [uIcc_of_le hr.le] using hz.1
    have hzim : b ≤ z.im ∧ z.im ≤ u := by
      simpa [uIcc_of_le hbu] using hz.2
    apply hdomain
    constructor
    · exact hmemOuter z ((by linarith : l ≤ c.re + q).trans hzre.1)
        hzre.2 hzim.1 hzim.2
    · have hne : z ≠ c := by
        intro hzc
        have hre := congrArg Complex.re hzc
        linarith [hzre.1]
      simpa using hne

/-- Exact one-puncture Cauchy--Green identity at a fixed square radius.  It
is obtained by applying the existing zero-free theorem to four rectangles
and cancelling their internal sides. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_onePunctureSquareCauchyGreen
    (x tau l r b u q : ℝ) (rho : NontrivialZetaZero)
    (hq : 0 < q)
    (hl : l < (suzukiChebyshevLaplaceZeroCoordinate rho).re - q)
    (hr : (suzukiChebyshevLaplaceZeroCoordinate rho).re + q < r)
    (hb : b < (suzukiChebyshevLaplaceZeroCoordinate rho).im - q)
    (hu : (suzukiChebyshevLaplaceZeroCoordinate rho).im + q < u)
    (hdomain :
      (([[l, r]] ×ℂ [[b, u]]) \
          {suzukiChebyshevLaplaceZeroCoordinate rho}) ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    rectangularBoundaryIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      rectangularAreaIntegralOutsideCenteredSquare l r b u
          (suzukiChebyshevLaplaceZeroCoordinate rho) q (fun p =>
            suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
              suzukiChebyshevLogAverageLaplacePoleClearedContinuation p) +
        rectangularBoundaryIntegral
          ((suzukiChebyshevLaplaceZeroCoordinate rho).re - q)
          ((suzukiChebyshevLaplaceZeroCoordinate rho).re + q)
          ((suzukiChebyshevLaplaceZeroCoordinate rho).im - q)
          ((suzukiChebyshevLaplaceZeroCoordinate rho).im + q)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) := by
  let c := suzukiChebyshevLaplaceZeroCoordinate rho
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
  let G : ℂ → ℂ := fun p =>
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation p
  obtain ⟨hleftDomain, hbottomDomain, htopDomain, hrightDomain⟩ :=
    fourRectanglesOutsideCenteredSquare_subset_of_rectangle_diff_singleton_subset
      l r b u c q hq (by simpa [c] using hl) (by simpa [c] using hr)
        (by simpa [c] using hb) (by simpa [c] using hu) (by simpa [c] using hdomain)
  have hleftInt : rectangularBoundaryIntegrable l (c.re - q) b u F :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau l (c.re - q) b u hleftDomain
  have hbottomInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) b (c.im - q) F :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau (c.re - q) (c.re + q) b (c.im - q) hbottomDomain
  have htopInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im + q) u F :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau (c.re - q) (c.re + q) (c.im + q) u htopDomain
  have hrightInt : rectangularBoundaryIntegrable
      (c.re + q) r b u F :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau (c.re + q) r b u hrightDomain
  have hsquareInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q) F :=
    ⟨hbottomInt.2.1, htopInt.1,
      hrightInt.2.2.2.mono_set (by
        intro y hy
        rw [uIcc_of_le (by linarith : c.im - q ≤ c.im + q)] at hy
        rw [uIcc_of_le (by linarith : b ≤ u)]
        exact ⟨hb.le.trans hy.1, hy.2.trans hu.le⟩),
      hleftInt.2.2.1.mono_set (by
        intro y hy
        rw [uIcc_of_le (by linarith : c.im - q ≤ c.im + q)] at hy
        rw [uIcc_of_le (by linarith : b ≤ u)]
        exact ⟨hb.le.trans hy.1, hy.2.trans hu.le⟩)⟩
  have hdecomp :=
    rectangularBoundaryIntegral_eq_fourPieces_add_centeredSquare
      l r b u c q F hleftInt hbottomInt hsquareInt htopInt hrightInt
  have hleftCG : rectangularBoundaryIntegral l (c.re - q) b u F =
      rectangularAreaIntegral l (c.re - q) b u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_rectangularCauchyGreen
        x tau l (c.re - q) b u hleftDomain
  have hbottomCG : rectangularBoundaryIntegral
      (c.re - q) (c.re + q) b (c.im - q) F =
      rectangularAreaIntegral
        (c.re - q) (c.re + q) b (c.im - q) G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_rectangularCauchyGreen
        x tau (c.re - q) (c.re + q) b (c.im - q) hbottomDomain
  have htopCG : rectangularBoundaryIntegral
      (c.re - q) (c.re + q) (c.im + q) u F =
      rectangularAreaIntegral
        (c.re - q) (c.re + q) (c.im + q) u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_rectangularCauchyGreen
        x tau (c.re - q) (c.re + q) (c.im + q) u htopDomain
  have hrightCG : rectangularBoundaryIntegral (c.re + q) r b u F =
      rectangularAreaIntegral (c.re + q) r b u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_rectangularCauchyGreen
        x tau (c.re + q) r b u hrightDomain
  rw [hdecomp, hleftCG, hbottomCG, htopCG, hrightCG]
  simp only [rectangularAreaIntegralOutsideCenteredSquare]
  ring

/-- The one-puncture improper Cauchy--Green area integral exists and is
exactly the outer boundary integral minus the local heat-weighted residue.
No integrability across the pole and no limit exchange are assumed. -/
theorem tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau l r b u : ℝ) (rho : NontrivialZetaZero)
    (hl : l < (suzukiChebyshevLaplaceZeroCoordinate rho).re)
    (hr : (suzukiChebyshevLaplaceZeroCoordinate rho).re < r)
    (hb : b < (suzukiChebyshevLaplaceZeroCoordinate rho).im)
    (hu : (suzukiChebyshevLaplaceZeroCoordinate rho).im < u)
    (hdomain :
      (([[l, r]] ×ℂ [[b, u]]) \
          {suzukiChebyshevLaplaceZeroCoordinate rho}) ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    Tendsto
      (fun q : ℝ =>
        rectangularAreaIntegralOutsideCenteredSquare l r b u
          (suzukiChebyshevLaplaceZeroCoordinate rho) q (fun p =>
            suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
              suzukiChebyshevLogAverageLaplacePoleClearedContinuation p))
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (suzukiChebyshevLaplaceZeroCoordinate rho) *
            (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  let c := suzukiChebyshevLaplaceZeroCoordinate rho
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
  let G : ℂ → ℂ := fun p =>
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation p
  have hsquare :=
    tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho
  have hlimit : Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral l r b u F -
        rectangularBoundaryIntegral
          (c.re - q) (c.re + q) (c.im - q) (c.im + q) F)
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u F -
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c *
            (analyticZetaZeroMultiplicity rho : ℂ)))) := by
    simpa [F, c] using tendsto_const_nhds.sub hsquare
  have hleftRange : Ioo (0 : ℝ) (c.re - l) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by simpa [c] using sub_pos.mpr hl)
  have hrightRange : Ioo (0 : ℝ) (r - c.re) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by simpa [c] using sub_pos.mpr hr)
  have hbottomRange : Ioo (0 : ℝ) (c.im - b) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by simpa [c] using sub_pos.mpr hb)
  have htopRange : Ioo (0 : ℝ) (u - c.im) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (by simpa [c] using sub_pos.mpr hu)
  apply hlimit.congr'
  filter_upwards [hleftRange, hrightRange, hbottomRange, htopRange]
      with q hql hqr hqb hqu
  have hexact :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_onePunctureSquareCauchyGreen
      x tau l r b u q rho hql.1
        (by simpa [c] using (show l < c.re - q by linarith [hql.2]))
        (by simpa [c] using (show c.re + q < r by linarith [hqr.2]))
        (by simpa [c] using (show b < c.im - q by linarith [hqb.2]))
        (by simpa [c] using (show c.im + q < u by linarith [hqu.2]))
        hdomain
  dsimp [F, G, c] at hexact ⊢
  rw [hexact]
  ring

/-- Selected form of the one-puncture improper area identity, exposing the
exact RH-detecting boundary-heat coefficient. -/
theorem tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
    (x tau l r b u : ℝ) (rho : NontrivialZetaZero)
    (hrho : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0)
    (hl : l < (suzukiChebyshevLaplaceZeroCoordinate rho).re)
    (hr : (suzukiChebyshevLaplaceZeroCoordinate rho).re < r)
    (hb : b < (suzukiChebyshevLaplaceZeroCoordinate rho).im)
    (hu : (suzukiChebyshevLaplaceZeroCoordinate rho).im < u)
    (hdomain :
      (([[l, r]] ×ℂ [[b, u]]) \
          {suzukiChebyshevLaplaceZeroCoordinate rho}) ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    Tendsto
      (fun q : ℝ =>
        rectangularAreaIntegralOutsideCenteredSquare l r b u
          (suzukiChebyshevLaplaceZeroCoordinate rho) q (fun p =>
            suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
              suzukiChebyshevLogAverageLaplacePoleClearedContinuation p))
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  simpa [suzukiChebyshevLaplaceBoundaryHeatResidue, hrho] using
    tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau l r b u rho hl hr hb hu hdomain

end

end RiemannGaussian
