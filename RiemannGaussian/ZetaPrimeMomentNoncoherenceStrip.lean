/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentNoncoherence
import RiemannGaussian.ZetaPrimeMomentCoherenceExposed
import RiemannGaussian.ZetaExposedZero

/-!
# A structural zero-free criterion from strip-wide non-coherence

Pointwise non-coherence is not the contrapositive of coherence implying a
zero. The correct global bridge uses exposed-zero SELECTION: any right-half
zero yields an exposed zero at least as far right. Thus non-coherence at
EVERY height and radius in a strip excludes every zero in that strip. The
criterion itself has no exposure premise, no Riesz floor and no unproved
zero-to-coherence assumption. All arithmetic non-coherence/block-deviation
premises remain explicit; no additional zero-free region is proved here.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip
open ZetaPrimeMomentCoherence ZetaPrimeMomentNoncoherence

/-- The current restricted campaign radius, corresponding to `Re(s)≥0.99995`. -/
def campaignRadius : ℝ := 10001/20000

/-- The arithmetic hypothesis covers every radius up to `U` and every height.
It must cover zeros reached by the proved rightward exposed-zero selection. -/
def StripNoncoherent (U : ℝ) : Prop :=
  ∀ u : ℝ, 1/2<u → u≤U → ∀ y : ℝ, Noncoherent u y

/-- A zeta zero with positive real part is nontrivial; the junk value at
the pole is already nonzero by the known `Re(s)≥1` nonvanishing theorem. -/
private theorem nontrivial_of_zero {s : ℂ} (hs : 0<s.re)
    (hz : riemannZeta s=0) : IsNontrivialZetaZero s := by
  have h1 : s≠1 := by
    intro he
    subst s
    exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hz
  apply isNontrivialZetaZero_of_poleRemoved_eq_zero hs
  rw [riemannZeta₁_eq_sub_one_mul h1, hz, mul_zero]

/-- Any hypothetical zero in the strip produces an actual coherent
moment sequence somewhere in the SAME strip, with its positive integer
analytic multiplicity. Exposure is selected internally, not assumed. -/
theorem exists_coherent_source_in_strip {U : ℝ} (hU : U<1)
    (rho0 : NontrivialZetaZero) (hstrip : 3/2-U≤rho0.1.re) :
    ∃ u y : ℝ, 1/2<u ∧ u≤U ∧ ∃ m : ℕ, 0<m ∧
      Tendsto (moments u y) atTop (𝓝 (-(m : ℂ))) := by
  have hrho0 : 1/2<rho0.1.re := by linarith
  obtain ⟨rho, hright, hexposed⟩ :=
    ZetaExposedZero.exists_exposed_right_half_zero rho0 hrho0
  have hrho : 1/2<rho.1.re := hrho0.trans_le hright
  refine ⟨3/2-rho.1.re, rho.1.im,
    by linarith [NontrivialZetaZero.re_lt_one rho], by linarith,
    analyticZetaZeroMultiplicity rho, analyticZetaZeroMultiplicity_positive rho, ?_⟩
  exact (ZetaPrimeMomentCoherenceExposed.multiplicity_iff_source rho hrho hexposed
    (analyticZetaZeroMultiplicity_positive rho)).mp rfl

/-- Strip-wide non-coherence gives a zero-free strip without an exposure
premise. The conclusion is CONDITIONAL on the unproved arithmetic premise. -/
theorem nonvanishing_of_strip_noncoherent {U : ℝ} (hU : U<1)
    (hnc : StripNoncoherent U) {s : ℂ} (hs : 3/2-U≤s.re) :
    riemannZeta s≠0 := by
  intro hz
  let rho0 : NontrivialZetaZero := ⟨s, nontrivial_of_zero (by linarith) hz⟩
  obtain ⟨u,y,hu,huU,m,hm,ha⟩ := exists_coherent_source_in_strip hU rho0 hs
  exact hnc u hu huU y m hm ha

/-- At a fixed candidate, it suffices to exclude coherence at every
possibly selected rightward radius and height. This strengthens the
pointwise premise rather than incorrectly reversing the converse theorem. -/
theorem candidate_nonvanishing_of_strip_noncoherent {u y : ℝ} (hu1 : u<1)
    (hnc : StripNoncoherent u) : riemannZeta (candidate u y)≠0 := by
  exact nonvanishing_of_strip_noncoherent hu1 hnc (by simp)

/-- The converse coherence theorem proves the reverse global direction:
an actually zero-free strip cannot contain a negative-integer source. -/
theorem strip_noncoherent_iff_nonvanishing {U : ℝ} (hU : U<1) :
    StripNoncoherent U ↔ ∀ s : ℂ, 3/2-U≤s.re → riemannZeta s≠0 := by
  constructor
  · intro hnc s hs
    exact nonvanishing_of_strip_noncoherent hU hnc hs
  · intro hne u hu huU y
    exact noncoherent_of_nonvanishing (by linarith) (huU.trans_lt hU)
      (hne (candidate u y) (by simp; linarith))

/-- Positive block-deviation limsup everywhere in the strip suffices.
This is an implication for an arithmetic theorem to supply, not that theorem. -/
theorem nonvanishing_of_strip_block_limsup {U : ℝ} (hU : U<1)
    (hdev : ∀ u : ℝ, 1/2<u → u≤U → ∀ y : ℝ, ∀ m : ℕ, 0<m →
      0<limsup (blockDeviation (moments u y) m) atTop)
    {s : ℂ} (hs : 3/2-U≤s.re) : riemannZeta s≠0 := by
  apply nonvanishing_of_strip_noncoherent hU _ hs
  intro u hu huU y
  exact noncoherent_of_pos_limsup (hdev u hu huU y)

/-- Cofinal positive block deviations are sufficient even when the real
deviations are unbounded. Constants may depend on radius, height and count. -/
theorem nonvanishing_of_strip_cofinalBlockDeviation {U : ℝ} (hU : U<1)
    (hdev : ∀ u : ℝ, 1/2<u → u≤U → ∀ y : ℝ, ∀ m : ℕ, 0<m →
      CofinalBlockDeviation (moments u y) m)
    {s : ℂ} (hs : 3/2-U≤s.re) : riemannZeta s≠0 := by
  apply nonvanishing_of_strip_noncoherent hU _ hs
  intro u hu huU y
  exact noncoherent_of_cofinalBlockDeviation (hdev u hu huU y)

/-- The canonical campaign premise: no negative-integer coherent source
at any permitted fixed radius and height. No block or norm hypothesis is
required; exposed-zero selection and the forward/converse sources are
composed by the general strip criterion. -/
theorem campaign_nonvanishing_of_noncoherent
    (hnc : StripNoncoherent campaignRadius)
    {s : ℂ} (hs : (19999/20000 : ℝ)≤s.re) : riemannZeta s≠0 := by
  apply nonvanishing_of_strip_noncoherent (U := campaignRadius)
    (by norm_num [campaignRadius]) hnc
  dsimp [campaignRadius]
  linarith

/-- The weakest canonical premise is exactly equivalent to zero freeness
of the target strip. This is a structural characterization, not an
independent arithmetic proof of either side. -/
theorem campaign_noncoherent_iff_nonvanishing :
    StripNoncoherent campaignRadius ↔
      ∀ s : ℂ, (19999/20000 : ℝ)≤s.re → riemannZeta s≠0 := by
  simpa only [campaignRadius,
    show (3/2-10001/20000 : ℝ)=19999/20000 by norm_num] using
    strip_noncoherent_iff_nonvanishing
      (U := campaignRadius) (by norm_num [campaignRadius])

/-- Sufficient corollary of the canonical non-coherence endpoint: a block
non-coherence theorem at all heights and
`1/2<u≤10001/20000` excludes all zeros with `Re(s)≥19999/20000`.
No arithmetic block lower bound is asserted by this structural theorem. -/
theorem campaign_nonvanishing_of_block_limsup
    (hdev : ∀ u : ℝ, 1/2<u → u≤campaignRadius → ∀ y : ℝ, ∀ m : ℕ, 0<m →
      0<limsup (blockDeviation (moments u y) m) atTop)
    {s : ℂ} (hs : (19999/20000 : ℝ)≤s.re) : riemannZeta s≠0 := by
  apply campaign_nonvanishing_of_noncoherent _ hs
  intro u hu huU y
  exact noncoherent_of_pos_limsup (hdev u hu huU y)

/-- Equivalent campaign endpoint in the cofinal fixed-gap formulation. -/
theorem campaign_nonvanishing_of_cofinalBlockDeviation
    (hdev : ∀ u : ℝ, 1/2<u → u≤campaignRadius → ∀ y : ℝ, ∀ m : ℕ, 0<m →
      CofinalBlockDeviation (moments u y) m)
    {s : ℂ} (hs : (19999/20000 : ℝ)≤s.re) : riemannZeta s≠0 := by
  apply campaign_nonvanishing_of_noncoherent _ hs
  intro u hu huU y
  exact noncoherent_of_cofinalBlockDeviation (hdev u hu huU y)

end RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip
