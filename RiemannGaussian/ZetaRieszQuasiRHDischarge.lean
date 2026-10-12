/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentTerminal
import RiemannGaussian.ZetaRieszCoupledArithmeticBound

/-!
# Transfer of an external quasi-RH theorem to the frozen Riesz endpoint

The general transfer accepts a zero-free half-plane strictly containing the
original campaign target. Each input is a theorem parameter, not a new axiom.
Instantiating it requires a separately pinned and checked external proof;
this module alone does not verify that proof or establish its premise.

The transfer gives the original closed campaign strip, its all-height
prime-moment non-coherence, and the literal terminal `NoPersistentError`.
It does not prove the Riesz carrier floor or ceiling, or full RH. The larger
radius consequence has a STRICT upper bound `u < 5/8`: the published theorem
does not exclude zeros on `Re(s) = 7/8`.

The `23/24` intermediate theorem in OpenAI's proof already suffices for the
original endpoint. Its smaller dependency chain can instantiate the general
transfer without first rebuilding the stronger `7/8` theorem.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace RiemannGaussian.ZetaRieszQuasiRHDischarge
open ZetaPrimeMomentCoherence ZetaPrimeMomentNoncoherence
open ZetaPrimeMomentNoncoherenceStrip ZetaPrimeMomentChebyshev
open ZetaRieszCoupledSignedBound ZetaRieszPairPrimePowerPayment

/-- An external baseline for Mathlib's actual zeta function. -/
def HalfPlaneNonvanishing (sigma : ℝ) : Prop :=
  ∀ s : ℂ, sigma < s.re → riemannZeta s ≠ 0

/-- The precise strongest published input, when its proof is instantiated. -/
def SevenEighthsNonvanishing : Prop :=
  HalfPlaneNonvanishing (7/8)

/-- Any zero-free half-plane strictly containing the original closed strip
supplies the frozen zero-free endpoint. -/
theorem campaign_nonvanishing_of_halfPlane {sigma : ℝ}
    (hsigma : sigma < 19999/20000) (hne : HalfPlaneNonvanishing sigma) :
    ∀ s : ℂ, (19999/20000 : ℝ) ≤ s.re → riemannZeta s ≠ 0 := by
  intro s hs
  exact hne s (hsigma.trans_le hs)

/-- The independent external baseline excludes each source whose candidate
lies in its half-plane, within the checked converse-coherence radius domain. -/
theorem noncoherent_of_halfPlane {sigma u : ℝ} (hne : HalfPlaneNonvanishing sigma)
    (hu : 0 < u) (hu1 : u < 1) (hsigma : sigma < 3/2-u) (y : ℝ) :
    Noncoherent u y := by
  apply noncoherent_of_nonvanishing hu hu1
  exact hne (candidate u y) (by simpa only [candidate_re] using hsigma)

/-- The original all-height prime-moment premise follows from any sufficient
external half-plane. The existing equivalence selects exposure internally. -/
theorem campaign_noncoherent_of_halfPlane {sigma : ℝ}
    (hsigma : sigma < 19999/20000) (hne : HalfPlaneNonvanishing sigma) :
    StripNoncoherent campaignRadius :=
  campaign_noncoherent_iff_nonvanishing.mpr
    (campaign_nonvanishing_of_halfPlane hsigma hne)

/-- General discharge of the exact frozen Chebyshev-error terminal condition. -/
theorem noPersistentError_of_halfPlane {sigma : ℝ}
    (hsigma : sigma < 19999/20000) (hne : HalfPlaneNonvanishing sigma) :
    ZetaPrimeMomentTerminal.NoPersistentError :=
  ZetaPrimeMomentTerminal.noncoherent_iff_noPersistentError.mp
    (campaign_noncoherent_of_halfPlane hsigma hne)

/-- The frozen campaign's closed target lies strictly inside the new half-plane. -/
theorem campaign_nonvanishing (hne : SevenEighthsNonvanishing) :
    ∀ s : ℂ, (19999/20000 : ℝ) ≤ s.re → riemannZeta s ≠ 0 :=
  campaign_nonvanishing_of_halfPlane (by norm_num) hne

/-- At every height, the external baseline excludes every positive-integer
source on the strictly enlarged radius interval. No exposure is assumed. -/
theorem noncoherent_of_lt_five_eighths (hne : SevenEighthsNonvanishing)
    {u : ℝ} (hu : 1/2 < u) (hU : u < 5/8) (y : ℝ) : Noncoherent u y := by
  apply noncoherent_of_nonvanishing (by linarith) (by linarith)
  apply hne
  rw [candidate_re]
  linarith

/-- Each closed radius strip strictly below `5/8` is non-coherent. -/
theorem strip_noncoherent_of_lt_five_eighths (hne : SevenEighthsNonvanishing)
    {U : ℝ} (hU : U < 5/8) : StripNoncoherent U := by
  intro u hu huU y
  exact noncoherent_of_lt_five_eighths hne hu (huU.trans_lt hU) y

/-- Discharge of the original all-height, all-multiplicity campaign premise. -/
theorem campaign_noncoherent (hne : SevenEighthsNonvanishing) :
    StripNoncoherent campaignRadius :=
  strip_noncoherent_of_lt_five_eighths hne (by norm_num [campaignRadius])

/-- The frozen terminal condition follows through its checked equivalence,
using the actual centered Chebyshev error and its original height domain. -/
theorem noPersistentError (hne : SevenEighthsNonvanishing) :
    ZetaPrimeMomentTerminal.NoPersistentError :=
  ZetaPrimeMomentTerminal.noncoherent_iff_noPersistentError.mp
    (campaign_noncoherent hne)

/-- The literal error source cannot have a negative-integer limit throughout
the enlarged interval wherever the checked error-to-prime transfer applies. -/
theorem no_errorSource_limit (hne : SevenEighthsNonvanishing)
    {u y : ℝ} (hu : 1/2 < u) (hU : u < 5/8) (hy : 1 ≤ |y|)
    {m : ℕ} (hm : 0 < m) :
    ¬ Tendsto (errorSource u y) atTop (𝓝 (-(m : ℂ))) := by
  intro ht
  exact noncoherent_of_lt_five_eighths hne hu hU y m hm
    ((errorSource_tendsto_iff (by linarith) (by linarith) hy _).mp ht)

/-- The external half-plane supplies a fixed genuine Cauchy disk at every
campaign height. Its left edge is `9/10 > 7/8`; the zeta pole is outside. -/
theorem analytic_three_fifths (hne : SevenEighthsNonvanishing)
    {y : ℝ} (hy : 54 ≤ |y|) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (Metric.closedBall (3/2 + Complex.I*y) (3/5)) := by
  intro s hs
  have hd : ‖s-(3/2+Complex.I*y)‖ ≤ (3/5 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hr : (7/8 : ℝ) < s.re := by
    have hl := (abs_le.mp ((Complex.abs_re_le_norm
      (s-(3/2+Complex.I*y))).trans hd)).1
    norm_num at hl
    linarith
  have hs1 : s ≠ 1 := by
    intro he
    have hi := (Complex.abs_im_le_norm (s-(3/2+Complex.I*y))).trans hd
    rw [he] at hi
    norm_num at hi
    linarith
  have ha := analyticOn_riemannZeta s
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs1)
  exact (ha.deriv.div ha (hne s hr)).neg

/-- All literal ordinary-prime moments, including order zero, acquire the
fixed radius `3/5`. The constant depends on height; the radius does not. -/
theorem exists_ordinary_radius_bound (hne : SevenEighthsNonvanishing)
    {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖ ≤ C/(3/5 : ℝ)^k :=
  ZetaRieszJoinedPhaseRadius.ordinary_moment_bound_of_analytic_radius
    (by norm_num) (by norm_num) (analytic_three_fifths hne hy)

/-- A uniform geometric payment of the canonical joined energy minus its
full correlation credit, CONDITIONAL on the external quasi-RH theorem.
Every ordinary-prime order and complex phase is retained. This does not
independently prove the upstream input or a larger RH statement. -/
theorem exists_coupled_geometric_bound (hne : SevenEighthsNonvanishing)
    {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1/2 ≤ u →
      u ≤ ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ, 65536 ≤ N →
        |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
          correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
            (41/12 : ℝ)*C^2*(10001/12000 : ℝ)^(N-1) := by
  obtain ⟨C,hC,hm⟩ := exists_ordinary_radius_bound hne hy
  refine ⟨C,hC,?_⟩
  intro u hu hU N hN
  have hu0 : 0 ≤ u := by linarith
  have hUq : u ≤ (10001/20000 : ℝ) := hU
  have hu1 : u ≤ 1 := by linarith
  have hq : u/(3/5 : ℝ) ≤ (10001/12000 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3/5)).mpr
    linarith
  have hp : (u/(3/5 : ℝ))^(N-1) ≤ (10001/12000 : ℝ)^(N-1) :=
    pow_le_pow_left₀ (by positivity) hq _
  have hc : (C*u)^2 ≤ C^2 := by
    have hcu : C*u ≤ C := by nlinarith
    exact pow_le_pow_left₀ (by positivity) hcu _
  apply (ZetaRieszCoupledArithmeticBound.abs_ordinary_energy_sub_credit_le
    (by norm_num) hu hU hm hN).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hp
    (by positivity) (by positivity)

/-- An assumed nontrivial zero in the original campaign gives a contradiction
directly, for every multiplicity, without a Riesz carrier inequality. -/
theorem false_of_campaign_zero (hne : SevenEighthsNonvanishing)
    (rho : NontrivialZetaZero) (hstrip : (19999/20000 : ℝ) ≤ rho.1.re) : False :=
  campaign_nonvanishing hne rho.1 hstrip rho.2.1

end RiemannGaussian.ZetaRieszQuasiRHDischarge
