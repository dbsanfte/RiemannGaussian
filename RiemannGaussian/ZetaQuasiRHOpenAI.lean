/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Nonvanishing
import RiemannGaussian.ZetaRieszQuasiRHDischarge

/-!
# The pinned OpenAI baseline in the current proof chain

OpenAI's `7/8` nonvanishing proof is imported from revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its exact source hashes,
analytic dependency patches and licenses are in `vendor/openai-quasi-rh`.
The resulting theorems have no external nonvanishing parameter or new axiom.

This external baseline discharges the original restricted Riesz terminal
condition and supplies the larger strict radius interval `u < 5/8`.
The original carrier floor/ceiling and full RH remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace RiemannGaussian.ZetaQuasiRHOpenAI
open ZetaPrimeMomentNoncoherence ZetaPrimeMomentNoncoherenceStrip
open ZetaPrimeMomentChebyshev ZetaRieszCoupledSignedBound
open ZetaRieszPairPrimePowerPayment

/-- The attributed external baseline for the actual Mathlib zeta function. -/
theorem sevenEighthsNonvanishing :
    ZetaRieszQuasiRHDischarge.SevenEighthsNonvanishing := by
  intro s hs
  exact OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- All-height nonvanishing in the upstream strict half-plane. -/
theorem nonvanishing {s : ℂ} (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  sevenEighthsNonvanishing s hs

/-- The complete original closed campaign strip, without an arithmetic premise. -/
theorem campaign_nonvanishing :
    ∀ s : ℂ, (19999/20000 : ℝ) ≤ s.re → riemannZeta s ≠ 0 :=
  ZetaRieszQuasiRHDischarge.campaign_nonvanishing sevenEighthsNonvanishing

/-- The original prime-moment premise at every height and positive multiplicity. -/
theorem campaign_noncoherent : StripNoncoherent campaignRadius :=
  ZetaRieszQuasiRHDischarge.campaign_noncoherent sevenEighthsNonvanishing

/-- Unconditional discharge of the exact frozen Chebyshev-error terminal condition. -/
theorem noPersistentError : ZetaPrimeMomentTerminal.NoPersistentError :=
  ZetaRieszQuasiRHDischarge.noPersistentError sevenEighthsNonvanishing

/-- The larger radius interval retains its strict upper endpoint. -/
theorem noncoherent_of_lt_five_eighths {u : ℝ} (hu : 1/2 < u)
    (hU : u < 5/8) (y : ℝ) : Noncoherent u y :=
  ZetaRieszQuasiRHDischarge.noncoherent_of_lt_five_eighths
    sevenEighthsNonvanishing hu hU y

/-- Every closed radius strip strictly below `5/8` is non-coherent. -/
theorem strip_noncoherent_of_lt_five_eighths {U : ℝ} (hU : U < 5/8) :
    StripNoncoherent U :=
  ZetaRieszQuasiRHDischarge.strip_noncoherent_of_lt_five_eighths
    sevenEighthsNonvanishing hU

/-- The signed error-limit exclusion keeps the proved error-transfer height domain. -/
theorem no_errorSource_limit {u y : ℝ} (hu : 1/2 < u)
    (hU : u < 5/8) (hy : 1 ≤ |y|) {m : ℕ} (hm : 0 < m) :
    ¬ Tendsto (errorSource u y) atTop (𝓝 (-(m : ℂ))) :=
  ZetaRieszQuasiRHDischarge.no_errorSource_limit
    sevenEighthsNonvanishing hu hU hy hm

/-- A hypothetical nontrivial zero in the original campaign yields a contradiction. -/
theorem false_of_campaign_zero (rho : NontrivialZetaZero)
    (hstrip : (19999/20000 : ℝ) ≤ rho.1.re) : False :=
  ZetaRieszQuasiRHDischarge.false_of_campaign_zero
    sevenEighthsNonvanishing rho hstrip

/-- The baseline supplies the fixed genuine Cauchy disk at every campaign height. -/
theorem analytic_three_fifths {y : ℝ} (hy : 54 ≤ |y|) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (Metric.closedBall (3/2 + Complex.I*y) (3/5)) :=
  ZetaRieszQuasiRHDischarge.analytic_three_fifths sevenEighthsNonvanishing hy

/-- Every ordinary-prime moment, including order zero, has radius `3/5`. -/
theorem exists_ordinary_radius_bound {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖ ≤ C/(3/5 : ℝ)^k :=
  ZetaRieszQuasiRHDischarge.exists_ordinary_radius_bound sevenEighthsNonvanishing hy

/-- The canonical joined energy keeps its full correlation credit and geometric decay. -/
theorem exists_coupled_geometric_bound {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1/2 ≤ u →
      u ≤ ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ, 65536 ≤ N →
        |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
          correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
            (41/12 : ℝ)*C^2*(10001/12000 : ℝ)^(N-1) :=
  ZetaRieszQuasiRHDischarge.exists_coupled_geometric_bound sevenEighthsNonvanishing hy

end RiemannGaussian.ZetaQuasiRHOpenAI
