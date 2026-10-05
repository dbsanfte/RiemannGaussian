/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentChebyshev
import RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip
import RiemannGaussian.ZetaElevenZeroCompleteness

/-!
# Terminal strip equivalence for the frozen prime-moment reduction

The canonical strip-wide non-coherence criterion is exactly equivalent to
absence of the persistent centered factorial transform of the actual
Chebyshev error. Low heights use the existing verified zero completeness;
all other heights retain the literal signed error integral. The arithmetic
premise is not proved here. No new zero-free region or RH claim follows.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace RiemannGaussian.ZetaPrimeMomentTerminal
open ZetaPrimeMomentCoherence ZetaPrimeMomentNoncoherenceStrip
open ZetaPrimeMomentChebyshev

/-- Absence of negative integer sources in the actual centered factorial
transform of `psi-x`, at every campaign radius and every uncovered height.
The finite verified low-height interval is supplied independently. -/
def NoPersistentError : Prop :=
  ∀ u : ℝ, 1/2<u → u≤campaignRadius → ∀ y : ℝ, 54≤|y| →
    ∀ m : ℕ, 0<m →
      ¬ Tendsto (errorSource u y) atTop (𝓝 (-(m : ℂ)))

/-- The actual-prime and actual-error formulations have exactly the same
strip-wide arithmetic premise; no Riesz carrier or exposure is assumed. -/
theorem noncoherent_iff_noPersistentError :
    StripNoncoherent campaignRadius ↔ NoPersistentError := by
  constructor
  · intro hnc u hu hU y hy m hm ht
    exact hnc u hu hU y m hm
      ((errorSource_tendsto_iff (by linarith)
        (by dsimp [campaignRadius] at hU; linarith) (by linarith) _).mp ht)
  · intro herr u hu hU y m hm ht
    by_cases hy : 54≤|y|
    · exact herr u hu hU y hy m hm
        ((errorSource_tendsto_iff (by linarith)
          (by dsimp [campaignRadius] at hU; linarith) (by linarith) _).mpr ht)
    · obtain ⟨rho,hrho,_⟩ := exists_zero_multiplicity_of_tendsto
        (by linarith) (by dsimp [campaignRadius] at hU; linarith) hm ht
      have hheight : |rho.1.im|≤54 := by
        have him : rho.1.im=y := by rw [hrho]; norm_num [candidate,center]
        rw [him]
        exact (lt_of_not_ge hy).le
      have hcritical := ZetaElevenZeroCompleteness.critical_line_through_fiftyFour
        rho hheight
      rw [hrho] at hcritical
      norm_num [candidate,center] at hcritical
      dsimp [campaignRadius] at hU
      linarith

/-- The frozen reduction's terminal equivalence, stated for the actual
zeta strip and actual Chebyshev error. Neither side is newly discharged. -/
theorem campaign_nonvanishing_iff_noPersistentError :
    (∀ s : ℂ, (19999/20000 : ℝ)≤s.re → riemannZeta s≠0) ↔
      NoPersistentError :=
  campaign_noncoherent_iff_nonvanishing.symm.trans
    noncoherent_iff_noPersistentError

end RiemannGaussian.ZetaPrimeMomentTerminal
