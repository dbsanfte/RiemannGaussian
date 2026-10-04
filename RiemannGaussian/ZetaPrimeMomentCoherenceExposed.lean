/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentCoherence
import RiemannGaussian.ZetaRieszPrimeCompletionPhase

/-!
# Prime-moment coherence characterizes exposed multiplicity

Exposure is a standing hypothesis for the forward implication. The
converse in `ZetaPrimeMomentCoherence` needs no exposure. This statement
does not assert that moment coherence itself implies exposure.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace RiemannGaussian.ZetaPrimeMomentCoherenceExposed
open ZetaPrimeMomentCoherence

/-- With exposure held fixed, the coherent ordinary-prime source is
equivalent to the specified actual analytic multiplicity. -/
theorem multiplicity_iff_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    {m : ℕ} (hm : 0<m) :
    analyticZetaZeroMultiplicity rho=m ↔
      Tendsto (moments (3/2-rho.1.re) rho.1.im) atTop (𝓝 (-(m : ℂ))) := by
  constructor
  · intro he
    change Tendsto (fun k : ℕ => ((3/2-rho.1.re : ℝ) : ℂ)^(k+1)*
      zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*(rho.1.im : ℂ))) atTop (𝓝 (-(m : ℂ)))
    simpa only [he] using
      ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed
  · intro ha
    apply multiplicity_eq_of_tendsto rho (by linarith [NontrivialZetaZero.re_lt_one rho])
      (by linarith) _ hm ha
    apply Complex.ext <;> simp [candidate,center]

end RiemannGaussian.ZetaPrimeMomentCoherenceExposed
