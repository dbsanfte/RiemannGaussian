import RiemannGaussian.RiemannXiSuzukiRealAxisLerchL2

/-!
# Suzuki's complete positive-time arithmetic signal in `L²(ℝ)`

All five real-axis components of Suzuki's arithmetic formula have now been
proved square-integrable.  This file performs the final literal assembly.
The carrier-weighted restriction of `riemannXiSuzukiArithmeticPPositive` is
proved pointwise equal to the sum of the pole, zeta, finite-prime, standalone
digamma, and Hurwitz--Lerch blocks.  Their checked `MemLp · 2` theorems then
compose by finite addition.

Thus the positive-time form of Suzuki's `S_t ∈ L²(ℝ)` proposition is a theorem
about the actual arithmetic expression, not an asymptotic placeholder or a
spectral-side assumption.  The signal is also packaged as a genuine
`Lp ℂ 2 ℝ` element for the subsequent norm and Gram analysis.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Suzuki's complete carrier-weighted positive-time arithmetic signal on
the real spectral axis. -/
def suzukiRealAxisArithmeticSignalPositive (t x : ℝ) : ℂ :=
  riemannXiSuzukiArithmeticSignalPositive t (x : ℂ)

/-- The full real-axis arithmetic signal is pointwise the sum of the five
carrier-weighted components already proved square-integrable. -/
theorem suzukiRealAxisArithmeticSignalPositive_eq_components
    (t x : ℝ) :
    suzukiRealAxisArithmeticSignalPositive t x =
      suzukiRealAxisCarrierPoleContribution t x +
        suzukiRealAxisCarrierZetaContribution t x +
          suzukiRealAxisCarrierPrimeContribution t x +
            suzukiRealAxisCarrierDigammaContribution x +
              suzukiRealAxisCarrierLerchContribution t x := by
  unfold suzukiRealAxisArithmeticSignalPositive
    riemannXiSuzukiArithmeticSignalPositive
    riemannXiSuzukiArithmeticPPositive
    suzukiRealAxisCarrierPoleContribution
    suzukiRealAxisCarrierZetaContribution
    suzukiRealAxisCarrierPrimeContribution
    suzukiRealAxisCarrierDigammaContribution
    suzukiRealAxisCarrierLerchContribution
    suzukiRealAxisXiZeroCarrier
    suzukiRealAxisDigammaContribution
    suzukiRealAxisLerchContribution
  ring

/-- Suzuki's complete positive-time arithmetic signal belongs to `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisArithmeticSignalPositive
    {t : ℝ} (ht : 0 < t) :
    MemLp (suzukiRealAxisArithmeticSignalPositive t) 2 := by
  have hcomponents :=
    ((((memLp_two_suzukiRealAxisCarrierPoleContribution t).add
      (memLp_two_suzukiRealAxisCarrierZetaContribution t)).add
        (memLp_two_suzukiRealAxisCarrierPrimeContribution t)).add
          memLp_two_suzukiRealAxisCarrierDigammaContribution).add
            (memLp_two_suzukiRealAxisCarrierLerchContribution ht)
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦
    suzukiRealAxisArithmeticSignalPositive_eq_components t x)).2
  exact hcomponents

/-- Literal formulation of the preceding theorem directly in terms of the
previously defined complex arithmetic signal. -/
theorem memLp_two_riemannXiSuzukiArithmeticSignalPositive_ofReal
    {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : ℝ ↦
      riemannXiSuzukiArithmeticSignalPositive t (x : ℂ)) 2 := by
  exact memLp_two_suzukiRealAxisArithmeticSignalPositive ht

/-- Suzuki's complete positive-time arithmetic signal as an actual element of
the Hilbert space `L²(ℝ, ℂ)`. -/
def suzukiRealAxisArithmeticSignalPositiveLp
    (t : ℝ) (ht : 0 < t) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_suzukiRealAxisArithmeticSignalPositive ht).toLp
    (suzukiRealAxisArithmeticSignalPositive t)

/-- The `L²` equivalence class has the literal arithmetic signal as a
representative almost everywhere. -/
theorem suzukiRealAxisArithmeticSignalPositiveLp_ae
    (t : ℝ) (ht : 0 < t) :
    suzukiRealAxisArithmeticSignalPositiveLp t ht =ᵐ[volume]
      suzukiRealAxisArithmeticSignalPositive t :=
  MemLp.coeFn_toLp (memLp_two_suzukiRealAxisArithmeticSignalPositive ht)

end

end RiemannGaussian
