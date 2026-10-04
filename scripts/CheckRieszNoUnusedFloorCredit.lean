import RiemannGaussian.ZetaRieszPairPrefixPayment
import Mathlib.Tactic.Linter

/-! A focused audit of the existing two-sided ledger, outside ordinary CI.
This gives no new floor payment or bound on the retained signed pair. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Filter Topology

namespace RiemannGaussian.ZetaRieszNoUnusedFloorCredit
open ZetaRieszPairPrefixPayment ZetaRieszSignedSelbergPayment
open ZetaRieszLowCountSignedBoundary ZetaRieszPrimeCountFrequency

/-- The aggregate discrepancy in the already checked floor reduction.
This is an audit quantity, not a replacement arithmetic carrier. -/
def gap (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
    (prefixPairDefect u y (dyadicMomentOrder j)).re+
    (literalSelberg u y (dyadicMomentOrder j)).re

/-- No phase or Selberg term is discarded when the gap is collected. -/
theorem gap_eq (u y : ℝ) (j : ℕ) :
    gap u y j=
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
      lowCountPeriods u y j+
      (prefixPairDefect u y (dyadicMomentOrder j)-
        literalPairDefect u y (dyadicMomentOrder j)).re := by
  rw [gap,lowCountPeriods_eq,Complex.sub_re]
  ring

/-- BOTH signs of the whole discrepancy have the existing geometric
price. An additional fixed positive reserve cannot be hidden here. -/
theorem eventually_abs_gap_le {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop, |gap u y j| ≤ nativeSignedPeriodBudget u y j+
      prefixBudget (dyadicMomentOrder j) := by
  filter_upwards [eventually_native_signed_period_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
    with j hj hN
  have he := (Complex.abs_re_le_norm
    (prefixPairDefect u y (dyadicMomentOrder j)-
      literalPairDefect u y (dyadicMomentOrder j))).trans
        (by simpa only [norm_sub_rev] using
          norm_literalPairDefect_sub_prefix_le hu.le hU hN hy)
  rw [gap_eq]
  exact (abs_add_le _ _).trans (add_le_add hj he)

/-- This gap vanishes independently of any hypothetical zero. It
does not say that the signed pair or any individual sector vanishes. -/
theorem gap_tendsto {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    Tendsto (gap u y) atTop (𝓝 0) := by
  have hb := (nativeSignedPeriodBudget_tendsto u y).add
    (prefixBudget_tendsto.comp tendsto_dyadicMomentOrder)
  simp only [add_zero] at hb
  apply squeeze_zero_norm' ?_ hb
  simpa only [Real.norm_eq_abs,Function.comp_def] using eventually_abs_gap_le hu hU hy

/-- A fixed positive aggregate credit is incompatible with the already
proved ledger. This does not exclude credits inside the unpaid pair. -/
theorem not_frequently_fixed_gap_credit {u y c : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|)
    (hc : 0 < c) : ¬∃ᶠ j in atTop, c ≤ gap u y j := by
  intro hf
  have hh : c ≤ (0 : ℝ) := ge_of_tendsto_of_frequently
    (gap_tendsto hu hU hy) hf
  exact (not_le_of_gt hc) hh

end RiemannGaussian.ZetaRieszNoUnusedFloorCredit

#lint+ in RiemannGaussian.ZetaRieszNoUnusedFloorCredit
#print axioms RiemannGaussian.ZetaRieszNoUnusedFloorCredit.gap_eq
#print axioms RiemannGaussian.ZetaRieszNoUnusedFloorCredit.eventually_abs_gap_le
#print axioms RiemannGaussian.ZetaRieszNoUnusedFloorCredit.gap_tendsto
#print axioms RiemannGaussian.ZetaRieszNoUnusedFloorCredit.not_frequently_fixed_gap_credit
