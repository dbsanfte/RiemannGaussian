/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAdaptiveRateAudit

/-!
# Quantifier audit for two literature transfer proposals

The least-prime duality estimate has an explicit log(y)/log(x) cost.
Even allowing the auxiliary cutoff to vary arbitrarily with the moment
order, that allowance grows after multiplication by the source envelope
on the literal core. This does not assert that the signed sum grows.

The displayed sharp-cutoff hybrid Euler--Hadamard error envelope also
fails at fixed height and increasing prime cutoff, for every choice of
integration-by-parts order. An upper envelope growing is not a lower
bound for the actual error, or an impossibility theorem for the exact
hybrid identity with its zero and pole terms retained.
-/

namespace RiemannGaussian.ZetaRieszDualityRateAudit
noncomputable section
open Filter Topology

/-- The two explicit terms in the least-prime duality allowance, with
`t = log x`, `a = log y`, and `e` the prime-density error supremum. -/
def dualityAllowance (t a e : ℝ) : ℝ := e*Real.log (t/a)+a/t

/-- Increasing or adapting the auxiliary cutoff cannot remove the
explicit inverse-logarithmic term in this particular upper envelope. -/
theorem dualityAllowance_lower {t a e : ℝ}
    (ha : Real.log 2 ≤ a) (hat : 2*a ≤ t) (he : 0 ≤ e) :
    Real.log 2/t ≤ dualityAllowance t a e := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := hl.trans_le ha
  have ht : 0 < t := by linarith
  have hta : 1 ≤ t/a := (le_div_iff₀ ha0).mpr (by linarith)
  have hterm := mul_nonneg he (Real.log_nonneg hta)
  have hdiv := div_le_div_of_nonneg_right ha ht.le
  dsimp [dualityAllowance]
  linarith

/-- This audits all auxiliary-cutoff schedules at once, even with a
vanishing prime-density error. The target is the stated allowance, not
the original arithmetic packet and not a claimed transfer theorem. -/
theorem adaptive_duality_allowance_tendsto {u : ℝ} (hu : 1/2 < u)
    (t a e : ℕ → ℝ)
    (h : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ a N ∧ 2*a N ≤ t N ∧
      t N ≤ (203/100 : ℝ)*N ∧ 0 ≤ e N) :
    Tendsto (fun N : ℕ => (2*u)^N*dualityAllowance (t N) (a N) (e N))
      atTop atTop := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg := (ZetaRieszShiftedCenter.polynomial_source_ratio_tendsto hu 1).const_mul_atTop
    (show 0 < (100/203 : ℝ)*Real.log 2 by positivity)
  apply Filter.tendsto_atTop_mono' _ ?_ hg
  filter_upwards [h] with N hN
  obtain ⟨ha, hat, htN, he⟩ := hN
  have ht : 0 < t N := by linarith
  have hratio : (100/203 : ℝ)*Real.log 2/((N : ℝ)+1) ≤ Real.log 2/t N := by
    calc
      _ = Real.log 2/((203/100 : ℝ)*((N : ℝ)+1)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hl.le ht
        (show t N ≤ (203/100 : ℝ)*((N : ℝ)+1) by linarith)
  have hbase := hratio.trans (dualityAllowance_lower ha hat he)
  have hp : 0 ≤ (2*u)^N := pow_nonneg (by linarith) _
  convert mul_le_mul_of_nonneg_left hbase hp using 1
  ring

/-- The displayed hybrid-product envelope in logarithmic prime cutoff.
Its order is allowed to depend on that cutoff in the audit below. -/
def hybridEnvelope (t H : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k+2 : ℕ)*t)/(H*t)^k

theorem hybridEnvelope_lower {t H : ℝ} (ht : 0 < t) (hH : 0 < H)
    (hscale : H*t ≤ Real.exp t) (k : ℕ) :
    Real.exp (2*t) ≤ hybridEnvelope t H k := by
  have hp := pow_le_pow_left₀ (mul_pos hH ht).le hscale k
  have hm := mul_le_mul_of_nonneg_left hp (le_of_lt (Real.exp_pos (2*t)))
  rw [hybridEnvelope, le_div_iff₀ (pow_pos (mul_pos hH ht) k)]
  convert hm using 1
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- No choice of the integration-by-parts order makes this published
sharp-cutoff envelope small when height is fixed and prime cutoff grows.
The implicit constants of the literature theorem are not assumed uniform
in that order, and no assertion about the actual approximation error is made. -/
theorem adaptive_hybrid_envelope_tendsto {H : ℝ} (hH : 0 < H)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (k : ℕ → ℕ) :
    Tendsto (fun N => hybridEnvelope (t N) H (k N)) atTop atTop := by
  have hr : Tendsto (fun x : ℝ => Real.exp x/x) atTop atTop := by
    simpa using tendsto_exp_mul_div_rpow_atTop (1 : ℝ) 1 (by norm_num)
  have hs : ∀ᶠ N : ℕ in atTop, H*t N ≤ Real.exp (t N) := by
    filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ)),
      (hr.comp ht).eventually (eventually_ge_atTop H)] with N hn hN
    exact (le_div_iff₀ hn).mp hN
  have hg : Tendsto (fun N => Real.exp (2*t N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (ht.const_mul_atTop (by norm_num))
  apply Filter.tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hs, ht.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hn
  exact hybridEnvelope_lower hn hH hN (k N)

end
end RiemannGaussian.ZetaRieszDualityRateAudit
