import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverage
import Mathlib.Analysis.PSeries

/-!
# Summability of the smooth Suzuki endpoint drift

The logarithmic-average work identity contains one purely smooth cumulative
term.  This file proves that term cannot grow: the drift from `b` to `b + 1`
is at most `b ^ (-3/2)`, hence the natural-endpoint drift series is summable.

It follows that cumulative signed mass-error work differs from the weighted
Chebyshev logarithmic average plus `log N` by a quantity converging to an
explicit finite constant.  Therefore every unbounded contribution required
at the arithmetic frontier must come from the logarithmic average, not from
the smooth discretization correction.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped BigOperators Topology

/-! ## An inverse-three-halves drift majorant -/

/-- The smooth drift over a unit endpoint step has the elementary upper bound
`1 / (b * sqrt b)` once `b >= 1`. -/
theorem suzukiChebyshevSmoothEndpointDrift_add_one_le_inv_mul_inv_sqrt
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevSmoothEndpointDrift b (b + 1) ≤
      1 / (b * Real.sqrt b) := by
  have hbPos : 0 < b := zero_lt_one.trans_le hb
  have hcPos : 0 < b + 1 := by linarith
  let ratio : ℝ := Real.sqrt ((b + 1) / b)
  have hratioPos : 0 < ratio := by
    dsimp only [ratio]
    exact Real.sqrt_pos.2 (div_pos hcPos hbPos)
  have hdivOne : (1 : ℝ) ≤ (b + 1) / b := by
    exact (le_div_iff₀ hbPos).2 (by linarith)
  have hratioOne : (1 : ℝ) ≤ ratio := by
    dsimp only [ratio]
    simpa using Real.sqrt_le_sqrt hdivOne
  have hlogLower := Real.one_sub_inv_le_log_of_pos hratioPos
  have hlogGap : ratio - 1 - Real.log ratio ≤ (ratio - 1) ^ 2 := by
    calc
      ratio - 1 - Real.log ratio ≤
          ratio - 1 - (1 - ratio⁻¹) :=
        sub_le_sub_left hlogLower (ratio - 1)
      _ = (ratio - 1) ^ 2 / ratio := by
        field_simp [hratioPos.ne']
      _ ≤ (ratio - 1) ^ 2 := by
        rw [div_le_iff₀ hratioPos]
        nlinarith [sq_nonneg (ratio - 1)]
  have hratioSq : ratio ^ 2 = (b + 1) / b := by
    dsimp only [ratio]
    exact Real.sq_sqrt (div_nonneg hcPos.le hbPos.le)
  have hfactor : (ratio - 1) * (ratio + 1) = 1 / b := by
    calc
      (ratio - 1) * (ratio + 1) = ratio ^ 2 - 1 := by ring
      _ = (b + 1) / b - 1 := by rw [hratioSq]
      _ = 1 / b := by
        field_simp [hbPos.ne']
        ring
  have hratioSubNonneg : 0 ≤ ratio - 1 := sub_nonneg.mpr hratioOne
  have htwoMul : 2 * (ratio - 1) ≤ 1 / b := by
    calc
      2 * (ratio - 1) ≤ (ratio + 1) * (ratio - 1) := by
        nlinarith
      _ = 1 / b := by rw [mul_comm, hfactor]
  have hratioSubBound : ratio - 1 ≤ 1 / (2 * b) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)).2
    calc
      (ratio - 1) * (2 * b) = (2 * (ratio - 1)) * b := by ring
      _ ≤ (1 / b) * b :=
        mul_le_mul_of_nonneg_right htwoMul hbPos.le
      _ = 1 := by field_simp [hbPos.ne']
  have hratioSubSq : (ratio - 1) ^ 2 ≤ (1 / (2 * b)) ^ 2 := by
    have hinvNonneg : 0 ≤ 1 / (2 * b) := by positivity
    nlinarith
  have hlogRatio : Real.log ((b + 1) / b) = 2 * Real.log ratio := by
    have hsqrtLog := Real.log_sqrt (div_nonneg hcPos.le hbPos.le)
    dsimp only [ratio]
    linarith
  have hscale : Real.sqrt b * ratio = Real.sqrt (b + 1) := by
    dsimp only [ratio]
    rw [Real.sqrt_div hcPos.le]
    field_simp [(Real.sqrt_pos.2 hbPos).ne']
  have hdrift :
      suzukiChebyshevSmoothEndpointDrift b (b + 1) =
        4 * Real.sqrt b * (ratio - 1 - Real.log ratio) := by
    unfold suzukiChebyshevSmoothEndpointDrift
    simp only [← Real.sqrt_eq_rpow, hlogRatio, ← hscale]
    ring
  have hfactorNonneg : 0 ≤ (4 : ℝ) * Real.sqrt b := by positivity
  calc
    suzukiChebyshevSmoothEndpointDrift b (b + 1) =
        4 * Real.sqrt b * (ratio - 1 - Real.log ratio) := hdrift
    _ ≤ 4 * Real.sqrt b * (ratio - 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogGap hfactorNonneg
    _ ≤ 4 * Real.sqrt b * (1 / (2 * b)) ^ 2 :=
      mul_le_mul_of_nonneg_left hratioSubSq hfactorNonneg
    _ = 1 / (b * Real.sqrt b) := by
      have hsqrtSq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hbPos.le
      field_simp [hbPos.ne', (Real.sqrt_pos.2 hbPos).ne']
      nlinarith

/-- In real-power notation, the unit-step drift is bounded by the summable
majorant `b ^ (-3/2)`. -/
theorem suzukiChebyshevSmoothEndpointDrift_add_one_le_rpow_neg_three_halves
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevSmoothEndpointDrift b (b + 1) ≤
      b ^ (-3 / 2 : ℝ) := by
  calc
    suzukiChebyshevSmoothEndpointDrift b (b + 1) ≤
        1 / (b * Real.sqrt b) :=
      suzukiChebyshevSmoothEndpointDrift_add_one_le_inv_mul_inv_sqrt hb
    _ = b ^ (-3 / 2 : ℝ) := by
      have hbNonneg : 0 ≤ b := hb.trans' (by norm_num)
      have hbPos : 0 < b := zero_lt_one.trans_le hb
      have hprod : b * b ^ (1 / 2 : ℝ) = b ^ (3 / 2 : ℝ) := by
        calc
          b * b ^ (1 / 2 : ℝ) = b ^ (1 : ℝ) * b ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_one]
          _ = b ^ ((1 : ℝ) + 1 / 2) := by
            rw [Real.rpow_add hbPos]
          _ = b ^ (3 / 2 : ℝ) := by norm_num
      have hneg : (-3 / 2 : ℝ) = -(3 / 2 : ℝ) := by ring
      rw [Real.sqrt_eq_rpow, hprod, hneg, Real.rpow_neg hbNonneg]
      simp only [one_div]

/-- Natural-endpoint specialization of the inverse-three-halves majorant. -/
theorem suzukiChebyshevSmoothEndpointDrift_nat_le_rpow_neg_three_halves
    (count : ℕ) :
    suzukiChebyshevSmoothEndpointDrift
        (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ)) ≤
      (((count + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h :=
    suzukiChebyshevSmoothEndpointDrift_add_one_le_rpow_neg_three_halves
      (b := (((count + 2 : ℕ) : ℝ))) (by
        exact_mod_cast (show 1 ≤ count + 2 by omega))
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at h ⊢
  ring_nf at h ⊢
  exact h

/-! ## Summability and bounded cumulative drift -/

/-- The natural-endpoint smooth drift series is summable by comparison with
the shifted `p`-series of exponent `3/2`. -/
theorem summable_suzukiChebyshevSmoothEndpointDrift_nat :
    Summable (fun count : ℕ =>
      suzukiChebyshevSmoothEndpointDrift
        (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ))) := by
  have hbase : Summable
      (fun count : ℕ => (count : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.2 (by norm_num)
  have hshift : Summable
      (fun count : ℕ => (((count + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) := by
    exact (summable_nat_add_iff 2).2 hbase
  exact hshift.of_nonneg_of_le
    (fun count =>
      suzukiChebyshevSmoothEndpointDrift_nat_succ_nonnegative (count + 1))
    suzukiChebyshevSmoothEndpointDrift_nat_le_rpow_neg_three_halves

/-- The cumulative smooth drift converges to the sum of the complete smooth
drift series. -/
theorem tendsto_suzukiChebyshevCumulativeSmoothEndpointDrift :
    Tendsto suzukiChebyshevCumulativeSmoothEndpointDrift atTop
      (𝓝 (∑' count : ℕ,
        suzukiChebyshevSmoothEndpointDrift
          (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ)))) := by
  change Tendsto
    (fun count : ℕ => ∑ index ∈ Finset.range count,
      suzukiChebyshevSmoothEndpointDrift
        (((index + 2 : ℕ) : ℝ)) (((index + 3 : ℕ) : ℝ)))
    atTop
    (𝓝 (∑' count : ℕ,
      suzukiChebyshevSmoothEndpointDrift
        (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ))))
  simpa only using
    summable_suzukiChebyshevSmoothEndpointDrift_nat.hasSum.tendsto_sum_nat

/-- Every cumulative smooth drift is bounded above by the finite complete
drift sum. -/
theorem suzukiChebyshevCumulativeSmoothEndpointDrift_le_tsum
    (count : ℕ) :
    suzukiChebyshevCumulativeSmoothEndpointDrift count ≤
      ∑' index : ℕ,
        suzukiChebyshevSmoothEndpointDrift
          (((index + 2 : ℕ) : ℝ)) (((index + 3 : ℕ) : ℝ)) := by
  unfold suzukiChebyshevCumulativeSmoothEndpointDrift
  exact summable_suzukiChebyshevSmoothEndpointDrift_nat.sum_le_tsum
    (Finset.range count) (fun index _hindex =>
      suzukiChebyshevSmoothEndpointDrift_nat_succ_nonnegative (index + 1))

/-! ## Asymptotic identification of work and logarithmic average -/

/-- Cumulative signed mass-error work minus the logarithmic-average error and
the endpoint logarithm converges to an explicit finite smooth constant. -/
theorem tendsto_cumulativeMassErrorWork_sub_logAverage_sub_log :
    Tendsto
      (fun count : ℕ =>
        suzukiChebyshevCumulativeMassErrorWork count -
          suzukiChebyshevLogAverageError (((count + 2 : ℕ) : ℝ)) -
          Real.log (((count + 2 : ℕ) : ℝ)))
      atTop
      (𝓝 (-Real.log 2 + 4 * (2 : ℝ) ^ (1 / 2 : ℝ) +
        ∑' index : ℕ,
          suzukiChebyshevSmoothEndpointDrift
            (((index + 2 : ℕ) : ℝ)) (((index + 3 : ℕ) : ℝ)))) := by
  have hlimit :=
    tendsto_suzukiChebyshevCumulativeSmoothEndpointDrift.const_add
      (-Real.log 2 + 4 * (2 : ℝ) ^ (1 / 2 : ℝ))
  convert hlimit using 1
  · funext count
    rw [
      suzukiChebyshevCumulativeMassErrorWork_eq_logAverage_add_logOffset_add_drift]
    ring

end

end RiemannGaussian
