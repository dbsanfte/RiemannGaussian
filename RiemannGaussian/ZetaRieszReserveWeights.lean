/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWingReserve

/-!
# Exact mass of the positive wing reserve

Both reciprocal marginals and the endpoint subtraction retain their actual
integer endpoints. Their limits evaluate the entire reserve weight.
-/

namespace RiemannGaussian.ZetaRieszWingReserve
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCentralHarmonicCost ZetaRieszHeadHarmonicAsymptotic
open HarmonicIntervalLimit ZetaRieszLengthAsymptotic

private theorem tendsto_reserve_lower_ratio :
    Tendsto (fun N : ℕ => ((13 * N / 32 : ℕ) : ℝ) / (N + 1))
      atTop (𝓝 (13 / 32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun N : ℕ => ((13 * N / 32 : ℕ) : ℝ) / (N + 1) - 13 / 32)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (2 : ℝ) / (N + 1)) ?_
      (hm.const_div_atTop 2)
    intro N
    have hlo : 13 * (N + 1) ≤ 32 * (13 * N / 32) + 64 := by omega
    have hhi : 32 * (13 * N / 32) ≤ 13 * (N + 1) + 64 := by omega
    have hlor : (13 : ℝ) * (N + 1) ≤ 32 * ((13 * N / 32 : ℕ) : ℝ) + 64 := by
      exact_mod_cast hlo
    have hhir : 32 * ((13 * N / 32 : ℕ) : ℝ) ≤ (13 : ℝ) * (N + 1) + 64 := by
      exact_mod_cast hhi
    have hm0 : (0 : ℝ) < N + 1 := by positivity
    have hb : |((13 * N / 32 : ℕ) : ℝ) - 13 / 32 * (N + 1)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs]
    calc
      _ = |((13 * N / 32 : ℕ) : ℝ) - 13 / 32 * (N + 1)| / (N + 1) := by
        rw [show ((13 * N / 32 : ℕ) : ℝ) / (N + 1) - 13 / 32 =
          (((13 * N / 32 : ℕ) : ℝ) - 13 / 32 * (N + 1)) / (N + 1) by
            field_simp, abs_div, abs_of_pos hm0]
      _ ≤ _ := div_le_div_of_nonneg_right hb hm0.le
  convert! he.add_const (13 / 32 : ℝ) using 1
  · funext N; ring
  · norm_num

private theorem tendsto_reserve_complement_ratio :
    Tendsto (fun N : ℕ => ((N - 13 * N / 32 : ℕ) : ℝ) / (N + 1))
      atTop (𝓝 (19 / 32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hm.const_div_atTop 1)).sub
    tendsto_reserve_lower_ratio
  norm_num only at h
  apply h.congr'
  filter_upwards [] with N
  have he : ((13 * N / 32 : ℕ) : ℝ) + ((N - 13 * N / 32 : ℕ) : ℝ) = N := by
    exact_mod_cast (show 13 * N / 32 + (N - 13 * N / 32) = N by omega)
  have hm0 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

private theorem reciprocal_interval (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc (a + 1) b, (1 : ℝ) / k) =
      (harmonic b : ℝ) - (harmonic a : ℝ) := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 b := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hs : Finset.Icc 1 b \ Finset.Icc 1 a = Finset.Icc (a + 1) b := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hh := Finset.sum_sdiff (f := fun k : ℕ => (1 : ℝ) / k) hsub
  rw [hs] at hh
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simpa only [one_div] using (eq_sub_iff_add_eq.mpr hh)

/-- The first reciprocal marginal of the actual reserve has its exact logarithmic mass. -/
theorem tendsto_reserve_reciprocal :
    Tendsto (fun N : ℕ => ∑ k ∈ reserveOrders N, (1 : ℝ) / k)
      atTop (𝓝 (Real.log (15 / 13))) := by
  have hA : Tendsto (fun N : ℕ => 13 * N / 32) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3 * b)] with N hN
    omega
  have hr : Tendsto (fun N : ℕ => (((15 * N + 64) / 32 : ℕ) : ℝ) /
      ((13 * N / 32 : ℕ) : ℝ)) atTop (𝓝 (15 / 13)) := by
    have h := tendsto_lower_endpoint_ratio.div tendsto_reserve_lower_ratio (by norm_num)
    norm_num only at h
    apply h.congr'
    filter_upwards [] with N
    dsimp only [Pi.div_apply]
    exact div_div_div_cancel_right₀ (by positivity : (N : ℝ) + 1 ≠ 0) _ _
  have h := tendsto_harmonic_difference (fun N => (15 * N + 64) / 32)
    (fun N => 13 * N / 32) tendsto_lower_endpoint_atTop hA (by norm_num) hr
  apply h.congr'
  filter_upwards [] with N
  exact (reciprocal_interval _ _ (by omega)).symm

/-- The reflected reciprocal marginal keeps the other pair of exact endpoints. -/
theorem tendsto_reserve_reflected_reciprocal :
    Tendsto (fun N : ℕ => ∑ k ∈ reserveOrders N, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ))
      atTop (𝓝 (Real.log (19 / 17))) := by
  have hA : Tendsto (fun N : ℕ => N - 13 * N / 32) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3 * b)] with N hN
    omega
  have hr : Tendsto (fun N : ℕ => ((N - 13 * N / 32 : ℕ) : ℝ) /
      (complementaryEndpoint N : ℝ)) atTop (𝓝 (19 / 17)) := by
    have h := tendsto_reserve_complement_ratio.div tendsto_complementaryEndpoint_ratio
      (by norm_num)
    norm_num only at h
    apply h.congr'
    filter_upwards [] with N
    dsimp only [Pi.div_apply]
    exact div_div_div_cancel_right₀ (by positivity : (N : ℝ) + 1 ≠ 0) _ _
  have h := tendsto_harmonic_difference (fun N => N - 13 * N / 32)
    complementaryEndpoint hA tendsto_complementaryEndpoint_atTop (by norm_num) hr
  apply h.congr'
  filter_upwards [eventually_ge_atTop 320] with N hN
  have he : (∑ k ∈ reserveOrders N, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc (complementaryEndpoint N + 1) (N - 13 * N / 32), (1 : ℝ) / k := by
    apply Finset.sum_bij (fun k _ => N + 1 - k)
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [Finset.mem_Icc]
      unfold complementaryEndpoint
      omega
    · intro a ha b hb he
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      omega
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      unfold complementaryEndpoint at hk'
      refine ⟨N + 1 - k, ?_, by omega⟩
      apply Finset.mem_Icc.mpr
      omega
    · intro k _; rfl
  rw [he, reciprocal_interval _ _ (by unfold complementaryEndpoint; omega)]

/-- The pair weight retains both reciprocal legs before subtracting the endpoint. -/
def reservePairWeight (N k : ℕ) : ℝ := 1 / (k : ℝ) + 1 / ((N + 1 - k : ℕ) : ℝ)

/-- The positive scalar weight of the reserve's negative endpoint term. -/
def reserveHeadWeight (u : ℝ) (N k : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N) * (1 / (k : ℝ))

/-- The exact total pair mass includes both unequal logarithmic intervals. -/
theorem tendsto_sum_reservePairWeight :
    Tendsto (fun N => ∑ k ∈ reserveOrders N, reservePairWeight N k) atTop
      (𝓝 (Real.log (15 / 13) + Real.log (19 / 17))) := by
  simpa only [reservePairWeight, Finset.sum_add_distrib] using
    tendsto_reserve_reciprocal.add tendsto_reserve_reflected_reciprocal

/-- The exact endpoint cost keeps the physical length and radius. -/
theorem tendsto_sum_reserveHeadWeight {u : ℝ} (hu : 0 < u) (huq : u ≤ 3 / 5) :
    Tendsto (fun N => ∑ k ∈ reserveOrders N, reserveHeadWeight u N k) atTop
      (𝓝 (Real.log (15 / 13) / (-2 * u * Real.log u))) := by
  have h := (tendsto_head_length_factor hu huq).mul tendsto_reserve_reciprocal
  simpa only [reserveHeadWeight, ← Finset.mul_sum, Nat.cast_add, Nat.cast_one,
    one_div, inv_mul_eq_div] using h

end
end RiemannGaussian.ZetaRieszWingReserve
