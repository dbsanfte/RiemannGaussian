/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Exact harmonic intervals and their logarithmic limits

Evaluate both genuine integer harmonic endpoints before taking the limit; their common Euler constant cancels.
-/

namespace RiemannGaussian.HarmonicIntervalLimit
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- A reversed reciprocal prefix is exactly a difference of genuine
harmonic numbers, including both integer endpoints. -/
theorem reversed_harmonic_prefix (M K : ℕ) (hKM : K < M) :
    (∑ k ∈ Finset.range (K + 1), (1 : ℝ) / ((M - k : ℕ) : ℝ)) =
      (harmonic M : ℝ) - (harmonic (M - K - 1) : ℝ) := by
  induction K with
  | zero =>
      have hM : M = M - 1 + 1 := by omega
      have hh := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ (M - 1))
      push_cast at hh
      rw [← hM] at hh
      have hMc : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hM.symm
      rw [hMc] at hh
      simp only [zero_add, Finset.sum_range_one, Nat.sub_zero]
      simpa only [one_div] using (eq_sub_iff_add_eq.mpr (by linarith [hh]))
  | succ K ih =>
      have hp := ih (by omega)
      have hl : M - K - 1 = (M - (K + 1) - 1) + 1 := by omega
      have hh := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ (M - (K + 1) - 1))
      push_cast at hh
      rw [← hl] at hh
      have hlc : ((M - (K + 1) - 1 : ℕ) : ℝ) + 1 =
          ((M - K - 1 : ℕ) : ℝ) := by exact_mod_cast hl.symm
      rw [hlc] at hh
      rw [Finset.sum_range_succ, hp]
      have he : M - (K + 1) = M - K - 1 := by omega
      simp only [he, one_div] at hh ⊢
      linarith

/-- Every pair of diverging harmonic endpoints with a nonzero limiting
ratio has the corresponding logarithmic difference limit. -/
theorem tendsto_harmonic_difference (A B : ℕ → ℕ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    {r : ℝ} (hr : r ≠ 0)
    (hAB : Tendsto (fun N => (A N : ℝ) / (B N : ℝ)) atTop (nhds r)) :
    Tendsto (fun N => (harmonic (A N) : ℝ) - (harmonic (B N) : ℝ))
      atTop (nhds (Real.log r)) := by
  have hd := (Real.tendsto_harmonic_sub_log.comp hA).sub
    (Real.tendsto_harmonic_sub_log.comp hB)
  have hl := (Real.continuousAt_log hr).tendsto.comp hAB
  have h := hd.add hl
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [hA.eventually_ge_atTop 1, hB.eventually_ge_atTop 1] with N hAN hBN
  have ha : (A N : ℝ) ≠ 0 := by exact_mod_cast (by omega : A N ≠ 0)
  have hb : (B N : ℝ) ≠ 0 := by exact_mod_cast (by omega : B N ≠ 0)
  simp only [Function.comp_def]
  rw [Real.log_div ha hb]
  ring

end
end RiemannGaussian.HarmonicIntervalLimit
