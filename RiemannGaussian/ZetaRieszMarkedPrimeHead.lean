/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhysicalCompletion

/-!
# An exponentially growing prime head in the marked Euler completion

The exact marked arithmetic series can discard every label containing a
prime at most exp(N/110), with a height-uniform source-scale error. The
factorial rectangle, the signed Riesz coefficient and all orders remain
unchanged. This pays an arithmetic boundary; the remaining signed Euler
response is not bounded here.
-/

namespace RiemannGaussian.ZetaRieszMarkedPrimeHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPhysicalCompletion ZetaRieszMarkedCompletion
open ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint

/-- On the existing core, a least prime below the exponential threshold
forces a share exterior. There is no physical or prime-count hypothesis. -/
theorem small_least_exterior {N n : ℕ} (hn : validLabel n)
    (hwindow : (39/20 : ℝ)*N < Real.log n)
    (hsmall : Real.log n.minFac ≤ (N : ℝ)/110) :
    ¬ZetaRieszLeastBoundary.interior n := by
  intro hi
  have hlog : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast validLabel_one_lt hn)
  have hleast := (lt_div_iff₀ hlog).mp hi.2.1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- The literal contribution of labels containing a prime below the
exponential threshold, keeping the full complex arithmetic atom. -/
def headAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  if Real.log n.minFac ≤ (N : ℝ)/110 then atom u y N n else 0

/-- The logarithmic test is exactly the presence of an actual prime
factor at most exp(N/110), not a condition on an auxiliary cofactor. -/
theorem head_condition_iff {n : ℕ} (hn : validLabel n) (N : ℕ) :
    Real.log n.minFac ≤ (N : ℝ)/110 ↔
      ∃ p ∈ n.primeFactors, (p : ℝ) ≤ Real.exp ((N : ℝ)/110) := by
  have hn1 := validLabel_one_lt hn
  have hmin := Nat.minFac_prime hn1.ne'
  constructor
  · intro h
    refine ⟨n.minFac, Nat.mem_primeFactors.mpr ⟨hmin,Nat.minFac_dvd n,hn.1.ne_zero⟩,?_⟩
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hmin.pos)).mp h
  · rintro ⟨p,hp,hs⟩
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hminp := Nat.minFac_le_of_dvd hprime.two_le (Nat.dvd_of_mem_primeFactors hp)
    have hlog := Real.log_le_log (by exact_mod_cast hmin.pos : (0 : ℝ) < n.minFac)
      (by exact_mod_cast hminp : (n.minFac : ℝ) ≤ p)
    exact hlog.trans ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mpr hs)

theorem summable_headAtom (u y : ℝ) (N : ℕ) (hN : 21 ≤ N) :
    Summable (headAtom u y N) := by
  apply (summable_atom u y N hN).norm.of_norm_bounded
  intro n
  by_cases hn : Real.log n.minFac ≤ (N : ℝ)/110
  · simp only [headAtom,if_pos hn,le_refl]
  · simp only [headAtom,if_neg hn,norm_zero]
    exact norm_nonneg _

/-- One common radial-plus-share allowance pays every finite partial
sum of labels containing a small prime, uniformly in the height. -/
theorem exists_finite_head_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, 21 ≤ N → ∀ u : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ∀ y : ℝ, ∀ S : Finset ℕ,
        ‖(u : ℂ)^(N+1)*∑ n ∈ S, headAtom u y N n‖ ≤
          r^N*C+shareBudget N := by
  obtain ⟨r,C,hr0,hr1,hC,hb⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (by norm_num [radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    ZetaRieszParityPacket.core_window_costs.1 ZetaRieszParityPacket.core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N hN u hu hU y S
  let T := S.filter (fun n => validLabel n ∧ Real.log n.minFac ≤ (N : ℝ)/110)
  have heq : (∑ n ∈ S, headAtom u y N n) = ∑ n ∈ T, atom u y N n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hs : Real.log n.minFac ≤ (N : ℝ)/110
    · by_cases hv : validLabel n
      · simp only [headAtom,if_pos hs,if_pos (show validLabel n ∧
          Real.log n.minFac ≤ (N : ℝ)/110 from ⟨hv,hs⟩)]
      · simp only [headAtom,if_pos hs,hv,false_and,if_false,atom,markedCoefficient,
          zero_mul]
    · simp only [headAtom,hs,and_false,if_false]
  let D := LogarithmicDeviation.deviationBand T (39/20) (203/100) N
  have hrad : ‖(u : ℂ)^(N+1)*
      ((∑ n ∈ T, atom u y N n)-∑ n ∈ D, atom u y N n)‖ ≤ r^N*C := by
    simpa only [atom,SquarefreeEulerQuadratic.primeFilterKernel_one,zetaPrimeLogKernel] using
      hb N T (markedCoefficient u N) (fun n _ => markedCoefficient_norm_le u N hN n) y u hu hU
  have hshare : ‖(u : ℂ)^(N+1)*∑ n ∈ D, atom u y N n‖ ≤ shareBudget N := by
    apply exterior_sum_bound hu hU y N (by omega) D
    intro n hn
    obtain ⟨hT,hw⟩ := Finset.mem_filter.mp hn
    obtain ⟨_hS,hv,hm⟩ := Finset.mem_filter.mp hT
    exact ⟨hv,small_least_exterior hv hw.1 hm⟩
  rw [heq]
  have he : (u : ℂ)^(N+1)*∑ n ∈ T, atom u y N n =
      (u : ℂ)^(N+1)*((∑ n ∈ T, atom u y N n)-∑ n ∈ D, atom u y N n)+
        (u : ℂ)^(N+1)*∑ n ∈ D, atom u y N n := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hrad hshare)

/-- The genuinely convergent small-prime series obeys the same
source-scale bound, with no zero hypothesis or varying-count allowance. -/
theorem exists_head_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, 21 ≤ N → ∀ u : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ∀ y : ℝ, ‖(u : ℂ)^(N+1)*(∑' n, headAtom u y N n)‖ ≤
        r^N*C+shareBudget N := by
  obtain ⟨r,C,hr0,hr1,hC,hb⟩ := exists_finite_head_bound
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N hN u hu hU y
  apply le_of_tendsto ((summable_headAtom u y N hN).hasSum.mul_left
    ((u : ℂ)^(N+1))).norm
  apply Eventually.of_forall
  intro S
  simpa only [Finset.mul_sum] using hb N hN u hu hU y S

/-- Removing every small-prime label is independently negligible,
even for moving heights and the exact original factorial weights. -/
theorem tendsto_head {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(∑' n, headAtom u (heights N) N n))
      atTop (nhds 0) := by
  obtain ⟨r,C,hr0,hr1,_hC,hb⟩ := exists_head_bound
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).add tendsto_shareBudget
  simp only [zero_mul,zero_add] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 21] with N hN
  exact hb N hN u hu hU (heights N)

/-- Quantitative rate test for the next Euler correction estimate. The
prime-square tail at the new threshold beats the safe-axis Cauchy cost.
This is only the scalar rate inequality, not the still-open inequality
transporting that tail through the marked Euler operator. -/
theorem quadratic_rate_lt :
    radiusCeiling/(3/2-(1+1/262144 : ℝ))*
      Real.exp (-(2*(1+1/262144 : ℝ)-1)/110) < 124/125 := by
  let x : ℝ := (2*(1+1/262144 : ℝ)-1)/110
  have he : -(2*(1+1/262144 : ℝ)-1)/110 = -x := by dsimp [x]; ring
  rw [he,Real.exp_neg,← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos x)).mpr
  calc
    _ < (124/125 : ℝ)*(x+1) := by norm_num [x,radiusCeiling]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp x) (by norm_num)

end
end RiemannGaussian.ZetaRieszMarkedPrimeHead
