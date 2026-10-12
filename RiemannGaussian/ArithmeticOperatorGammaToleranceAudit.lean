/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFiniteGammaControl

/-!
# Arbitrarily small uniform Gamma tolerance still permits a coherent tail

The deleted unit-prime Mangoldt measure has finite inverse-weighted mass.
Restoring a sufficiently large finite prime head therefore makes its
literal Gamma deficit at MOST epsilon*X at EVERY integer cutoff X, while
preserving the coherent full source -2 and exact finite calibration.

This does not contradict the positive-cone rigidity theorem: a fixed
control still has a positive LINEAR deficit, not o(X). The selected head
depends on epsilon. The result closes finite/exact-head plus fixed-small-
relative-Gamma-error inference, not use of the complete exact Gamma data.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaToleranceAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ArithmeticOperatorBinaryDensityAudit
open ArithmeticOperatorGammaConeStability

/-- Every deleted proper power is retained in this inverse mass. -/
def inverseLoss (u y : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n-control u y n)/(n : ℝ)

theorem inverseLoss_nonneg (u y : ℝ) (n : ℕ) : 0 ≤ inverseLoss u y n :=
  div_nonneg (sub_nonneg.mpr (control_bounds u y n).2) (Nat.cast_nonneg n)

/-- The dyadic density bound is summable, not merely o(1). -/
theorem summable_densityBudget {u : ℝ} (hu : 1/2<u) :
    Summable (densityBudget u) := by
  have hh : Summable (fun J : ℕ => (J : ℝ)*(1/2 : ℝ)^J) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2) (by norm_num)
  have hr : Summable (fun J : ℕ => (J : ℝ)*densityRate u^J) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := densityRate u) (by
          rw [Real.norm_of_nonneg (densityRate_bounds hu).1.le]
          exact (densityRate_bounds hu).2)
  have ht := ((hh.mul_left (4*Real.log 2)).add
    (summable_geometric_two.mul_left 18)).add (hr.mul_left (32*Real.log 2))
  apply ht.congr
  intro J
  unfold densityBudget
  ring

private theorem four_pow (J : ℕ) : (4 : ℕ)^J=2^(2*J) := by
  rw [pow_mul]
  norm_num

/-- Group integer labels by their ACTUAL dyadic shell, retaining every
proper-power label and both shell endpoints. -/
theorem inverseLoss_shell_le {u : ℝ} (hu : 1/2<u) (y : ℝ) (M J : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n => Nat.log 4 n=J),inverseLoss u y n)≤
      4*densityBudget u (J+1) := by
  let S := (Finset.range M).filter (fun n => Nat.log 4 n=J)
  have hsum : (∑ n ∈ S,inverseLoss u y n)≤
      loss u y (4^(J+1))/(4 : ℝ)^J := by
    calc
      _ ≤ ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n-control u y n)/(4 : ℝ)^J := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n=0
        · simp only [hn0,inverseLoss,Nat.cast_zero,div_zero]
          exact div_nonneg (sub_nonneg.mpr (control_bounds u y 0).2) (by positivity)
        · have hj := (Finset.mem_filter.mp hn).2
          have hpow : (4 : ℝ)^J≤(n : ℝ) := by
            exact_mod_cast (hj ▸ Nat.pow_log_le_self 4 hn0)
          exact div_le_div_of_nonneg_left (sub_nonneg.mpr (control_bounds u y n).2)
            (by positivity) hpow
      _ = (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n-control u y n))/(4 : ℝ)^J :=
        (Finset.sum_div _ _ _).symm
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hj := (Finset.mem_filter.mp hn).2
          have hh := Nat.lt_pow_succ_log_self (by norm_num : 1<(4 : ℕ)) n
          rw [hj] at hh
          exact Finset.mem_range.mpr (by omega)
        · intro n _ _
          exact sub_nonneg.mpr (control_bounds u y n).2
  apply hsum.trans
  have hh := mul_le_mul_of_nonneg_left (loss_div_dyadic_le hu y (J+1))
    (by norm_num : (0 : ℝ)≤4)
  have hp : (2 : ℝ)^(2*(J+1))=(4 : ℝ)^(J+1) := by
    rw [pow_mul]
    norm_num
  rw [←four_pow,hp] at hh
  convert hh using 1
  simp only [pow_succ]
  field_simp

/-- The complete inverse-weighted deletion is summable. This is stronger
than PNT-scale density agreement, but still leaves its factorial source. -/
theorem summable_inverseLoss {u : ℝ} (hu : 1/2<u) (y : ℝ) :
    Summable (inverseLoss u y) := by
  have hs : Summable (fun J : ℕ => 4*densityBudget u (J+1)) :=
    ((summable_nat_add_iff 1).mpr (summable_densityBudget hu)).mul_left 4
  apply summable_of_sum_range_le (inverseLoss_nonneg u y)
    (c := ∑' J : ℕ,4*densityBudget u (J+1))
  intro M
  have hm : ∀ n ∈ Finset.range M, Nat.log 4 n ∈ Finset.range M := by
    intro n hn
    exact Finset.mem_range.mpr ((Nat.log_le_self 4 n).trans_lt (Finset.mem_range.mp hn))
  rw [←Finset.sum_fiberwise_of_maps_to hm]
  apply (Finset.sum_le_sum (fun J _ => inverseLoss_shell_le hu y M J)).trans
  exact hs.sum_le_tsum _ (fun J _ => by
    unfold densityBudget densityRate
    positivity)

/-- A genuine tail mass, not a local error normalized by the full carrier. -/
def tailMass (u y : ℝ) (B : ℕ) : ℝ :=
  (∑' n : ℕ,inverseLoss u y n)-∑ n ∈ Finset.range (B+1),inverseLoss u y n

theorem tailMass_nonneg {u : ℝ} (hu : 1/2<u) (y : ℝ) (B : ℕ) :
    0≤tailMass u y B := by
  apply sub_nonneg.mpr
  exact (summable_inverseLoss hu y).sum_le_tsum _ (fun n _ => inverseLoss_nonneg u y n)

theorem tendsto_tailMass {u : ℝ} (hu : 1/2<u) (y : ℝ) :
    Tendsto (tailMass u y) atTop (𝓝 0) := by
  have ht := (summable_inverseLoss hu y).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hx : Tendsto (fun B : ℕ => (∑' n : ℕ,inverseLoss u y n)-
      ∑ n ∈ Finset.range (B+1),inverseLoss u y n) atTop
      (𝓝 ((∑' n : ℕ,inverseLoss u y n)-(∑' n : ℕ,inverseLoss u y n))) :=
    tendsto_const_nhds.sub ht
  change Tendsto (fun B : ℕ => tailMass u y B) atTop (𝓝 0)
  simpa only [tailMass,sub_self] using hx

/-- Exact floors give a uniform ALL-cutoff Gamma error, with no source
envelope and no termwise loss of a complex phase correlation. -/
theorem deficit_le_cutoff_mul_tail {u : ℝ} (hu : 1/2<u) (y : ℝ) (B X : ℕ) :
    deficit (ArithmeticOperatorFiniteGammaControl.control B u y) X≤
      (X : ℝ)*tailMass u y B := by
  let w := ArithmeticOperatorFiniteGammaControl.control B u y
  have hs := summable_inverseLoss hu y
  let S := (Finset.Icc 1 X).filter (fun n => B<n)
  have hp : (∑ n ∈ S,inverseLoss u y n)≤tailMass u y B := by
    have hdis : Disjoint S (Finset.range (B+1)) := by
      apply Finset.disjoint_left.mpr
      intro n hn hb
      have := (Finset.mem_filter.mp hn).2
      have := Finset.mem_range.mp hb
      omega
    have ht := hs.sum_le_tsum (S ∪ Finset.range (B+1))
      (fun n _ => inverseLoss_nonneg u y n)
    rw [Finset.sum_union hdis] at ht
    exact (le_sub_iff_add_le).mpr ht
  rw [deficit_eq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        if B<n then (X : ℝ)*inverseLoss u y n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hBn : B<n
      · rw [ite_eq_left hBn]
        have hnew := (ArithmeticOperatorFiniteGammaControl.control_bounds B u y n).2
        have hold := ArithmeticOperatorFiniteGammaControl.old_control_le B u y n
        apply (mul_le_mul_of_nonneg_right (Nat.cast_div_le :
          ((X/n : ℕ) : ℝ)≤(X : ℝ)/(n : ℝ)) (sub_nonneg.mpr hnew)).trans
        apply (mul_le_mul_of_nonneg_left (sub_le_sub_left hold _)
          (by positivity : (0 : ℝ)≤(X : ℝ)/(n : ℝ))).trans_eq
        unfold inverseLoss
        ring
      · rw [ite_eq_right hBn,ArithmeticOperatorFiniteGammaControl.control_eq_mangoldt_of_le
          B u y (by omega),sub_self,mul_zero]
    _ = (X : ℝ)*(∑ n ∈ S,inverseLoss u y n) := by
      simp only [S,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg X)

/-- Each fixed repaired control still has a positive linear Gamma cost.
Its constant can be arbitrarily small; it is never a sublinear deficit. -/
theorem repaired_control_linear_deficit (B : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      c≤deficit (ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54) X/(X : ℝ) := by
  obtain ⟨p,hp,hpB,hd⟩ := ArithmeticOperatorFiniteGammaControl.exists_deleted_prime_gt B
    (u := 10001/20000) (by norm_num) (by norm_num) (y := 54) (by norm_num)
  let w := ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54
  have hw : ∀ n, w n≤ArithmeticFunction.vonMangoldt n :=
    fun n => (ArithmeticOperatorFiniteGammaControl.control_bounds B _ _ n).2
  have hz : w p=0 := by
    simp only [w,ArithmeticOperatorFiniteGammaControl.control,
      ArithmeticOperatorPrimeTowerControl.towerCoefficient,hp.minFac_eq,
      ArithmeticOperatorFiniteGammaControl.base,ite_eq_right (by omega : ¬p≤B),
      ArithmeticOperatorBinaryPrimeControl.retainedBase,hd,sub_self,zero_mul]
  have hlog : 0<Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  refine ⟨Real.log p/(2*(p : ℝ)),div_pos hlog (by positivity),?_⟩
  filter_upwards [eventually_ge_atTop (2*p)] with X hX
  simpa only [hz,sub_zero,ArithmeticFunction.vonMangoldt_apply_prime hp] using
    normalized_atom_le_deficit hw hp.pos hX

/-- The small-tolerance construction cannot be used as a counterexample
to the already-checked cofinal o(X) positive-cone rigidity theorem. -/
theorem repaired_control_not_cofinal_sublinear_deficit (B : ℕ) {X : ℕ → ℕ}
    (hX : Tendsto X atTop atTop) :
    ¬Tendsto (fun j : ℕ => deficit
      (ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54)
      (X j)/(X j : ℝ)) atTop (𝓝 0) := by
  intro ht
  obtain ⟨c,hc,he⟩ := repaired_control_linear_deficit B
  obtain ⟨j,hlo,hhi⟩ := ((ht.eventually_lt_const hc).and (hX.eventually he)).exists
  exact (not_lt_of_ge hhi) hlo

/-- Every fixed positive tolerance, even at ALL cutoffs, coexists with
exact finite calibration and the full coherent source -2. This is NOT
one control with o(X) deficit and NOT actual-prime non-coherence. -/
theorem exists_uniform_tolerance_control (head : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℕ, head≤B ∧
      (∀ n≤head, ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54 n=
        ArithmeticFunction.vonMangoldt n) ∧
      (∀ X : ℕ, 0≤deficit (ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54) X ∧
        deficit (ArithmeticOperatorFiniteGammaControl.control B (10001/20000) 54) X≤ε*X) ∧
      Tendsto (ArithmeticOperatorPrimeTowerControl.fullMoment
        (ArithmeticOperatorFiniteGammaControl.base B (10001/20000) 54)
        (10001/20000) 54) atTop (𝓝 (-2)) := by
  obtain ⟨B,hB,hsmall⟩ := ((eventually_ge_atTop head).and
    ((tendsto_tailMass (by norm_num : (1/2 : ℝ)<10001/20000) 54).eventually_lt_const hε)).exists
  refine ⟨B,hB,?_,?_,ArithmeticOperatorFiniteGammaControl.full_source B⟩
  · intro n hn
    exact ArithmeticOperatorFiniteGammaControl.control_eq_mangoldt_of_le B _ _ (hn.trans hB)
  · intro X
    constructor
    · rw [deficit_eq]
      apply Finset.sum_nonneg
      intro n _
      exact mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (ArithmeticOperatorFiniteGammaControl.control_bounds B _ _ n).2)
    · exact (deficit_le_cutoff_mul_tail (by norm_num) 54 B X).trans
        ((mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg X)).trans_eq (by ring))

end
end RiemannGaussian.ArithmeticOperatorGammaToleranceAudit
