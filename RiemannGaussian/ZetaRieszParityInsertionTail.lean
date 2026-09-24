/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityInsertionIdentity

/-!
# All supported insertion orders twelve and above

The estimate is uniform in the retained positive auxiliary lower cutoff.
It concerns the entire signed supported-kernel tail, not a truncation of
the count sum and not the empty-cofactor boundary source.
-/

namespace RiemannGaussian.ZetaRieszParityInsertionPoisson
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszParityFirstInsertion
set_option backward.isDefEq.respectTransparency false

theorem restricted_firstDensity {a : ℝ} (ha : 0 < a) :
    IntegrableOn firstDensity (Ioc a cutoff) ∧
      (∫ x in Ioc a cutoff, firstDensity x) ≤ Real.log (28/9) := by
  have hsub : Ioc a cutoff ⊆ Ioc (0 : ℝ) (7/250) := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2⟩
  have hfi : IntegrableOn firstDensity (Ioc (0 : ℝ) (7/250)) := integrable_firstDensity
  refine ⟨hfi.mono_set hsub, ?_⟩
  rw [← integral_firstDensity]
  apply setIntegral_mono_set hfi
    (Filter.Eventually.of_forall firstDensity_nonneg)
  exact Filter.Eventually.of_forall hsub

/-- Near the maximal eleven-jump sum, every coordinate is forced away
from zero. This bound keeps the genuine nested density integrals. -/
theorem jumpCount_near_endpoint {a : ℝ} (ha : 0 < a) (k : ℕ) {g : ℝ}
    (hg : (k : ℝ)*cutoff-(cutoff-9/1000) < g) :
    jumpCount a k g ≤ Real.log (28/9)^k := by
  induction k generalizing g with
  | zero => simpa using ((jumpCount_properties ha 0).1 g).2
  | succ k ih =>
    have hlog : 0 ≤ Real.log (28/9 : ℝ) := Real.log_nonneg (by norm_num)
    have hden := restricted_firstDensity ha
    have hb : ∀ x ∈ Ioc a cutoff,
        x⁻¹*jumpCount a k (g-x) ≤ firstDensity x*Real.log (28/9)^k := by
      intro x hx
      by_cases hsmall : x ≤ 9/1000
      · rw [jumpCount_eq_zero ha k (by push_cast at hg; linarith), mul_zero]
        exact mul_nonneg (firstDensity_nonneg _) (pow_nonneg hlog _)
      · have hh := ih (g := g-x) (by push_cast at hg; linarith [hx.2])
        have hxden : firstDensity x = x⁻¹ := by
          unfold firstDensity
          rw [indicator_of_mem (show x ∈ Ioc (9/1000 : ℝ) (7/250) from
            ⟨lt_of_not_ge hsmall, hx.2⟩)]
        rw [hxden]
        exact mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (ha.trans hx.1).le)
    calc
      _ ≤ ∫ x in Ioc a cutoff, firstDensity x*Real.log (28/9)^k := by
        apply integral_mono_ae (integrable_jumpCount ha k g) (hden.1.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hb x hx
      _ = (∫ x in Ioc a cutoff, firstDensity x)*Real.log (28/9)^k := integral_mul_const _ _
      _ ≤ Real.log (28/9)*Real.log (28/9)^k :=
        mul_le_mul_of_nonneg_right hden.2 (pow_nonneg hlog _)
      _ = _ := by rw [pow_succ]; ring

theorem eleven_insertion_bounds {a g : ℝ} (ha : 0 < a) (hg : (289/1000 : ℝ) < g) :
    0 ≤ insertion a 11 g ∧ insertion a 11 g < 1/1000000 := by
  rw [eleven_insertion_eq ha hg]
  have hb := jumpCount_near_endpoint ha 11 (g := g) (by norm_num [cutoff]; exact hg)
  have hlo : 0 ≤ Real.log (28/9 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog : Real.log (28/9 : ℝ) ≤ 6/5 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6/5) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hp := pow_le_pow_left₀ hlo hlog 11
  constructor
  · exact div_nonneg ((jumpCount_properties ha 11).1 g).1 (by positivity)
  · apply (div_le_div_of_nonneg_right (hb.trans hp) (by positivity : (0 : ℝ) ≤ (11 : ℕ).factorial)).trans_lt
    norm_num [Nat.factorial]

/-- Every supported insertion from order twelve onward, with signs retained. -/
def higherInsertionTail (a g : ℝ) : ℝ := ∑' k : ℕ, insertion a (k+12) g

/-- Exact subtraction of the first supported level. The series includes
every insertion order from twelve through infinity. -/
theorem higherInsertionTail_eq {a g : ℝ} (ha : 0 < a) (hg : (289/1000 : ℝ) < g) :
    higherInsertionTail a g = supportInsertionSum a g-insertion a 11 g := by
  have hz : ∑ k ∈ Finset.range 11, insertion a k g = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k ≤ 10 := by simp only [Finset.mem_range] at hk; omega
    have hkR : (k : ℝ) ≤ 10 := by exact_mod_cast hk0
    apply insertion_eq_zero ha k
    norm_num [cutoff]
    linarith
  have h := (hasSum_nat_add_iff' 12).mpr (summable_insertion ha g).hasSum
  rw [show (12 : ℕ) = 11+1 by norm_num, Finset.sum_range_succ, hz, zero_add] at h
  exact h.tsum_eq

/-- The entire signed 12+ support tail is below one millionth, uniformly
as the auxiliary lower cutoff approaches zero. No termwise norm sum occurs. -/
theorem higherInsertionTail_bound {a g : ℝ} (ha : 0 < a) (har : a ≤ cutoff)
    (hg : (289/1000 : ℝ) < g) : ‖higherInsertionTail a g‖ < 1/1000000 := by
  rw [higherInsertionTail_eq ha hg, Real.norm_eq_abs, abs_lt]
  have ht := supportInsertionSum_core_bound ha har hg
  have hfirst := eleven_insertion_bounds ha hg
  constructor <;> linarith

/-- Direct instantiation at the literal moving length and core window. -/
theorem higherInsertionTail_core {a u : ℝ} (ha : 0 < a) (har : a ≤ cutoff)
    (hu : 1/2 ≤ u) {N K n : ℕ} (hN : 2 ≤ N)
    (hn : n ∈ ZetaRieszParityPacket.coreBand u N K) :
    ‖higherInsertionTail a (1-SquarefreeVaughanLogSource.length u N/Real.log n)‖ < 1/1000000 :=
  higherInsertionTail_bound ha har (core_support_gap_sharp hu hN hn)

/-- The same bound stated directly for the actual repeated two-shift
support kernel at the core coordinates, with all factorials retained. -/
theorem nested_tail_core_bound {a u : ℝ} (ha : 0 < a) (har : a ≤ cutoff)
    (hu : 1/2 ≤ u) {N K n : ℕ} (hN : 2 ≤ N)
    (hn : n ∈ ZetaRieszParityPacket.coreBand u N K) (p : ℝ) :
    ‖∑' k : ℕ, nestedSupport a (k+12) (1-p)
      (SquarefreeVaughanLogSource.length u N/Real.log n-p)/((k+12).factorial : ℝ)‖ < 1/1000000 := by
  have he (k : ℕ) : nestedSupport a (k+12) (1-p)
      (SquarefreeVaughanLogSource.length u N/Real.log n-p)/((k+12).factorial : ℝ) =
        insertion a (k+12) (1-SquarefreeVaughanLogSource.length u N/Real.log n) := by
    rw [← insertion_eq_nestedSupport ha]
    congr 1
    ring
  simp_rw [he]
  exact higherInsertionTail_core ha har hu hN hn

end
end RiemannGaussian.ZetaRieszParityInsertionPoisson
