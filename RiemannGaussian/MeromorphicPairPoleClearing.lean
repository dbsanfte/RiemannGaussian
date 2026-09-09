/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusWronskianArithmetic
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# A common finite pole-clearing weight

The negative parts of two actual divisors determine a finite common
weight on a compact set. The selected point is excluded from this
weight, so its leading coefficient remains visible. Multiplying also by
the selected quadratic factor gives genuine analytic representatives
when both selected poles have order at most two.
-/

open Complex Filter Function MeromorphicOn Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The exact common pole multiplicity, excluding the selected point.
Nonnegative divisor orders require no cancellation. -/
def meromorphicPairClearingExponent (f g : ℂ → ℂ) (K : Set ℂ) (a z : ℂ) : ℤ :=
  if z = a then 0 else max 0 (max (-divisor f K z) (-divisor g K z))

/-- The common weight keeps every divisor location and multiplicity.
Its finite support is proved on compact sets below. -/
def meromorphicPairClearingWeight (f g : ℂ → ℂ) (K : Set ℂ) (a : ℂ) : ℂ → ℂ :=
  ∏ᶠ z, (fun s ↦ s - z) ^ meromorphicPairClearingExponent f g K a z

/-- Compactness makes the common pole-clearing product finite. -/
theorem hasFiniteSupport_meromorphicPairClearingExponent (f g : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (a : ℂ) :
    (meromorphicPairClearingExponent f g K a).HasFiniteSupport := by
  apply ((divisor f K).finiteSupport hK |>.union ((divisor g K).finiteSupport hK)).subset
  intro z hz
  by_contra hn
  have hf : divisor f K z = 0 := by simpa using (not_or.mp hn).1
  have hg : divisor g K z = 0 := by simpa using (not_or.mp hn).2
  simp [Function.mem_support, meromorphicPairClearingExponent, hf, hg] at hz

/-- The clearing weight is entire: every exponent is nonnegative. -/
theorem analyticAt_meromorphicPairClearingWeight (f g : ℂ → ℂ) (K : Set ℂ) (a s : ℂ) :
    AnalyticAt ℂ (meromorphicPairClearingWeight f g K a) s := by
  apply Function.FactorizedRational.analyticAt
  simp only [meromorphicPairClearingExponent]
  split_ifs <;> simp

/-- Excluding the selected point makes its weight nonzero. -/
theorem meromorphicPairClearingWeight_ne_zero (f g : ℂ → ℂ) (K : Set ℂ) (a : ℂ) :
    meromorphicPairClearingWeight f g K a a ≠ 0 :=
  Function.FactorizedRational.ne_zero (by simp [meromorphicPairClearingExponent])

/-- The finite weight has exactly the prescribed order at every point. -/
theorem meromorphicOrderAt_meromorphicPairClearingWeight (f g : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (a s : ℂ) :
    meromorphicOrderAt (meromorphicPairClearingWeight f g K a) s =
      meromorphicPairClearingExponent f g K a s :=
  Function.FactorizedRational.meromorphicOrderAt_eq _
    (hasFiniteSupport_meromorphicPairClearingExponent f g hK a)

/-- Both responses use exactly the same finite weight. -/
theorem meromorphicPairClearingWeight_comm (f g : ℂ → ℂ) (K : Set ℂ) (a : ℂ) :
    meromorphicPairClearingWeight f g K a = meromorphicPairClearingWeight g f K a := by
  simp only [meromorphicPairClearingWeight, meromorphicPairClearingExponent,
    max_comm (-divisor f K _) (-divisor g K _)]

/-- The common weight removes every nonselected pole of the first
response. No missing cancellation is assumed as a premise. -/
theorem meromorphicOrderAt_pairCleared_nonneg {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a s : ℂ} (hs : s ∈ K) (ha : s ≠ a) :
    0 ≤ meromorphicOrderAt (meromorphicPairClearingWeight f g K a * f) s := by
  rw [meromorphicOrderAt_mul (analyticAt_meromorphicPairClearingWeight f g K a s).meromorphicAt
      (hf s hs), meromorphicOrderAt_meromorphicPairClearingWeight f g hK]
  by_cases ht : meromorphicOrderAt f s = ⊤
  · simp [ht]
  lift meromorphicOrderAt f s to ℤ using ht with n hn
  have hd : divisor f K s = n := by
    rw [hf.divisor_apply hs, ← hn]
    rfl
  simp only [meromorphicPairClearingExponent, if_neg ha, hd]
  change ((0 : ℤ) : WithTop ℤ) ≤
    ((max 0 (max (-n) (-divisor g K s)) : ℤ) : WithTop ℤ) + (n : WithTop ℤ)
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have h₁ := le_max_right (0 : ℤ) (max (-n) (-divisor g K s))
  have h₂ := le_max_left (-n) (-divisor g K s)
  omega

/-- The selected quadratic factor and common weight remove all poles
when the selected pole has order at most two. -/
theorem meromorphicOrderAt_pairQuadraticCleared_nonneg {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ}
    (ha : (-2 : WithTop ℤ) ≤ meromorphicOrderAt f a) {s : ℂ} (hs : s ∈ K) :
    0 ≤ meromorphicOrderAt ((fun z : ℂ ↦ z - a) ^ (2 : ℕ) *
      (meromorphicPairClearingWeight f g K a * f)) s := by
  have hw := (analyticAt_meromorphicPairClearingWeight f g K a s).meromorphicAt
  rw [meromorphicOrderAt_mul (by fun_prop) (hw.mul (hf s hs))]
  by_cases hsa : s = a
  · subst s
    rw [meromorphicOrderAt_pow (by fun_prop), meromorphicOrderAt_id_sub_const,
      meromorphicOrderAt_mul hw (hf a hs),
      meromorphicOrderAt_meromorphicPairClearingWeight f g hK,
      meromorphicPairClearingExponent, if_pos rfl, WithTop.coe_zero, zero_add, mul_one]
    by_cases ht : meromorphicOrderAt f a = ⊤
    · simp [ht]
    lift meromorphicOrderAt f a to ℤ using ht with n hn
    change ((-2 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) at ha
    change ((0 : ℤ) : WithTop ℤ) ≤ ((2 : ℤ) : WithTop ℤ) + (n : WithTop ℤ)
    rw [WithTop.coe_le_coe] at ha
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    omega
  · exact add_nonneg (AnalyticAt.meromorphicOrderAt_nonneg (by fun_prop))
      (meromorphicOrderAt_pairCleared_nonneg hK hf hs hsa)

/-- The actual analytic representative after all quadratic poles have
been cleared. Values at removable points are explicitly filled. -/
def meromorphicPairQuadraticRegular (f g : ℂ → ℂ) (K : Set ℂ) (a : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn ((fun z : ℂ ↦ z - a) ^ (2 : ℕ) *
    (meromorphicPairClearingWeight f g K a * f)) K

/-- The complete cleared response is analytic on a neighborhood of
every point of the compact domain, including its former poles. -/
theorem analyticOnNhd_meromorphicPairQuadraticRegular {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ}
    (ha : (-2 : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    AnalyticOnNhd ℂ (meromorphicPairQuadraticRegular f g K a) K := by
  have hm : MeromorphicOn ((fun z : ℂ ↦ z - a) ^ (2 : ℕ) *
      (meromorphicPairClearingWeight f g K a * f)) K := by
    intro s hs
    exact (AnalyticAt.meromorphicAt (by fun_prop)).mul
      ((analyticAt_meromorphicPairClearingWeight f g K a s).meromorphicAt.mul (hf s hs))
  intro s hs
  apply ((meromorphicNFOn_toMeromorphicNFOn _ K hs).meromorphicOrderAt_nonneg_iff_analyticAt).mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm hs]
  exact meromorphicOrderAt_pairQuadraticCleared_nonneg hK hf ha hs

/-- The analytic representative keeps the original response throughout
each punctured germ, which is the interface for Cauchy estimates. -/
theorem meromorphicPairQuadraticRegular_eventuallyEq {f g : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) {a s : ℂ} (hs : s ∈ K) :
    meromorphicPairQuadraticRegular f g K a =ᶠ[𝓝[≠] s]
      (fun z : ℂ ↦ z - a) ^ (2 : ℕ) * (meromorphicPairClearingWeight f g K a * f) := by
  apply MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE _ hs
  intro z hz
  exact (AnalyticAt.meromorphicAt (by fun_prop)).mul
    ((analyticAt_meromorphicPairClearingWeight f g K a z).meromorphicAt.mul (hf z hz))

private theorem order_regular_selected {f g : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K) :
    meromorphicOrderAt (meromorphicPairQuadraticRegular f g K a) a =
      2 + meromorphicOrderAt f a := by
  rw [meromorphicOrderAt_congr (meromorphicPairQuadraticRegular_eventuallyEq hf ha),
    meromorphicOrderAt_mul (by fun_prop)
      ((analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.mul (hf a ha)),
    meromorphicOrderAt_pow (by fun_prop), meromorphicOrderAt_id_sub_const,
    meromorphicOrderAt_mul (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt (hf a ha),
    meromorphicOrderAt_meromorphicPairClearingWeight f g hK, meromorphicPairClearingExponent,
    if_pos rfl, WithTop.coe_zero, zero_add, mul_one]
  norm_num

/-- A selected double pole becomes a nonzero analytic value after
clearing, so the common weight cannot erase its source. -/
theorem meromorphicPairQuadraticRegular_ne_zero {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K)
    (ho : meromorphicOrderAt f a = -2) : meromorphicPairQuadraticRegular f g K a a ≠ 0 := by
  apply (meromorphicNFOn_toMeromorphicNFOn _ K ha).meromorphicOrderAt_eq_zero_iff.mp
  change meromorphicOrderAt (meromorphicPairQuadraticRegular f g K a) a = 0
  rw [order_regular_selected hK hf ha, ho]
  change ((2 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add]
  rfl

/-- The filled value retains the selected pole's exact leading
coefficient multiplied by the explicit nonzero common weight. -/
theorem meromorphicPairQuadraticRegular_apply {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K)
    (ho : meromorphicOrderAt f a = -2) :
    meromorphicPairQuadraticRegular f g K a a =
      meromorphicPairClearingWeight f g K a a * meromorphicTrailingCoeffAt f a := by
  have hreg := analyticOnNhd_meromorphicPairQuadraticRegular (g := g) hK hf (a := a) (by rw [ho]) a ha
  rw [← hreg.meromorphicTrailingCoeffAt_of_ne_zero (meromorphicPairQuadraticRegular_ne_zero hK hf ha ho),
    meromorphicTrailingCoeffAt_congr_nhdsNE (meromorphicPairQuadraticRegular_eventuallyEq hf ha),
    MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop)
      ((analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.mul (hf a ha)),
    MeromorphicAt.meromorphicTrailingCoeffAt_pow (by fun_prop), meromorphicTrailingCoeffAt_id_sub_const,
    (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.meromorphicTrailingCoeffAt_mul (hf a ha),
    (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicTrailingCoeffAt_of_ne_zero
      (meromorphicPairClearingWeight_ne_zero f g K a)]
  simp

/-- A strictly lower-order selected pole becomes zero at the same
quadratic scale, while keeping the full analytic representative. -/
theorem meromorphicPairQuadraticRegular_eq_zero {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K)
    (ho : (-2 : WithTop ℤ) < meromorphicOrderAt f a) :
    meromorphicPairQuadraticRegular f g K a a = 0 := by
  have hp : 0 < meromorphicOrderAt (meromorphicPairQuadraticRegular f g K a) a := by
    rw [order_regular_selected hK hf ha]
    by_cases ht : meromorphicOrderAt f a = ⊤
    · simp [ht]
    lift meromorphicOrderAt f a to ℤ using ht with n hn
    change ((-2 : ℤ) : WithTop ℤ) < (n : WithTop ℤ) at ho
    change ((0 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) + (n : WithTop ℤ)
    rw [WithTop.coe_lt_coe] at ho
    rw [← WithTop.coe_add, WithTop.coe_lt_coe]
    omega
  exact tendsto_nhds_unique
    ((analyticOnNhd_meromorphicPairQuadraticRegular (g := g) hK hf ho.le a ha).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) (tendsto_zero_of_meromorphicOrderAt_pos hp)

end

end RiemannGaussian
