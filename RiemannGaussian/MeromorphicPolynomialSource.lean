/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MeromorphicPairPoleClearing
import RiemannGaussian.AnalyticDoublePoleMoments
import Mathlib.Topology.Algebra.Polynomial

/-!+# Polynomial clearing and the exact surviving simple-pole source

The existing compact-domain clearing weight is a genuine finite polynomial.
Its selected value is nonzero. A linear regularization retains the exact
simple-pole coefficient, and Cauchy's estimate gives a geometric error for
every signed factorial moment after clearing. The complete complex identity
is retained before taking its norm or asymptotic limit.
-/

open Complex Filter Function MeromorphicOn Metric Set Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The actual finite polynomial of the common compact-domain pole divisor,
with its exact locations and integer multiplicities. -/
def meromorphicPairClearingPolynomial (f g : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (a : ℂ) : Polynomial ℂ :=
  ∏ z ∈ (hasFiniteSupport_meromorphicPairClearingExponent f g hK a).toFinset,
    (Polynomial.X - Polynomial.C z) ^ (meromorphicPairClearingExponent f g K a z).toNat

/-- Polynomial evaluation recovers the original entire clearing weight
pointwise, including at every pole and at the selected point. -/
theorem meromorphicPairClearingPolynomial_eval (f g : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (a s : ℂ) :
    (meromorphicPairClearingPolynomial f g hK a).eval s =
      meromorphicPairClearingWeight f g K a s := by
  have hd := hasFiniteSupport_meromorphicPairClearingExponent f g hK a
  rw [meromorphicPairClearingWeight, Function.FactorizedRational.finprod_eq_fun hd]
  dsimp only
  rw [finprod_eq_prod_of_mulSupport_subset (s := hd.toFinset)]
  · simp only [meromorphicPairClearingPolynomial, Polynomial.eval_prod,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_congr rfl
    intro z _
    have he : 0 ≤ meromorphicPairClearingExponent f g K a z := by
      simp only [meromorphicPairClearingExponent]
      split_ifs <;> simp
    rw [← zpow_natCast, Int.toNat_of_nonneg he]
  · intro z hz
    apply (hd.mem_toFinset).mpr
    change meromorphicPairClearingExponent f g K a z ≠ 0
    intro he
    exact hz (by simp [he])

/-- The literal clearing polynomial leaves a nonzero selected coefficient. -/
theorem meromorphicPairClearingPolynomial_eval_ne_zero (f g : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (a : ℂ) : (meromorphicPairClearingPolynomial f g hK a).eval a ≠ 0 := by
  rw [meromorphicPairClearingPolynomial_eval]
  exact meromorphicPairClearingWeight_ne_zero f g K a

/-- The common weight followed by the selected linear factor clears every
pole when the selected order is at least minus one. -/
theorem meromorphicOrderAt_pairLinearCleared_nonneg {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ}
    (ha : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f a) {s : ℂ} (hs : s ∈ K) :
    0 ≤ meromorphicOrderAt ((fun z : ℂ ↦ z - a) *
      (meromorphicPairClearingWeight f g K a * f)) s := by
  have hw := (analyticAt_meromorphicPairClearingWeight f g K a s).meromorphicAt
  rw [meromorphicOrderAt_mul (by fun_prop) (hw.mul (hf s hs))]
  by_cases hsa : s = a
  · subst s
    rw [meromorphicOrderAt_id_sub_const, meromorphicOrderAt_mul hw (hf a hs),
      meromorphicOrderAt_meromorphicPairClearingWeight f g hK,
      meromorphicPairClearingExponent, if_pos rfl, WithTop.coe_zero, zero_add]
    by_cases ht : meromorphicOrderAt f a = ⊤
    · simp [ht]
    lift meromorphicOrderAt f a to ℤ using ht with n hn
    change ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) at ha
    change ((0 : ℤ) : WithTop ℤ) ≤ ((1 : ℤ) : WithTop ℤ) + (n : WithTop ℤ)
    rw [WithTop.coe_le_coe] at ha
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    omega
  · exact add_nonneg (AnalyticAt.meromorphicOrderAt_nonneg (by fun_prop))
      (meromorphicOrderAt_pairCleared_nonneg hK hf hs hsa)

/-- The analytic representative after every nonselected pole and the
selected simple pole have been cleared, with removable values filled. -/
def meromorphicPairSimpleRegular (f g : ℂ → ℂ) (K : Set ℂ) (a : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn ((fun z : ℂ ↦ z - a) *
    (meromorphicPairClearingWeight f g K a * f)) K

/-- The filled linear regularization is analytic on the whole compact
domain, including the entire original divisor. -/
theorem analyticOnNhd_meromorphicPairSimpleRegular {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ}
    (ha : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    AnalyticOnNhd ℂ (meromorphicPairSimpleRegular f g K a) K := by
  have hm : MeromorphicOn ((fun z : ℂ ↦ z - a) *
      (meromorphicPairClearingWeight f g K a * f)) K := by
    intro s hs
    exact (AnalyticAt.meromorphicAt (by fun_prop)).mul
      ((analyticAt_meromorphicPairClearingWeight f g K a s).meromorphicAt.mul (hf s hs))
  intro s hs
  apply ((meromorphicNFOn_toMeromorphicNFOn _ K hs).meromorphicOrderAt_nonneg_iff_analyticAt).mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm hs]
  exact meromorphicOrderAt_pairLinearCleared_nonneg hK hf ha hs

/-- The filled response agrees with the full original weighted response
on every punctured germ of the domain. -/
theorem meromorphicPairSimpleRegular_eventuallyEq {f g : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) {a s : ℂ} (hs : s ∈ K) :
    meromorphicPairSimpleRegular f g K a =ᶠ[𝓝[≠] s]
      (fun z : ℂ ↦ z - a) * (meromorphicPairClearingWeight f g K a * f) := by
  apply MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE _ hs
  intro z hz
  exact (AnalyticAt.meromorphicAt (by fun_prop)).mul
    ((analyticAt_meromorphicPairClearingWeight f g K a z).meromorphicAt.mul (hf z hz))

/-- The selected simple pole becomes a nonzero analytic value. -/
theorem meromorphicPairSimpleRegular_ne_zero {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K)
    (ho : meromorphicOrderAt f a = -1) : meromorphicPairSimpleRegular f g K a a ≠ 0 := by
  apply (meromorphicNFOn_toMeromorphicNFOn _ K ha).meromorphicOrderAt_eq_zero_iff.mp
  change meromorphicOrderAt (meromorphicPairSimpleRegular f g K a) a = 0
  rw [meromorphicOrderAt_congr (meromorphicPairSimpleRegular_eventuallyEq hf ha),
    meromorphicOrderAt_mul (by fun_prop)
      ((analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.mul (hf a ha)),
    meromorphicOrderAt_id_sub_const,
    meromorphicOrderAt_mul (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt (hf a ha),
    meromorphicOrderAt_meromorphicPairClearingWeight f g hK, meromorphicPairClearingExponent,
    if_pos rfl, WithTop.coe_zero, zero_add, ho]
  change ((1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add]
  rfl

/-- The exact selected value keeps the original complex residue and the
nonzero clearing weight, before any norm is taken. -/
theorem meromorphicPairSimpleRegular_apply {f g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MeromorphicOn f K) {a : ℂ} (ha : a ∈ K)
    (ho : meromorphicOrderAt f a = -1) :
    meromorphicPairSimpleRegular f g K a a =
      meromorphicPairClearingWeight f g K a a * meromorphicTrailingCoeffAt f a := by
  have hreg := analyticOnNhd_meromorphicPairSimpleRegular (g := g) hK hf (a := a) (by rw [ho]) a ha
  rw [← hreg.meromorphicTrailingCoeffAt_of_ne_zero (meromorphicPairSimpleRegular_ne_zero hK hf ha ho),
    meromorphicTrailingCoeffAt_congr_nhdsNE (meromorphicPairSimpleRegular_eventuallyEq hf ha),
    MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop)
      ((analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.mul (hf a ha)),
    meromorphicTrailingCoeffAt_id_sub_const,
    (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicAt.meromorphicTrailingCoeffAt_mul (hf a ha),
    (analyticAt_meromorphicPairClearingWeight f g K a a).meromorphicTrailingCoeffAt_of_ne_zero
      (meromorphicPairClearingWeight_ne_zero f g K a)]
  simp

/-- The exact simple-pole moment splits into its residue and the full
analytic divided difference, with the original complex displacement. -/
theorem signedTaylorMoment_div_sub {f : ℂ → ℂ} {a s : ℂ}
    (ha : AnalyticAt ℂ f a) (hs : AnalyticAt ℂ f s) (hne : s ≠ a) (n : ℕ) :
    signedTaylorMoment n (fun z ↦ f z / (z - a)) s =
      f a * ((s - a)⁻¹) ^ (n + 1) + signedTaylorMoment n (dslope f a) s := by
  have he : (fun z ↦ f z / (z - a)) =ᶠ[𝓝 s]
      (fun z ↦ f a * (z - a)⁻¹ + dslope f a z) := by
    filter_upwards [eventually_ne_nhds hne] with z hz
    rw [dslope_of_ne _ hz, slope]
    simp only [smul_eq_mul, vsub_eq_sub]
    field_simp
    ring
  have hp : AnalyticAt ℂ (fun z ↦ f a * (z - a)⁻¹) s :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne))
  rw [signedTaylorMoment_congr n he,
    signedTaylorMoment_add n hp (analyticAt_dslope_of_analyticAt ha hs),
    signedTaylorMoment_const_mul, signedTaylorMoment_inv_sub]

/-- A quantitative geometric error retains the exact simple-pole source;
the radius is the actual closed analytic domain, not an assumed source bound. -/
theorem exists_simplePoleMoment_geometric_error {f : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall s R)) (ha : ‖s - a‖ < R) (hne : s ≠ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(s - a) ^ (n + 1) * signedTaylorMoment n (fun z ↦ f z / (z - a)) s - f a‖ ≤
        C * (‖s - a‖ / R) ^ n := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) ha
  have has : a ∈ closedBall s R := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using ha.le
  have hss : s ∈ closedBall s R := mem_closedBall_self hR.le
  have hd := analyticOnNhd_dslope_of_mem hf has
  obtain ⟨B, hB⟩ := ((isCompact_closedBall s R).image_of_continuousOn hd.continuousOn).isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨s, hss, rfl⟩)
  have hdc : DiffContOnCl ℂ (dslope f a) (ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    exact hd.differentiableOn
  have hb (n : ℕ) : ‖signedTaylorMoment n (dslope f a) s‖ ≤ B / R ^ n :=
    norm_signedTaylorMoment_le hR hdc (fun z hz ↦ hB _ ⟨z, sphere_subset_closedBall hz, rfl⟩) n
  refine ⟨B * ‖s - a‖ + 1, by positivity, fun n ↦ ?_⟩
  have hpow : (s - a) ^ (n + 1) * ((s - a)⁻¹) ^ (n + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_pow]
  have he : (s - a) ^ (n + 1) * signedTaylorMoment n (fun z ↦ f z / (z - a)) s - f a =
      (s - a) ^ (n + 1) * signedTaylorMoment n (dslope f a) s := by
    rw [signedTaylorMoment_div_sub (hf a has) (hf s hss) hne, mul_add,
      ← mul_assoc, mul_right_comm _ (f a), hpow]
    ring
  rw [he, norm_mul, norm_pow]
  calc
    _ ≤ ‖s - a‖ ^ (n + 1) * (B / R ^ n) :=
      mul_le_mul_of_nonneg_left (hb n) (by positivity)
    _ = (B * ‖s - a‖) * (‖s - a‖ / R) ^ n := by rw [div_pow, pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The actual divisor polynomial preserves the selected residue in all
signed factorial moments, with a quantitative geometric error. -/
theorem exists_meromorphicClearingPolynomial_source {f g : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall s R)) (hfs : AnalyticAt ℂ f s)
    (ha : ‖s - a‖ < R) (hne : s ≠ a) (ho : meromorphicOrderAt f a = -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(s - a) ^ (n + 1) * signedTaylorMoment n
        (fun z ↦ (meromorphicPairClearingPolynomial f g (isCompact_closedBall s R) a).eval z * f z) s -
        meromorphicPairClearingWeight f g (closedBall s R) a a * meromorphicTrailingCoeffAt f a‖ ≤
          C * (‖s - a‖ / R) ^ n := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) ha
  have hs : s ∈ closedBall s R := mem_closedBall_self hR.le
  have has : a ∈ closedBall s R := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using ha.le
  have hG := analyticOnNhd_meromorphicPairSimpleRegular (g := g) (isCompact_closedBall s R) hf (by rw [ho])
  have hw := analyticAt_meromorphicPairClearingWeight f g (closedBall s R) a s
  have hraw : AnalyticAt ℂ ((fun z : ℂ ↦ z - a) *
      (meromorphicPairClearingWeight f g (closedBall s R) a * f)) s :=
    (analyticAt_id.sub analyticAt_const).mul (hw.mul hfs)
  have he := ((hG s hs).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hraw.continuousAt).mp
    (meromorphicPairSimpleRegular_eventuallyEq (g := g) (a := a) hf hs)
  have hquot : (fun z ↦ (meromorphicPairClearingPolynomial f g (isCompact_closedBall s R) a).eval z * f z)
      =ᶠ[𝓝 s] (fun z ↦ meromorphicPairSimpleRegular f g (closedBall s R) a z / (z - a)) := by
    filter_upwards [he, eventually_ne_nhds hne] with z hz hza
    rw [meromorphicPairClearingPolynomial_eval, hz]
    simp only [Pi.mul_apply]
    field_simp
  obtain ⟨C, hC, hb⟩ := exists_simplePoleMoment_geometric_error hG ha hne
  refine ⟨C, hC, fun n ↦ ?_⟩
  rw [signedTaylorMoment_congr n hquot,
    ← meromorphicPairSimpleRegular_apply (isCompact_closedBall s R) hf has ho]
  exact hb n

end
end RiemannGaussian
