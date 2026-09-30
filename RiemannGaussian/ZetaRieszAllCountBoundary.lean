/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedCofactor
import RiemannGaussian.ZetaRieszContinuumCascade

/-!
# Joining every middle count before the physical response is estimated

Finite subset cancellation converts the exact Euler-odds weighted Riesz
sum into one Euler denominator times a signed truncated boundary. The
empty-cofactor term is retained explicitly. No infinite completion occurs.
-/

namespace RiemannGaussian.ZetaRieszAllCountBoundary
noncomputable section
open Complex Filter
open scoped BigOperators Classical
open ZetaRieszSelectedCofactor ZetaRieszSelectedPhysical

/-- The finite weighted cutoff difference, including its empty subset. -/
def difference {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (x : ι → ℝ)
    (F : ℝ → ℂ) (d : ℝ) : ℂ :=
  ∑ V ∈ Q.powerset, (-1 : ℂ)^V.card*(∏ p ∈ V, q p)*F (d-∑ p ∈ V, x p)

theorem difference_insert {ι : Type*} [DecidableEq ι] (Q : Finset ι)
    (q : ι → ℂ) (x : ι → ℝ) (F : ℝ → ℂ) (d : ℝ) {i : ι} (hi : i ∉ Q) :
    difference (insert i Q) q x F d =
      difference Q q x F d-q i*difference Q q x F (d-x i) := by
  unfold difference
  rw [Finset.sum_powerset_insert hi]
  rw [sub_eq_add_neg,← neg_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro V hV
  have hiV : i ∉ V := fun h => hi (Finset.mem_powerset.mp hV h)
  rw [Finset.card_insert_of_notMem hiV,Finset.prod_insert hiV,
    Finset.sum_insert hiV,pow_succ,
    show d-(x i+∑ p ∈ V, x p) = d-x i-∑ p ∈ V, x p by ring]
  ring

/-- Exact all-count cancellation for arbitrary finite shifts and any
complex physical test function. Each denominator is kept. -/
theorem sum_odds_difference {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (q : ι → ℂ) (x : ι → ℝ) (F : ℝ → ℂ)
    (hq : ∀ p ∈ Q, 1-q p ≠ 0) (d : ℝ) :
    (∑ U ∈ Q.powerset, (∏ p ∈ U, q p/(1-q p))*
      difference U (fun _ => 1) x F d) =
      (∏ p ∈ Q, (1-q p)⁻¹)*difference Q q x F d := by
  induction Q using Finset.induction_on generalizing d with
  | empty => simp [difference]
  | @insert i Q hi ih =>
    have hqQ : ∀ p ∈ Q, 1-q p ≠ 0 := fun p hp => hq p (Finset.mem_insert_of_mem hp)
    have hqi := hq i (Finset.mem_insert_self _ _)
    have he (U : Finset ι) (hU : U ∈ Q.powerset) :
        (∏ p ∈ insert i U, q p/(1-q p))*
          difference (insert i U) (fun _ => 1) x F d =
        (q i/(1-q i))*((∏ p ∈ U, q p/(1-q p))*difference U (fun _ => 1) x F d)-
        (q i/(1-q i))*((∏ p ∈ U, q p/(1-q p))*difference U (fun _ => 1) x F (d-x i)) := by
      have hiU : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
      rw [Finset.prod_insert hiU,difference_insert U _ _ _ _ hiU]
      ring
    rw [Finset.sum_powerset_insert hi,Finset.sum_congr rfl he,
      Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
      ih hqQ d,ih hqQ (d-x i),Finset.prod_insert hi,difference_insert Q _ _ _ _ hi]
    field_simp
    ring

theorem difference_sub_shift {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (x : ι → ℝ) (F : ℝ → ℂ) (a d : ℝ) :
    difference Q q x (fun v => F v-F (v-a)) d =
      difference Q q x F d-difference Q q x F (d-a) := by
  unfold difference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro V _hV
  dsimp only
  rw [show d-(∑ p ∈ V, x p)-a = d-a-∑ p ∈ V, x p by ring]
  ring

theorem difference_one_hinge {ι : Type*} (Q : Finset ι) (x : ι → ℝ) (d : ℝ) :
    difference Q (fun _ => 1) x (fun v => ((max 0 v : ℝ) : ℂ)) d =
      (ZetaRieszContinuumCascade.kernel Q x d : ℂ) := by
  simp [difference,ZetaRieszContinuumCascade.kernel]

/-- The exact prime hinge, including its saturated constant tail. -/
def primeHinge (r : ℕ) (d : ℝ) : ℂ :=
  ((max 0 d : ℝ) : ℂ)-((max 0 (d-Real.log r) : ℝ) : ℂ)

theorem difference_primeHinge (U : Finset ℕ) (r : ℕ) (hr : r ∉ U) (d : ℝ) :
    difference U (fun _ => 1) (fun p => Real.log p) (primeHinge r) d =
      (ZetaRieszContinuumCascade.kernel (insert r U) (fun p => Real.log p) d : ℂ) := by
  unfold primeHinge
  rw [difference_sub_shift,difference_one_hinge,difference_one_hinge,
    ZetaRieszContinuumCascade.kernel_insert U _ _ hr]
  push_cast
  rfl

/-- One finite Euler-boundary response. It contains every cofactor count,
and subtracts the exact empty-middle (ordinary-prime) response. -/
def eulerBoundary (r : ℕ) (Q : Finset ℕ) (s : ℂ) (d : ℝ) : ℂ :=
  (∏ p ∈ Q, (1-zetaPrimeFeature s p)⁻¹)*
    difference Q (zetaPrimeFeature s) (fun p => Real.log p) (primeHinge r) d-
      primeHinge r d

theorem all_count_riesz_eq (Q : Finset ℕ) (r : ℕ) (hr : r.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hrQ : r ∉ Q)
    (s : ℂ) (hs : ∀ p ∈ Q, 1-zetaPrimeFeature s p ≠ 0) (d : ℝ) :
    (∑ U ∈ Q.powerset.filter Finset.Nonempty,
      middleWeight U s*(VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ)) =
        eulerBoundary r Q s d := by
  have he (U : Finset ℕ) (hU : U ∈ Q.powerset) :
      difference U (fun _ => 1) (fun p => Real.log p) (primeHinge r) d =
        (VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ) := by
    have hrU : r ∉ U := fun h => hrQ (Finset.mem_powerset.mp hU h)
    rw [difference_primeHinge U r hrU,
      ZetaRieszContinuumCascade.kernel_eq_riesz_prime_product (insert r U)
        (fun p hp => by
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact hr
          · exact hQ p (Finset.mem_powerset.mp hU hp)),
      Finset.prod_insert hrU]
  have h := sum_odds_difference Q (zetaPrimeFeature s) (fun p => Real.log p)
    (primeHinge r) hs d
  have hsums : (∑ U ∈ Q.powerset, (∏ p ∈ U, zetaPrimeFeature s p/(1-zetaPrimeFeature s p))*
      difference U (fun _ => 1) (fun p => Real.log p) (primeHinge r) d) =
      primeHinge r d+∑ U ∈ Q.powerset.filter Finset.Nonempty,
        middleWeight U s*(VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ) := by
    rw [← Q.powerset.add_sum_erase _ (Finset.empty_mem_powerset Q)]
    simp only [Finset.prod_empty,difference,Finset.powerset_empty,
      Finset.sum_singleton,Finset.card_empty,pow_zero,one_mul,Finset.sum_empty,sub_zero]
    congr 1
    have hsets : Q.powerset.erase ∅ = Q.powerset.filter Finset.Nonempty := by
      ext U
      simp [Finset.nonempty_iff_ne_empty,and_comm]
    rw [hsets]
    apply Finset.sum_congr rfl
    intro U hU
    change _*difference U (fun _ => 1) (fun p => Real.log p) (primeHinge r) d = _
    rw [he U (Finset.mem_filter.mp hU).1]
    rfl
  rw [hsums] at h
  unfold eulerBoundary
  linear_combination h

/-- Joining counts commutes with the actual signed factorial moment.
The prime-hinge correction remains inside the differentiated function,
including at order zero. -/
theorem boundary_moment_eq (Q : Finset ℕ) (r : ℕ) (hr : r.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hrQ : r ∉ Q) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) (k : ℕ) (d : ℝ) :
    signedTaylorMoment k (fun z => eulerBoundary r Q z d) s =
      ∑ U ∈ Q.powerset.filter Finset.Nonempty,
        signedTaylorMoment k (middleWeight U) s*
          (VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ) := by
  have he : (fun z => eulerBoundary r Q z d) =ᶠ[nhds s]
      (fun z => ∑ U ∈ Q.powerset.filter Finset.Nonempty,
        (VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ)*middleWeight U z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hs]
      with z hz
    rw [← all_count_riesz_eq Q r hr hQ hrQ z (fun p hp => by
      have hb := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hz.le (h16 p hp)
      intro hd
      have hf : zetaPrimeFeature z p = 1 := by linear_combination -hd
      rw [hf,norm_one] at hb
      norm_num at hb) d]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have ha (U : Finset ℕ) (hU : U ∈ Q.powerset.filter Finset.Nonempty) :
      AnalyticAt ℂ (fun z =>
        (VaughanLogAverage.riesz d (r*∏ p ∈ U, p) : ℂ)*middleWeight U z) s :=
    analyticAt_const.mul (middleWeight_analytic U
      (fun p hp => h16 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp)) hs.le)
  rw [signedTaylorMoment_congr k he,signedTaylorMoment_sum _ k _ ha]
  simp only [signedTaylorMoment_const_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The literal physical cofactor has ONE all-count Euler-boundary
response for each least prime. No subset/count is normed separately. -/
theorem physicalCofactor_eq_eulerBoundary (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    {s : ℂ} (hs : 1/2 < s.re) (N j h : ℕ) (d : ℝ) :
    physicalCofactor A N j h s d =
      ∑ r ∈ A, zetaPrimeLogKernel h s r*
        signedTaylorMoment (N+1-j-h)
          (fun z => eulerBoundary r (ZetaRieszMarkedSeparation.tailPrimes A r) z d) s := by
  unfold physicalCofactor ZetaRieszUnshiftedCharacter.indices
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [boundary_moment_eq (ZetaRieszMarkedSeparation.tailPrimes A r) r (hA r hr)
    (fun p hp => hA p (Finset.mem_filter.mp hp).1)
    (by simp [ZetaRieszMarkedSeparation.tailPrimes])
    (fun p hp => h16 p (Finset.mem_filter.mp hp).1) hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hrU : r ∉ U := by
    intro hh
    have hp := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hh
    exact (Finset.mem_filter.mp hp).2.false
  simp only [indexWeight,ZetaRieszUnshiftedCharacter.label]
  rw [Finset.prod_insert hrU]
  ring

end
end RiemannGaussian.ZetaRieszAllCountBoundary
